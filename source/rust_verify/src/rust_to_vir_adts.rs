use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics, def_id_to_vir_path, get_mode, get_verifier_attrs, hack_get_def_name,
    is_visibility_private, ty_to_vir,
};
use crate::unsupported_unless;
use crate::util::spanned_new;
use rustc_ast::Attribute;
use rustc_hir::{EnumDef, Generics, ItemId, VariantData};
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{DatatypeTransparency, DatatypeX, Ident, KrateX, Mode, Variant, VirErr};
use vir::ast_util::{ident_binder, str_ident};
use vir::def::{variant_field_ident, variant_ident, variant_positional_field_ident};

fn check_variant_data<'tcx>(
    ctxt: &Context<'tcx>,
    name: &Ident,
    variant_data: &'tcx VariantData<'tcx>,
) -> (Variant, bool) {
    // TODO handle field visibility; does rustc_middle::ty::Visibility have better visibility
    // information than hir?
    let (vir_fields, one_field_private) = match variant_data {
        VariantData::Struct(fields, recovered) => {
            unsupported_unless!(!recovered, "recovered_struct", variant_data);
            let (vir_fields, field_private): (Vec<_>, Vec<_>) = fields
                .iter()
                .map(|field| {
                    (
                        ident_binder(
                            &variant_field_ident(name, &field.ident.as_str()),
                            &(
                                ty_to_vir(ctxt.tcx, field.ty),
                                get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                            ),
                        ),
                        is_visibility_private(&field.vis.node),
                    )
                })
                .unzip();
            (Arc::new(vir_fields), field_private.into_iter().any(|x| x))
        }
        VariantData::Tuple(fields, _variant_id) => {
            let (vir_fields, field_private): (Vec<_>, Vec<_>) = fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    (
                        ident_binder(
                            &variant_positional_field_ident(name, i),
                            &(
                                ty_to_vir(ctxt.tcx, field.ty),
                                get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                            ),
                        ),
                        is_visibility_private(&field.vis.node),
                    )
                })
                .unzip();
            (Arc::new(vir_fields), field_private.into_iter().any(|x| x))
        }
        VariantData::Unit(_vairant_id) => (Arc::new(vec![]), false),
    };
    (ident_binder(name, &vir_fields), one_field_private)
}

pub fn check_item_struct<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    span: Span,
    id: &ItemId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    variant_data: &'tcx VariantData<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<(), VirErr> {
    check_generics(generics)?;
    let name = hack_get_def_name(ctxt.tcx, id.def_id.to_def_id());
    let path = def_id_to_vir_path(ctxt.tcx, id.def_id.to_def_id());
    let variant_name = variant_ident(&name, &name);
    let (variant, one_field_private) = check_variant_data(ctxt, &variant_name, variant_data);
    let vattrs = get_verifier_attrs(attrs)?;
    let transparency = if !vattrs.do_verify {
        DatatypeTransparency::Never
    } else if one_field_private {
        DatatypeTransparency::WithinModule
    } else {
        DatatypeTransparency::Always
    };
    let variants = Arc::new(vec![variant]);
    vir.datatypes.push(spanned_new(span, DatatypeX { path, visibility, transparency, variants }));
    Ok(())
}

pub fn check_item_enum<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    span: Span,
    id: &ItemId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    enum_def: &'tcx EnumDef<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<(), VirErr> {
    check_generics(generics)?;
    let name = Arc::new(hack_get_def_name(ctxt.tcx, id.def_id.to_def_id()));
    let path = def_id_to_vir_path(ctxt.tcx, id.def_id.to_def_id());
    let (variants, one_field_private): (Vec<_>, Vec<_>) = enum_def
        .variants
        .iter()
        .map(|variant| {
            let rust_variant_name = variant.ident.as_str();
            let variant_name = str_ident(
                format!("{}{}{}", name, vir::def::VARIANT_SEPARATOR, rust_variant_name).as_str(),
            );
            check_variant_data(ctxt, &variant_name, &variant.data)
        })
        .unzip();
    let one_field_private = one_field_private.into_iter().any(|x| x);
    let vattrs = get_verifier_attrs(attrs)?;
    let transparency = if !vattrs.do_verify {
        DatatypeTransparency::Never
    } else if one_field_private {
        DatatypeTransparency::WithinModule
    } else {
        DatatypeTransparency::Always
    };
    vir.datatypes.push(spanned_new(
        span,
        DatatypeX { path, visibility, transparency, variants: Arc::new(variants) },
    ));
    Ok(())
}
