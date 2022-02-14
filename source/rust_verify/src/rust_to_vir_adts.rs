use crate::attributes::{get_mode, get_verifier_attrs};
use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics, def_id_to_vir_path, hack_get_def_name, is_visibility_private, mk_visibility,
    ty_to_vir,
};
use crate::unsupported_unless;
use crate::util::spanned_new;
use air::ast_util::str_ident;
use rustc_ast::Attribute;
use rustc_hir::{EnumDef, Generics, ItemId, VariantData};
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{DatatypeTransparency, DatatypeX, Ident, KrateX, Mode, Path, Variant, VirErr};
use vir::ast_util::ident_binder;
use vir::def::positional_field_ident;

fn check_variant_data<'tcx>(
    ctxt: &Context<'tcx>,
    module_path: &Path,
    name: &Ident,
    variant_data: &'tcx VariantData<'tcx>,
    in_enum: bool,
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
                            &str_ident(&field.ident.as_str()),
                            &(
                                ty_to_vir(ctxt.tcx, field.ty),
                                get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                                mk_visibility(&Some(module_path.clone()), &field.vis, !in_enum),
                            ),
                        ),
                        is_visibility_private(&field.vis.node, !in_enum),
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
                            &positional_field_ident(i),
                            &(
                                ty_to_vir(ctxt.tcx, field.ty),
                                get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                                mk_visibility(&Some(module_path.clone()), &field.vis, !in_enum),
                            ),
                        ),
                        is_visibility_private(&field.vis.node, !in_enum),
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
    module_path: &Path,
    span: Span,
    id: &ItemId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    variant_data: &'tcx VariantData<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<(), VirErr> {
    let vattrs = get_verifier_attrs(attrs)?;
    let typ_params = Arc::new(check_generics(ctxt.tcx, generics, false, vattrs.external_body)?);
    let name = hack_get_def_name(ctxt.tcx, id.def_id.to_def_id());
    let path = def_id_to_vir_path(ctxt.tcx, id.def_id.to_def_id());
    let variant_name = Arc::new(name.clone());
    let (variant, one_field_private) = if vattrs.external_body {
        (ident_binder(&variant_name, &Arc::new(vec![])), false)
    } else {
        check_variant_data(ctxt, module_path, &variant_name, variant_data, false)
    };
    let transparency = if vattrs.external_body {
        DatatypeTransparency::Never
    } else if one_field_private {
        DatatypeTransparency::WithinModule
    } else {
        DatatypeTransparency::Always
    };
    let variants = Arc::new(vec![variant]);
    let mode = get_mode(Mode::Exec, attrs);
    let unforgeable = vattrs.unforgeable;
    let datatype =
        DatatypeX { path, visibility, transparency, typ_params, variants, mode, unforgeable };
    vir.datatypes.push(spanned_new(span, datatype));
    Ok(())
}

pub fn check_item_enum<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    span: Span,
    id: &ItemId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    enum_def: &'tcx EnumDef<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<(), VirErr> {
    let vattrs = get_verifier_attrs(attrs)?;
    let typ_params = Arc::new(check_generics(ctxt.tcx, generics, false, vattrs.external_body)?);
    let path = def_id_to_vir_path(ctxt.tcx, id.def_id.to_def_id());
    let (variants, one_field_private): (Vec<_>, Vec<_>) = enum_def
        .variants
        .iter()
        .map(|variant| {
            let variant_name = str_ident(&variant.ident.as_str());
            check_variant_data(ctxt, module_path, &variant_name, &variant.data, true)
        })
        .unzip();
    let one_field_private = one_field_private.into_iter().any(|x| x);
    let transparency = if vattrs.external_body {
        DatatypeTransparency::Never
    } else if one_field_private {
        DatatypeTransparency::WithinModule
    } else {
        DatatypeTransparency::Always
    };
    let mode = get_mode(Mode::Exec, attrs);
    let unforgeable = vattrs.unforgeable;
    vir.datatypes.push(spanned_new(
        span,
        DatatypeX {
            path,
            visibility,
            transparency,
            typ_params,
            variants: Arc::new(variants),
            mode,
            unforgeable,
        },
    ));
    Ok(())
}
