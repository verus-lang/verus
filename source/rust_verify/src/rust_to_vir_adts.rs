use crate::attributes::{get_mode, get_verifier_attrs};
use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics_bounds, def_id_to_vir_path, hack_get_def_name, is_visibility_private,
    mid_ty_to_vir, mk_visibility,
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
    field_defs: impl Iterator<Item = &'tcx rustc_middle::ty::FieldDef>,
) -> (Variant, bool) {
    // TODO handle field visibility; does rustc_middle::ty::Visibility have better visibility
    // information than hir?
    let (vir_fields, one_field_private) = match variant_data {
        VariantData::Struct(fields, recovered) => {
            unsupported_unless!(!recovered, "recovered_struct", variant_data);
            let (vir_fields, field_private): (Vec<_>, Vec<_>) = fields
                .iter()
                .zip(field_defs)
                .map(|(field, field_def)| {
                    assert!(field.ident.name == field_def.ident.name);
                    let field_ty = ctxt.tcx.type_of(field_def.did);

                    (
                        ident_binder(
                            &str_ident(&field.ident.as_str()),
                            &(
                                mid_ty_to_vir(ctxt.tcx, field_ty, false),
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
                .zip(field_defs)
                .enumerate()
                .map(|(i, (field, field_def))| {
                    assert!(field.ident.name == field_def.ident.name);
                    let field_ty = ctxt.tcx.type_of(field_def.did);

                    (
                        ident_binder(
                            &positional_field_ident(i),
                            &(
                                mid_ty_to_vir(ctxt.tcx, field_ty, false),
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
    adt_def: &'tcx rustc_middle::ty::AdtDef,
) -> Result<(), VirErr> {
    assert!(adt_def.is_struct());

    let vattrs = get_verifier_attrs(attrs)?;
    let def_id = id.def_id.to_def_id();
    let typ_params =
        Arc::new(check_generics_bounds(ctxt.tcx, generics, vattrs.external_body, def_id)?);
    let name = hack_get_def_name(ctxt.tcx, def_id);
    let path = def_id_to_vir_path(ctxt.tcx, def_id);
    let variant_name = Arc::new(name.clone());
    let (variant, one_field_private) = if vattrs.external_body {
        (ident_binder(&variant_name, &Arc::new(vec![])), false)
    } else {
        let field_defs = adt_def.all_fields();
        check_variant_data(ctxt, module_path, &variant_name, variant_data, false, field_defs)
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

pub fn get_mid_variant_def_by_name<'a>(
    adt_def: &'a rustc_middle::ty::AdtDef,
    variant_name: &str,
) -> &'a rustc_middle::ty::VariantDef {
    for variant_def in adt_def.variants.iter() {
        if variant_def.ident.name.as_str() == variant_name {
            return variant_def;
        }
    }
    panic!("get_mid_variant_def_by_name failed to find variant");
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
    adt_def: &'tcx rustc_middle::ty::AdtDef,
) -> Result<(), VirErr> {
    assert!(adt_def.is_enum());

    let vattrs = get_verifier_attrs(attrs)?;
    let def_id = id.def_id.to_def_id();
    let typ_params =
        Arc::new(check_generics_bounds(ctxt.tcx, generics, vattrs.external_body, def_id)?);
    let path = def_id_to_vir_path(ctxt.tcx, def_id);
    let (variants, one_field_private): (Vec<_>, Vec<_>) = enum_def
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident.as_str();
            let variant_def = get_mid_variant_def_by_name(&adt_def, variant_name);
            let variant_name = str_ident(variant_name);
            let field_defs = variant_def.fields.iter();
            check_variant_data(ctxt, module_path, &variant_name, &variant.data, true, field_defs)
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
