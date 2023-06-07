use crate::attributes::{get_mode, get_verifier_attrs};
use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics_bounds, def_id_to_vir_path, hack_get_def_name, is_visibility_private,
    mid_ty_to_vir, mk_visibility,
};
use crate::unsupported_err_unless;
use crate::util::err_span;
use crate::util::unsupported_err_span;
use air::ast_util::str_ident;
use rustc_ast::Attribute;
use rustc_hir::{EnumDef, Generics, ItemId, VariantData};
use rustc_span::Span;
use rustc_span::Symbol;
use std::sync::Arc;
use vir::ast::{DatatypeTransparency, DatatypeX, Ident, KrateX, Mode, Path, Variant, VirErr};
use vir::ast_util::ident_binder;
use vir::def::positional_field_ident;

fn check_variant_data<'tcx, 'fd>(
    span: Span,
    ctxt: &Context<'tcx>,
    module_path: &Path,
    name: &Ident,
    variant_data: &'tcx VariantData<'tcx>,
    field_defs: impl Iterator<Item = &'fd rustc_middle::ty::FieldDef>,
) -> Result<(Variant, bool), VirErr>
where
    'tcx: 'fd,
{
    // TODO handle field visibility; does rustc_middle::ty::Visibility have better visibility
    // information than hir?
    let (vir_fields, one_field_private) = match variant_data {
        VariantData::Struct(fields, recovered) => {
            unsupported_err_unless!(!recovered, span, "recovered_struct", variant_data);
            let (vir_fields, field_private): (Vec<_>, Vec<_>) = fields
                .iter()
                .zip(field_defs)
                .map(|(field, field_def)| {
                    assert!(field.ident.name == field_def.ident(ctxt.tcx).name);
                    let field_ty = ctxt.tcx.type_of(field_def.did);

                    Ok((
                        ident_binder(
                            &str_ident(&field.ident.as_str()),
                            &(
                                mid_ty_to_vir(ctxt.tcx, span, &field_ty, false)?,
                                get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                                mk_visibility(
                                    ctxt,
                                    &Some(module_path.clone()),
                                    field.def_id.to_def_id(),
                                ),
                            ),
                        ),
                        is_visibility_private(
                            ctxt,
                            span,
                            &Some(module_path.clone()),
                            field.def_id.to_def_id(),
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, VirErr>>()?
                .into_iter()
                .unzip();
            (Arc::new(vir_fields), field_private.into_iter().any(|x| x))
        }
        VariantData::Tuple(fields, _variant_id, _local_def_id) => {
            let (vir_fields, field_private): (Vec<_>, Vec<_>) = fields
                .iter()
                .zip(field_defs)
                .enumerate()
                .map(|(i, (field, field_def))| {
                    assert!(field.ident.name == field_def.ident(ctxt.tcx).name);
                    let field_ty = ctxt.tcx.type_of(field_def.did);

                    Ok((
                        ident_binder(
                            &positional_field_ident(i),
                            &(
                                mid_ty_to_vir(ctxt.tcx, span, &field_ty, false)?,
                                get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                                mk_visibility(
                                    ctxt,
                                    &Some(module_path.clone()),
                                    field.def_id.to_def_id(),
                                ),
                            ),
                        ),
                        is_visibility_private(
                            ctxt,
                            span,
                            &Some(module_path.clone()),
                            field.def_id.to_def_id(),
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, VirErr>>()?
                .into_iter()
                .unzip();
            (Arc::new(vir_fields), field_private.into_iter().any(|x| x))
        }
        VariantData::Unit(_variant_id, _local_def_id) => (Arc::new(vec![]), false),
    };
    Ok((ident_binder(name, &vir_fields), one_field_private))
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
    adt_def: &'_ rustc_middle::ty::AdtDef,
) -> Result<(), VirErr> {
    assert!(adt_def.is_struct());

    let is_strslice_struct = ctxt
        .tcx
        .is_diagnostic_item(Symbol::intern("pervasive::string::StrSlice"), id.owner_id.to_def_id());

    if is_strslice_struct {
        return Ok(());
    }

    let vattrs = get_verifier_attrs(attrs)?;

    if vattrs.external_fn_specification {
        return err_span(span, "`external_fn_specification` attribute not supported here");
    }

    let def_id = id.owner_id.to_def_id();
    let typ_params = Arc::new(check_generics_bounds(
        ctxt.tcx,
        generics,
        vattrs.external_body,
        def_id,
        Some(&vattrs),
    )?);
    let name = hack_get_def_name(ctxt.tcx, def_id);
    let path = def_id_to_vir_path(ctxt.tcx, def_id);

    let variant_name = Arc::new(name.clone());
    let (variant, one_field_private) = if vattrs.external_body {
        (ident_binder(&variant_name, &Arc::new(vec![])), false)
    } else {
        let field_defs = adt_def.all_fields();
        check_variant_data(span, ctxt, module_path, &variant_name, variant_data, field_defs)?
    };
    let transparency = if vattrs.external_body {
        DatatypeTransparency::Never
    } else if one_field_private {
        DatatypeTransparency::WithinModule
    } else {
        DatatypeTransparency::Always
    };
    let datatype = DatatypeX {
        path,
        visibility,
        transparency,
        typ_params,
        variants: Arc::new(vec![variant]),
        mode: get_mode(Mode::Exec, attrs),
        ext_equal: vattrs.ext_equal,
    };
    vir.datatypes.push(ctxt.spanned_new(span, datatype));
    Ok(())
}

pub fn get_mid_variant_def_by_name<'tcx, 'df>(
    ctxt: &Context<'tcx>,
    adt_def: &'df rustc_middle::ty::AdtDef,
    variant_name: &str,
) -> &'df rustc_middle::ty::VariantDef
where
    'tcx: 'df,
{
    for variant_def in adt_def.variants().iter() {
        if variant_def.ident(ctxt.tcx).name.as_str() == variant_name {
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
    adt_def: &rustc_middle::ty::AdtDef,
) -> Result<(), VirErr> {
    assert!(adt_def.is_enum());

    let vattrs = get_verifier_attrs(attrs)?;

    if vattrs.external_fn_specification {
        return err_span(span, "`external_fn_specification` attribute not supported here");
    }

    let def_id = id.owner_id.to_def_id();
    let typ_params = Arc::new(check_generics_bounds(
        ctxt.tcx,
        generics,
        vattrs.external_body,
        def_id,
        Some(&vattrs),
    )?);
    let path = def_id_to_vir_path(ctxt.tcx, def_id);
    let (variants, one_field_private): (Vec<_>, Vec<_>) = enum_def
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident.as_str();
            let variant_def = get_mid_variant_def_by_name(ctxt, &adt_def, variant_name);
            let variant_name = str_ident(variant_name);
            let field_defs = variant_def.fields.iter();
            check_variant_data(
                variant.span,
                ctxt,
                module_path,
                &variant_name,
                &variant.data,
                field_defs,
            )
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .unzip();
    let one_field_private = one_field_private.into_iter().any(|x| x);
    let transparency = if vattrs.external_body {
        DatatypeTransparency::Never
    } else if one_field_private {
        DatatypeTransparency::WithinModule
    } else {
        DatatypeTransparency::Always
    };
    vir.datatypes.push(ctxt.spanned_new(
        span,
        DatatypeX {
            path,
            visibility,
            transparency,
            typ_params,
            variants: Arc::new(variants),
            mode: get_mode(Mode::Exec, attrs),
            ext_equal: vattrs.ext_equal,
        },
    ));
    Ok(())
}
