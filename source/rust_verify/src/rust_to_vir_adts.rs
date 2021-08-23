use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics, def_id_to_vir_path, get_mode, hack_get_def_name, ty_to_vir,
};
use crate::unsupported_unless;
use crate::util::spanned_new;
use rustc_hir::{EnumDef, Generics, ItemId, VariantData};
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{DatatypeX, Ident, KrateX, Mode, Variant, VirErr};
use vir::ast_util::{ident_binder, str_ident};
use vir::def::{variant_field_ident, variant_ident, variant_positional_field_ident};

fn check_variant_data<'tcx>(
    ctxt: &Context<'tcx>,
    name: &Ident,
    variant_data: &'tcx VariantData<'tcx>,
) -> Variant {
    // TODO handle field visibility; does rustc_middle::ty::Visibility have better visibility
    // information than hir?
    ident_binder(
        name,
        &(match variant_data {
            VariantData::Struct(fields, recovered) => {
                unsupported_unless!(!recovered, "recovered_struct", variant_data);
                Arc::new(
                    fields
                        .iter()
                        .map(|field| {
                            ident_binder(
                                &variant_field_ident(name, &field.ident.as_str()),
                                &(
                                    ty_to_vir(ctxt.tcx, field.ty),
                                    get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                                ),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            }
            VariantData::Tuple(fields, _variant_id) => Arc::new(
                fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        ident_binder(
                            &variant_positional_field_ident(name, i),
                            &(
                                ty_to_vir(ctxt.tcx, field.ty),
                                get_mode(Mode::Exec, ctxt.tcx.hir().attrs(field.hir_id)),
                            ),
                        )
                    })
                    .collect::<Vec<_>>(),
            ),
            VariantData::Unit(_vairant_id) => Arc::new(vec![]),
        }),
    )
}

pub fn check_item_struct<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    span: Span,
    id: &ItemId,
    variant_data: &'tcx VariantData<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<(), VirErr> {
    check_generics(generics)?;
    let name = hack_get_def_name(ctxt.tcx, id.def_id.to_def_id());
    let path = def_id_to_vir_path(ctxt.tcx, id.def_id.to_def_id());
    let variant_name = variant_ident(&name, &name);
    let variants = Arc::new(vec![check_variant_data(ctxt, &variant_name, variant_data)]);
    vir.datatypes.push(spanned_new(span, DatatypeX { path, variants }));
    Ok(())
}

pub fn check_item_enum<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    span: Span,
    id: &ItemId,
    enum_def: &'tcx EnumDef<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<(), VirErr> {
    check_generics(generics)?;
    let name = Arc::new(hack_get_def_name(ctxt.tcx, id.def_id.to_def_id()));
    let path = def_id_to_vir_path(ctxt.tcx, id.def_id.to_def_id());
    let variants = Arc::new(
        enum_def
            .variants
            .iter()
            .map(|variant| {
                let rust_variant_name = variant.ident.as_str();
                let variant_name = str_ident(
                    format!("{}{}{}", name, vir::def::VARIANT_SEPARATOR, rust_variant_name)
                        .as_str(),
                );
                check_variant_data(ctxt, &variant_name, &variant.data)
            })
            .collect::<Vec<_>>(),
    );
    vir.datatypes.push(spanned_new(span, DatatypeX { path, variants }));
    Ok(())
}
