use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics_bounds_with_polarity, def_id_to_vir_path, process_predicate_bounds,
};
use crate::rust_to_vir_func::{check_item_fn, CheckItemFnEither};
use crate::unsupported_err_unless;
use crate::util::err_span;
use rustc_hir::{Generics, TraitFn, TraitItem, TraitItemKind, TraitItemRef};
use rustc_span::def_id::DefId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    Fun, Function, FunctionKind, GenericBound, GenericBoundX, Ident, KrateX, TraitX, TypX, VirErr,
    Visibility,
};
use vir::def::trait_self_type_param;

pub(crate) fn translate_trait<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    trait_span: Span,
    trait_def_id: DefId,
    visibility: Visibility,
    module_path: &vir::ast::Path,
    trait_generics: &'tcx Generics,
    trait_items: &'tcx [TraitItemRef],
    external_fn_specification_trait_method_impls: &mut Vec<(DefId, rustc_span::Span)>,
) -> Result<(), VirErr> {
    let trait_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, trait_def_id);
    let (generics_params, typ_bounds) = {
        let (generics_params, mut typ_bounds) = check_generics_bounds_with_polarity(
            ctxt.tcx,
            &ctxt.verus_items,
            trait_generics.span,
            Some(trait_generics),
            false,
            trait_def_id,
            None,
            Some(&mut *ctxt.diagnostics.borrow_mut()),
        )?;
        // Remove the Self: Trait bound introduced by rustc
        Arc::make_mut(&mut typ_bounds).retain(|gb| {
            match &**gb {
                GenericBoundX::Trait(bnd, tp) => {
                    if bnd == &trait_path {
                        let gp: Vec<_> = Some(trait_self_type_param())
                            .into_iter()
                            .chain(generics_params.iter().map(|(p, _)| p.clone()))
                            .map(|p| Some(p))
                            .collect();
                        let tp: Vec<_> = tp
                            .iter()
                            .map(|p| match &**p {
                                TypX::TypParam(p) => Some(p.clone()),
                                _ => None,
                            })
                            .collect();
                        assert_eq!(*tp, *gp);
                        return false;
                    }
                }
                GenericBoundX::TypEquality(..) => {}
                GenericBoundX::ConstTyp(..) => {}
            }
            true
        });
        (generics_params, typ_bounds)
    };
    let mut assoc_typs: Vec<Ident> = Vec::new();
    let mut assoc_typs_bounds: Vec<GenericBound> = Vec::new();
    let mut methods: Vec<Function> = Vec::new();
    let mut method_names: Vec<Fun> = Vec::new();
    for trait_item_ref in trait_items {
        let trait_item = ctxt.tcx.hir().trait_item(trait_item_ref.id);
        let TraitItem { ident, owner_id, generics: item_generics, kind, span, defaultness: _ } =
            trait_item;
        let (item_generics_params, item_typ_bounds) = check_generics_bounds_with_polarity(
            ctxt.tcx,
            &ctxt.verus_items,
            item_generics.span,
            Some(item_generics),
            false,
            owner_id.to_def_id(),
            None,
            Some(&mut *ctxt.diagnostics.borrow_mut()),
        )?;

        let attrs = ctxt.tcx.hir().attrs(trait_item.hir_id());
        let vattrs = ctxt.get_verifier_attrs(attrs)?;
        if vattrs.external {
            return err_span(
                *span,
                "a trait item cannot be marked 'external' - perhaps you meant to mark the entire trait external?",
            );
        }

        match kind {
            TraitItemKind::Fn(sig, fun) => {
                let body_id = match fun {
                    TraitFn::Provided(body_id) => CheckItemFnEither::BodyId(body_id),
                    TraitFn::Required(param_names) => CheckItemFnEither::ParamNames(*param_names),
                };
                let attrs = ctxt.tcx.hir().attrs(trait_item.hir_id());
                let fun = check_item_fn(
                    ctxt,
                    &mut methods,
                    None,
                    owner_id.to_def_id(),
                    FunctionKind::TraitMethodDecl { trait_path: trait_path.clone() },
                    visibility.clone(),
                    module_path,
                    attrs,
                    sig,
                    Some((trait_generics, trait_def_id)),
                    item_generics,
                    body_id,
                    external_fn_specification_trait_method_impls,
                )?;
                if let Some(fun) = fun {
                    method_names.push(fun);
                }
            }
            TraitItemKind::Type([], None) => {
                unsupported_err_unless!(item_generics_params.len() == 0, *span, "trait generics");
                unsupported_err_unless!(item_typ_bounds.len() == 0, *span, "trait generics");
                assoc_typs.push(Arc::new(ident.to_string()));
            }
            TraitItemKind::Type(_, Some(_)) => {
                return err_span(
                    trait_span,
                    "Verus does not yet support associated types with a concrete type",
                );
            }
            TraitItemKind::Type(_generic_bounds, None) => {
                unsupported_err_unless!(item_generics_params.len() == 0, *span, "trait generics");
                unsupported_err_unless!(item_typ_bounds.len() == 0, *span, "trait generics");
                assoc_typs.push(Arc::new(ident.to_string()));

                let bounds =
                    ctxt.tcx.item_bounds(trait_item.owner_id.def_id.to_def_id()).skip_binder();
                let bounds = bounds.iter().map(|p| (p, *span)).collect::<Vec<_>>();
                let vir_bounds = process_predicate_bounds(
                    ctxt.tcx,
                    trait_def_id,
                    &ctxt.verus_items,
                    bounds.iter(),
                    ctxt.tcx.generics_of(trait_def_id),
                )?;
                assoc_typs_bounds.extend(vir_bounds);
            }
            TraitItemKind::Const(_, _) => {
                return err_span(trait_span, "Verus does not yet support associated constants");
            }
        }
    }
    let mut methods = vir::headers::make_trait_decls(methods)?;
    vir.functions.append(&mut methods);
    let traitx = TraitX {
        name: trait_path,
        visibility,
        methods: Arc::new(method_names),
        assoc_typs: Arc::new(assoc_typs),
        typ_params: generics_params,
        typ_bounds,
        assoc_typs_bounds: Arc::new(assoc_typs_bounds),
    };
    vir.traits.push(ctxt.spanned_new(trait_span, traitx));
    Ok(())
}
