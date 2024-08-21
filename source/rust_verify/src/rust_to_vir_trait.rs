use crate::attributes::VerifierAttrs;
use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics_bounds_with_polarity, def_id_to_vir_path, process_predicate_bounds,
};
use crate::rust_to_vir_func::{check_item_fn, CheckItemFnEither};
use crate::rust_to_vir_impl::ExternalInfo;
use crate::unsupported_err_unless;
use crate::util::{err_span, err_span_bare};
use rustc_hir::{Generics, TraitFn, TraitItem, TraitItemKind, TraitItemRef};
use rustc_middle::ty::{ClauseKind, ImplPolarity, TraitPredicate, TraitRef, TyCtxt};
use rustc_span::def_id::DefId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    Fun, Function, FunctionKind, GenericBound, GenericBoundX, Ident, KrateX, TraitX, TypX, VirErr,
    Visibility,
};
use vir::def::{trait_self_type_param, VERUS_SPEC};

pub(crate) fn external_trait_specification_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_items: &'tcx [TraitItemRef],
    trait_vattrs: &VerifierAttrs,
) -> Result<Option<TraitRef<'tcx>>, VirErr> {
    let mut ex_trait_ref_for: Option<TraitRef> = None;
    for trait_item_ref in trait_items {
        let trait_item = tcx.hir().trait_item(trait_item_ref.id);
        let TraitItem { ident, kind, span, .. } = trait_item;
        match kind {
            TraitItemKind::Type(_generic_bounds, None) => {
                if Some(ident.to_string()) == trait_vattrs.external_trait_specification {
                    let bounds = tcx
                        .explicit_item_bounds(trait_item.owner_id.def_id.to_def_id())
                        .skip_binder();
                    for (bound, _) in bounds {
                        match bound.kind().skip_binder() {
                            ClauseKind::Trait(TraitPredicate {
                                trait_ref,
                                polarity: ImplPolarity::Positive,
                            }) => {
                                let trait_def_id = trait_ref.def_id;
                                if Some(trait_def_id) == tcx.lang_items().sized_trait() {
                                    continue;
                                }
                                if ex_trait_ref_for.is_some() {
                                    return err_span(
                                        *span,
                                        format!("only one bound allowed in {ident}"),
                                    );
                                }
                                ex_trait_ref_for = Some(trait_ref);
                            }
                            _ => {
                                return err_span(*span, format!("unexpected bound in {ident}"));
                            }
                        }
                    }
                    if ex_trait_ref_for.is_none() {
                        return err_span(*span, format!("{ident} must have a bound"));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(ex_trait_ref_for)
}

pub(crate) fn translate_trait<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    trait_span: Span,
    trait_def_id: DefId,
    visibility: Visibility,
    module_path: &vir::ast::Path,
    trait_generics: &'tcx Generics,
    trait_items: &'tcx [TraitItemRef],
    trait_vattrs: &VerifierAttrs,
    external_info: &mut ExternalInfo,
) -> Result<(), VirErr> {
    let tcx = ctxt.tcx;
    let orig_trait_path = def_id_to_vir_path(tcx, &ctxt.verus_items, trait_def_id);
    let mut trait_path = orig_trait_path.clone();
    let (generics_params, mut typ_bounds) = {
        let (generics_params, mut typ_bounds) = check_generics_bounds_with_polarity(
            tcx,
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
    let ex_trait_ref_for = external_trait_specification_of(tcx, trait_items, trait_vattrs)?;
    if let Some(ex_trait_ref_for) = ex_trait_ref_for {
        crate::rust_to_vir_base::check_item_external_generics(
            None,
            trait_generics,
            false,
            ex_trait_ref_for.args,
            true,
            trait_generics.span,
        )?;
        let external_predicates = tcx.predicates_of(ex_trait_ref_for.def_id);
        let proxy_predicates = tcx.predicates_of(trait_def_id);
        let mut preds1 = external_predicates.instantiate(tcx, ex_trait_ref_for.args).predicates;
        let mut preds2 = proxy_predicates.instantiate(tcx, ex_trait_ref_for.args).predicates;
        use crate::rust_to_vir_func::remove_ignored_trait_bounds_from_predicates;
        remove_ignored_trait_bounds_from_predicates(
            tcx,
            true,
            &[ex_trait_ref_for.def_id],
            Some(ex_trait_ref_for.args[0]),
            &mut preds1,
        );
        remove_ignored_trait_bounds_from_predicates(
            tcx,
            true,
            &[ex_trait_ref_for.def_id, trait_def_id],
            Some(ex_trait_ref_for.args[0]),
            &mut preds2,
        );
        if !crate::rust_to_vir_func::predicates_match(ctxt.tcx, &preds1, &preds2) {
            let err =
                err_span_bare(trait_span, "external_trait_specification trait bound mismatch")
                    .help(format!(
                        "external_trait_specification requires trait bounds to match exactly \
                    but the proxy's trait bounds are:\n{}\nthe external trait bounds are:\n{}",
                        preds2
                            .iter()
                            .map(|x| format!("  - {}", x.to_string()))
                            .collect::<Vec<_>>()
                            .join("\n"),
                        preds1
                            .iter()
                            .map(|x| format!("  - {}", x.to_string()))
                            .collect::<Vec<_>>()
                            .join("\n")
                    ));
            return Err(err);
        }
    }
    let ex_trait_id_for = ex_trait_ref_for.map(|r| r.def_id);
    if let Some(ex_trait_id_for) = ex_trait_id_for {
        trait_path = def_id_to_vir_path(tcx, &ctxt.verus_items, ex_trait_id_for);
    }
    if let Some(x) = &trait_vattrs.external_trait_specification {
        if ex_trait_id_for.is_none() {
            return err_span(
                trait_span,
                format!("`external_trait_specification` trait must declare a type {x}"),
            );
        }
    }

    for trait_item_ref in trait_items {
        let trait_item = tcx.hir().trait_item(trait_item_ref.id);
        let TraitItem { ident, owner_id, generics: item_generics, kind, span, defaultness: _ } =
            trait_item;
        let (item_generics_params, item_typ_bounds) = check_generics_bounds_with_polarity(
            tcx,
            &ctxt.verus_items,
            item_generics.span,
            Some(item_generics),
            false,
            owner_id.to_def_id(),
            None,
            Some(&mut *ctxt.diagnostics.borrow_mut()),
        )?;

        let attrs = tcx.hir().attrs(trait_item.hir_id());
        let vattrs = ctxt.get_verifier_attrs(attrs)?;
        if vattrs.external {
            return err_span(
                *span,
                "a trait item cannot be marked 'external' - perhaps you meant to mark the entire trait external?",
            );
        }

        let item_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, owner_id.to_def_id());
        let is_verus_spec =
            item_path.segments.last().expect("segment.last").starts_with(VERUS_SPEC);
        let ex_item_id_for = if let Some(ex_trait_id_for) = ex_trait_id_for {
            match kind {
                TraitItemKind::Type(_generic_bounds, None) => {
                    if Some(ident.to_string()) == trait_vattrs.external_trait_specification {
                        continue;
                    }
                }
                _ => {}
            }
            let assoc_item = tcx.associated_item(owner_id.to_def_id());
            let ex_assoc_items = tcx.associated_items(ex_trait_id_for);
            let ex_assoc_item =
                ex_assoc_items.find_by_name_and_kind(tcx, *ident, assoc_item.kind, ex_trait_id_for);
            if is_verus_spec {
                None
            } else if let Some(ex_assoc_item) = ex_assoc_item {
                Some(ex_assoc_item.def_id)
            } else {
                let name = tcx.def_path_str(ex_trait_id_for);
                return err_span(
                    *span,
                    format!("cannot find member named {ident} in trait {name}"),
                );
            }
        } else {
            None
        };

        match kind {
            TraitItemKind::Fn(sig, fun) => {
                let body_id = match fun {
                    TraitFn::Provided(_) if ex_trait_id_for.is_some() && !is_verus_spec => {
                        return err_span(
                            *span,
                            format!("`external_trait_specification` functions cannot have bodies"),
                        );
                    }
                    TraitFn::Provided(body_id) => CheckItemFnEither::BodyId(body_id),
                    TraitFn::Required(param_names) => CheckItemFnEither::ParamNames(*param_names),
                };
                let attrs = tcx.hir().attrs(trait_item.hir_id());
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
                    ex_trait_id_for,
                    ex_item_id_for,
                    external_info,
                )?;
                if let Some(fun) = fun {
                    method_names.push(fun);
                }
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

                let bounds = tcx.item_bounds(trait_item.owner_id.def_id.to_def_id()).skip_binder();
                let bounds = bounds.iter().map(|p| (p, *span)).collect::<Vec<_>>();
                let vir_bounds = process_predicate_bounds(
                    tcx,
                    trait_def_id,
                    &ctxt.verus_items,
                    bounds.iter(),
                    tcx.generics_of(trait_def_id),
                )?;
                assoc_typs_bounds.extend(vir_bounds);

                if let Some(ex_trait_ref_for) = ex_trait_ref_for {
                    let ex_item_id_for = ex_item_id_for.expect("ex_item_id_for");
                    let external_predicates = tcx.item_bounds(ex_item_id_for);
                    let proxy_predicates = tcx.item_bounds(owner_id.to_def_id());
                    let preds1 = external_predicates.instantiate(tcx, ex_trait_ref_for.args);
                    let preds2 = proxy_predicates.instantiate(tcx, ex_trait_ref_for.args);
                    // TODO, but low priority, since this is just a check for trusted declarations:
                    // crate::rust_to_vir_func::predicates_match(tcx, true, &preds1.iter().collect(), &preds2.iter().collect())?;
                    // (would need to fix up the TyKind::Alias projections inside the clauses)

                    if preds1.len() != preds2.len() {
                        return err_span(
                            trait_span,
                            format!(
                                "Mismatched bounds on associated type\n{:?}\n vs.\n{:?}",
                                preds1, preds2
                            ),
                        );
                    }
                }
            }
            TraitItemKind::Const(_, _) => {
                return err_span(trait_span, "Verus does not yet support associated constants");
            }
        }
    }
    let mut methods = vir::headers::make_trait_decls(methods)?;
    vir.functions.append(&mut methods);
    let mut assoc_typs_bounds = Arc::new(assoc_typs_bounds);
    let target_trait_id = if let Some(target_trait_id) = ex_trait_id_for {
        typ_bounds =
            vir::traits::rewrite_external_bounds(&orig_trait_path, &trait_path, &typ_bounds);
        assoc_typs_bounds =
            vir::traits::rewrite_external_bounds(&orig_trait_path, &trait_path, &assoc_typs_bounds);
        target_trait_id
    } else {
        trait_def_id
    };
    external_info.local_trait_ids.push(target_trait_id);
    let traitx = TraitX {
        name: trait_path,
        proxy: ex_trait_id_for.map(|_| (*ctxt.spanned_new(trait_span, orig_trait_path)).clone()),
        visibility,
        methods: Arc::new(method_names),
        assoc_typs: Arc::new(assoc_typs),
        typ_params: generics_params,
        typ_bounds,
        assoc_typs_bounds,
    };
    vir.traits.push(ctxt.spanned_new(trait_span, traitx));
    Ok(())
}
