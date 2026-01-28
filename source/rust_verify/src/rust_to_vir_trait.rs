use crate::attributes::VerifierAttrs;
use crate::context::Context;
use crate::external::CrateItems;
use crate::rust_to_vir_base::{check_generics_bounds_with_polarity, process_predicate_bounds};
use crate::rust_to_vir_func::{CheckItemFnEither, check_item_fn};
use crate::rust_to_vir_impl::ExternalInfo;
use crate::unsupported_err_unless;
use crate::util::{err_span, err_span_bare};
use rustc_hir::{Generics, Safety, TraitFn, TraitItem, TraitItemId, TraitItemKind};
use rustc_middle::ty::{ClauseKind, TraitPredicate, TraitRef, TyCtxt};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use std::sync::Arc;
use vir::ast::{
    Fun, Function, FunctionKind, GenericBound, Ident, KrateX, TraitX, VirErr, Visibility,
};
use vir::def::VERUS_SPEC;

pub(crate) fn make_external_trait_extension_impl_map<'tcx>(
    ctxt: &Context<'tcx>,
    external_info: &mut ExternalInfo,
    imported: &Vec<vir::ast::Krate>,
    crate_items: &CrateItems,
) -> Result<(), VirErr> {
    use crate::external::{GeneralItemId, VerifOrExternal};
    use rustc_hir::ItemKind;

    for krate in imported.iter() {
        for t in &krate.traits {
            if let Some((spec, imp)) = &t.x.external_trait_extension {
                let m = &mut external_info.external_trait_extension_impl_map;
                assert!(!m.contains_key(imp));
                m.insert(imp.clone(), spec.clone());
            }
        }
    }

    for crate_item in crate_items.items.iter() {
        match &crate_item.verif {
            VerifOrExternal::VerusAware { .. } => match crate_item.id {
                GeneralItemId::ItemId(item_id) => {
                    let item = ctxt.tcx.hir_item(item_id);
                    let trait_def_id = item.owner_id.to_def_id();
                    match &item.kind {
                        ItemKind::Trait(..) => {
                            let attrs = ctxt.tcx.hir_attrs(item.hir_id());
                            let vattrs = ctxt.get_verifier_attrs(attrs)?;
                            if let Some((spec, imp)) = vattrs.external_trait_extension {
                                let path = ctxt.def_id_to_vir_path(trait_def_id);
                                let spec = path.replace_last(Arc::new(spec.clone()));
                                let imp = path.replace_last(Arc::new(imp.clone()));
                                let m = &mut external_info.external_trait_extension_impl_map;
                                assert!(!m.contains_key(&imp));
                                m.insert(imp, spec);
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    Ok(())
}

pub(crate) fn external_trait_specification_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_items: &'tcx [TraitItemId],
    trait_vattrs: &VerifierAttrs,
) -> Result<Option<TraitRef<'tcx>>, VirErr> {
    let mut ex_trait_ref_for: Option<TraitRef> = None;
    for trait_item_id in trait_items {
        let trait_item = tcx.hir_trait_item(*trait_item_id);
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
                                polarity: rustc_middle::ty::PredicatePolarity::Positive,
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
    trait_items: &'tcx [TraitItemId],
    trait_vattrs: &VerifierAttrs,
    external_info: &mut ExternalInfo,
    crate_items: &CrateItems,
    safety: Safety,
) -> Result<(), VirErr> {
    let tcx = ctxt.tcx;
    let orig_trait_path = ctxt.def_id_to_vir_path(trait_def_id);
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
        vir::traits::remove_self_is_itself_bound(&mut typ_bounds, &trait_path, &generics_params);
        (generics_params, typ_bounds)
    };
    let mut assoc_typs: Vec<Ident> = Vec::new();
    let mut assoc_typs_bounds: Vec<GenericBound> = Vec::new();
    let mut methods: Vec<Function> = Vec::new();
    let mut method_names: Vec<Fun> = Vec::new();
    let ex_trait_ref_for = external_trait_specification_of(tcx, trait_items, trait_vattrs)?;
    let external_trait_extension = &trait_vattrs.external_trait_extension;
    let trait_extension = if let Some((spec, _)) = external_trait_extension {
        if ex_trait_ref_for.is_none() {
            return err_span(trait_span, "unexpected `external_trait_extension`");
        }
        Some(spec.clone())
    } else {
        None
    };
    if let Some(ex_trait_ref_for) = ex_trait_ref_for {
        crate::rust_to_vir_base::check_item_external_generics(
            ctxt.tcx,
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
            ctxt,
            true,
            &[ex_trait_ref_for.def_id],
            Some(ex_trait_ref_for.args[0]),
            &mut preds1,
        );
        remove_ignored_trait_bounds_from_predicates(
            ctxt,
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
                        preds2.iter().map(|x| format!("  - {x}")).collect::<Vec<_>>().join("\n"),
                        preds1.iter().map(|x| format!("  - {x}")).collect::<Vec<_>>().join("\n")
                    ));
            return Err(err);
        }
    }
    let ex_trait_id_for = ex_trait_ref_for.map(|r| r.def_id);
    if let Some(ex_trait_id_for) = ex_trait_id_for {
        trait_path = ctxt.def_id_to_vir_path(ex_trait_id_for);
    }
    if let Some(x) = &trait_vattrs.external_trait_specification {
        if ex_trait_id_for.is_none() {
            return err_span(
                trait_span,
                format!("`external_trait_specification` trait must declare a type {x}"),
            );
        }
    }

    for trait_item_id in trait_items {
        let trait_item = tcx.hir_trait_item(*trait_item_id);
        let TraitItem {
            ident,
            owner_id,
            generics: item_generics,
            kind,
            span,
            defaultness: _,
            has_delayed_lints: _,
        } = trait_item;
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

        if crate_items.is_trait_item_external(*trait_item_id) {
            return err_span(
                *span,
                "a trait item cannot be marked 'external' - perhaps you meant to mark the entire trait external?",
            );
        }

        let item_path = ctxt.def_id_to_vir_path(owner_id.to_def_id());
        let is_verus_spec =
            item_path.segments.last().expect("segment.last").starts_with(VERUS_SPEC);
        let attrs = tcx.hir_attrs(trait_item.hir_id());
        let ex_item_id_for = if let Some(ex_trait_id_for) = ex_trait_id_for {
            match kind {
                TraitItemKind::Type(_generic_bounds, None) => {
                    if Some(ident.to_string()) == trait_vattrs.external_trait_specification {
                        continue;
                    }
                }
                _ => {}
            }
            use vir::ast::Mode;
            let mode = crate::attributes::get_mode(Mode::Exec, attrs);
            let assoc_item = tcx.associated_item(owner_id.to_def_id());
            let ex_assoc_items = tcx.associated_items(ex_trait_id_for);
            let ex_assoc_item = ex_assoc_items.find_by_ident_and_kind(
                tcx,
                *ident,
                assoc_item.as_tag(),
                ex_trait_id_for,
            );
            if mode == Mode::Spec {
                if external_trait_extension.is_some() {
                    if let TraitItemKind::Fn(_, TraitFn::Provided(_)) = kind {
                        if !is_verus_spec {
                            return err_span(
                                *span,
                                "feature not yet supported: external spec extensions cannot yet provide default bodies",
                            );
                        }
                        // TODO: support defaults
                        // (they would currently just get dropped here if we didn't return an error)
                    }
                    // spec functions live in extension trait, not in our trait
                    continue;
                } else if !is_verus_spec && ex_assoc_item.is_none() {
                    return err_span(
                        *span,
                        "external spec extensions only allowed in `external_trait_extension` traits",
                    );
                }
            }
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
                // putting param_names here ensures that Vec in TraitFn::Required case below lives long enough
                let param_names;
                let (body_id, has_default) = match fun {
                    TraitFn::Provided(_) if ex_trait_id_for.is_some() && !is_verus_spec => {
                        return err_span(
                            *span,
                            format!("`external_trait_specification` functions cannot have bodies"),
                        );
                    }
                    TraitFn::Provided(body_id) => (CheckItemFnEither::BodyId(body_id), true),
                    TraitFn::Required(opt_param_names) => {
                        // REVIEW: Is filtering out `None`s the right thing to do here?
                        param_names =
                            opt_param_names.into_iter().flatten().cloned().collect::<Vec<_>>();
                        (CheckItemFnEither::ParamNames(param_names.as_slice()), false)
                    }
                };
                // requires and ensures on exec functions can refer to spec extension trait:
                let trait_extension_in_spec =
                    if is_verus_spec { trait_extension.clone() } else { None };
                let fun = check_item_fn(
                    ctxt,
                    &mut methods,
                    None,
                    owner_id.to_def_id(),
                    FunctionKind::TraitMethodDecl { trait_path: trait_path.clone(), has_default },
                    visibility.clone(),
                    module_path,
                    attrs,
                    sig,
                    Some((trait_generics, trait_def_id)),
                    item_generics,
                    body_id,
                    ex_trait_id_for.map(|d| (d, trait_extension_in_spec)),
                    ex_item_id_for,
                    external_info,
                    None,
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

                    let mut preds1 = preds1.to_vec();
                    let mut preds2 = preds2.to_vec();
                    preds1.sort_by_key(|x| x.to_string());
                    preds2.sort_by_key(|x| x.to_string());

                    if preds1.len() != preds2.len() {
                        let mut t = format!(
                            "Mismatched bounds on associated type ({} != {})\n",
                            preds1.len(),
                            preds2.len(),
                        );
                        t.push_str("Target:\n");
                        for p1 in preds1.iter() {
                            t.push_str(&format!("  - {}\n", p1));
                        }
                        t.push_str("External specification:\n");
                        for p2 in preds2.iter() {
                            t.push_str(&format!("  - {}\n", p2));
                        }
                        return err_span(trait_span, t);
                    }

                    for (p1, p2) in preds1.iter().zip(preds2.iter()) {
                        match (p1.kind().skip_binder(), p2.kind().skip_binder()) {
                            (ClauseKind::Trait(p1), ClauseKind::Trait(p2)) => {
                                if p1.def_id() != p2.def_id() {
                                    return err_span(
                                        trait_span,
                                        format!(
                                            "Mismatched bounds on associated type ({} != {})",
                                            p1, p2
                                        ),
                                    );
                                }
                            }
                            _ => {
                                return err_span(
                                    trait_span,
                                    "Verus does not yet support this bound on external specs",
                                );
                            }
                        }
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
    let external_trait_extension = if let Some((spec, imp)) = external_trait_extension {
        let spec = orig_trait_path.replace_last(Arc::new(spec.clone()));
        let imp = orig_trait_path.replace_last(Arc::new(imp.clone()));
        Some((spec, imp))
    } else {
        None
    };
    let traitx = TraitX {
        name: trait_path,
        proxy: ex_trait_id_for.map(|_| (*ctxt.spanned_new(trait_span, orig_trait_path)).clone()),
        visibility,
        methods: Arc::new(method_names),
        assoc_typs: Arc::new(assoc_typs),
        typ_params: generics_params,
        typ_bounds,
        assoc_typs_bounds,
        is_unsafe: match safety {
            Safety::Safe => false,
            Safety::Unsafe => true,
        },
        dyn_compatible: None,
        external_trait_extension,
    };
    vir.traits.push(ctxt.spanned_new(trait_span, traitx));
    Ok(())
}
