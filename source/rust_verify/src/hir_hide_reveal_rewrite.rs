use rustc_hir::{ExprKind, MaybeOwner, OwnerNode, def_id::LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefIndex;
use std::collections::HashMap;

pub(crate) enum ResOrSymbol {
    Res(rustc_hir::def::Res),
    Symbol(rustc_span::symbol::Symbol),
}

pub(crate) fn hir_hide_reveal_rewrite<'tcx>(
    mut crate_: rustc_middle::hir::Crate<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> rustc_middle::hir::Crate<'tcx> {
    // To read all owners from the original crate without triggering query cycles,
    // we temporarily clear delayed_ids. With delayed_ids empty, Crate::owner()
    // returns directly from the internal owners vec (even for Phantom entries)
    // without falling through to tcx.delayed_owner().
    let delayed_ids = std::mem::take(&mut crate_.delayed_ids);
    let mut new_owners: IndexVec<LocalDefId, MaybeOwner<'tcx>> = IndexVec::new();
    let num_defs = tcx.definitions_untracked().num_definitions();
    for i in 0..num_defs {
        let def_id = LocalDefId { local_def_index: DefIndex::from_usize(i) };
        let owner = new_owners.ensure_contains_elem(def_id, || MaybeOwner::Phantom);
        *owner = crate_.owner(tcx, def_id);
    }
    for new_owner in new_owners.iter_mut() {
        if let MaybeOwner::Owner(inner_owner) = new_owner {
            if let OwnerNode::Item(item) = inner_owner.node() {
                if let rustc_hir::ItemKind::Fn { ident, body: body_id, .. } = &item.kind {
                    if ident.as_str() == "__VERUS_REVEAL_INTERNAL__" {
                        *new_owner =
                            rewrite_reveal_internal(inner_owner, item, body_id, tcx);
                    }
                }
            }
        }
    }
    rustc_middle::hir::Crate::new(
        new_owners,
        delayed_ids,
        crate_.delayed_resolver,
        crate_.opt_hir_hash.clone(),
    )
}

fn rewrite_reveal_internal<'tcx>(
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
    item: &'tcx rustc_hir::Item<'tcx>,
    body_id: &rustc_hir::BodyId,
    tcx: TyCtxt<'tcx>,
) -> MaybeOwner<'tcx> {
    {
        assert_eq!(inner_owner.nodes.bodies.len(), 1);
        let mut bodies = inner_owner.nodes.bodies.clone();
        let old_body = bodies[&body_id.hir_id.local_id];
        let emit_invalid_error = || {
            tcx.sess
                .dcx()
                .struct_span_err(
                    item.span,
                    "invalid reveal/hide: this is likely a bug, please report it",
                )
                .emit()
        };

        (|| {
            let ExprKind::Block(stmts, expr) = old_body.value.kind else {
                emit_invalid_error();
                return;
            };
            if expr.is_some() || stmts.stmts.len() != 0 {
                emit_invalid_error();
                return;
            };
            let Some(expr) = stmts.expr else {
                emit_invalid_error();
                return;
            };
            let ExprKind::Call(callee, args) = expr.kind else {
                emit_invalid_error();
                return;
            };
            let ExprKind::Path(rustc_hir::QPath::Resolved(None, _callee_res_path)) = callee.kind
            else {
                emit_invalid_error();
                return;
            };

            // We'd normally use verus_items, but they are not available here.
            // In fact, we can't even use 'is_diagnostic_item'; I have observed
            // that trying to call 'is_diagnostic_item' here for an item
            // *in the current crate* causes rustc to hang indefinitely.
            // (Furthermore, when embedding 'verus_builtin' as a module rather than
            // a crate, it is *expected* that the item is in the current crate.)

            // REVIEW What should we replace this check with?

            /*if !tcx.is_diagnostic_item(
                rustc_span::symbol::Symbol::intern(
                    "verus::verus_builtin::reveal_hide_internal_path",
                ),
                callee_res_path.res.def_id(),
            ) {
                emit_invalid_error();
                return;
            }*/

            if args.len() != 1 {
                emit_invalid_error();
                return;
            }

            let resolved = match &args[0].kind {
                ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) => {
                    (None, ResOrSymbol::Res(path.res))
                }
                ExprKind::Path(rustc_hir::QPath::Resolved(Some(ty), path)) => {
                    let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(None, ty_ppath)) =
                        ty.kind
                    else {
                        emit_invalid_error();
                        return;
                    };
                    (Some(ty_ppath.res), ResOrSymbol::Res(path.res))
                }
                ExprKind::Path(rustc_hir::QPath::TypeRelative(ty, ps)) => {
                    let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(None, ty_ppath)) =
                        ty.kind
                    else {
                        emit_invalid_error();
                        return;
                    };

                    if let Some(invalid_ty_arg_span) = ty_ppath.segments.iter().find_map(|ps_w| {
                        ps_w.args.and_then(|args| {
                            args.args.iter().find_map(|ps_a| {
                                match ps_a {
                                    rustc_hir::GenericArg::Lifetime(l) => !l.is_anonymous(),
                                    rustc_hir::GenericArg::Type(t) => {
                                        !matches!(t.kind, rustc_hir::TyKind::Infer(_))
                                    }
                                    rustc_hir::GenericArg::Const(_) => true,
                                    rustc_hir::GenericArg::Infer(_) => false,
                                }
                                .then(|| ps_a.span())
                            })
                        })
                    }) {
                        tcx.sess
                            .dcx()
                            .struct_span_warn(
                                invalid_ty_arg_span,
                                "in hide/reveal, type arguments are ignored, replace them with `_`",
                            )
                            .emit();
                    }

                    if ps.res == rustc_hir::def::Res::Err {
                        (Some(ty_ppath.res), ResOrSymbol::Symbol(ps.ident.name))
                    } else {
                        (Some(ty_ppath.res), ResOrSymbol::Res(ps.res))
                    }
                }
                _ => {
                    emit_invalid_error();
                    return;
                }
            };
            let mut guard =
                crate::verifier::BODY_HIR_ID_TO_REVEAL_PATH_RES.write().expect("lock failed");
            if guard.is_none() {
                *guard = Some(HashMap::new());
            }
            let Some(path_map) = &mut *guard else {
                unreachable!();
            };
            path_map.insert(body_id.hir_id.owner.def_id.to_def_id(), resolved);
        })();

        let expr = tcx.hir_arena.alloc(rustc_hir::Expr {
            hir_id: old_body.value.hir_id,
            kind: rustc_hir::ExprKind::Tup(&[]),
            span: old_body.value.span,
        });
        let body = tcx.hir_arena.alloc(rustc_hir::Body { params: old_body.params, value: expr });
        bodies[&body_id.hir_id.local_id] = body;

        let nodes: rustc_hir::OwnerNodes<'tcx> = rustc_hir::OwnerNodes {
            opt_hash_including_bodies: inner_owner.nodes.opt_hash_including_bodies,
            nodes: inner_owner.nodes.nodes.clone(),
            bodies,
        };
        let attrs: rustc_hir::AttributeMap<'tcx> = rustc_hir::AttributeMap {
            map: inner_owner.attrs.map.clone(),
            opt_hash: inner_owner.attrs.opt_hash,
            define_opaque: None,
        };
        let owner_info = tcx.hir_arena.alloc(rustc_hir::OwnerInfo {
            nodes,
            parenting: inner_owner.parenting.clone(),
            attrs,
            trait_map: inner_owner
                .trait_map
                .items()
                .map(|(&id, traits)| {
                    let as_vec = traits
                        .iter()
                        .map(|trait_| rustc_hir::TraitCandidate {
                            def_id: trait_.def_id,
                            import_ids: trait_.import_ids,
                            lint_ambiguous: false,
                        })
                        .collect::<Vec<_>>();
                    let alloced: &[rustc_hir::TraitCandidate<'_>] =
                        tcx.hir_arena.alloc_slice(&as_vec);
                    (id, alloced)
                })
                .collect(),
            delayed_lints: rustc_hir::lints::DelayedLints { lints: Box::new([]), opt_hash: None },
        });
        rustc_hir::MaybeOwner::Owner(owner_info)
    }
}
