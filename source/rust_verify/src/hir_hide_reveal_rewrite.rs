use rustc_hir::{ExprKind, OwnerNode};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;

pub(crate) enum ResOrSymbol {
    Res(rustc_hir::def::Res),
    Symbol(rustc_span::symbol::Symbol),
}

pub(crate) fn hir_hide_reveal_rewrite<'tcx>(
    crate_: &mut rustc_hir::Crate<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    for owner in crate_.owners.iter_mut() {
        if let rustc_hir::MaybeOwner::Owner(inner_owner) = owner {
            match inner_owner.node() {
                OwnerNode::Item(item) => {
                    match &item.kind {
                        rustc_hir::ItemKind::Fn(_sig, _generics, body_id) => {
                            if item.ident.as_str() == "__VERUS_REVEAL_INTERNAL__" {
                                assert_eq!(inner_owner.nodes.bodies.len(), 1);
                                let mut bodies = inner_owner.nodes.bodies.clone();
                                let old_body = bodies[&body_id.hir_id.local_id];
                                let emit_invalid_error = || {
                                    tcx.sess.dcx()
                                        .struct_span_err(item.span, "invalid reveal/hide: this is likely a bug, please report it")
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
                                    let ExprKind::Path(rustc_hir::QPath::Resolved(
                                        None,
                                        _callee_res_path,
                                    )) = callee.kind
                                    else {
                                        emit_invalid_error();
                                        return;
                                    };

                                    // We'd normally use verus_items, but they are not available here.
                                    // In fact, we can't even use 'is_diagnostic_item'; I have observed
                                    // that trying to call 'is_diagnostic_item' here for an item
                                    // *in the current crate* causes rustc to hang indefinitely.
                                    // (Furthermore, when embedding 'builtin' as a module rather than
                                    // a crate, it is *expected* that the item is in the current crate.)

                                    // REVIEW What should we replace this check with?

                                    /*if !tcx.is_diagnostic_item(
                                        rustc_span::symbol::Symbol::intern(
                                            "verus::builtin::reveal_hide_internal_path",
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
                                        ExprKind::Path(rustc_hir::QPath::Resolved(
                                            Some(ty),
                                            path,
                                        )) => {
                                            let rustc_hir::TyKind::Path(
                                                rustc_hir::QPath::Resolved(None, ty_ppath),
                                            ) = ty.kind
                                            else {
                                                emit_invalid_error();
                                                return;
                                            };
                                            (Some(ty_ppath.res), ResOrSymbol::Res(path.res))
                                        }
                                        ExprKind::Path(rustc_hir::QPath::TypeRelative(ty, ps)) => {
                                            let rustc_hir::TyKind::Path(
                                                rustc_hir::QPath::Resolved(None, ty_ppath),
                                            ) = ty.kind
                                            else {
                                                emit_invalid_error();
                                                return;
                                            };

                                            if let Some(invalid_ty_arg_span) =
                                                ty_ppath.segments.iter().find_map(|ps_w| {
                                                    ps_w.args.and_then(|args| {
                                                        args.args.iter().find_map(|ps_a| {
                                                            match ps_a {
                                                                rustc_hir::GenericArg::Lifetime(
                                                                    l,
                                                                ) => !l.is_anonymous(),
                                                                rustc_hir::GenericArg::Type(t) => {
                                                                    !matches!(
                                                                        t.kind,
                                                                        rustc_hir::TyKind::Infer
                                                                    )
                                                                }
                                                                rustc_hir::GenericArg::Const(_) => {
                                                                    true
                                                                }
                                                                rustc_hir::GenericArg::Infer(_) => {
                                                                    false
                                                                }
                                                            }
                                                            .then(|| ps_a.span())
                                                        })
                                                    })
                                                })
                                            {
                                                tcx.sess.dcx()
                                                    .struct_span_warn(invalid_ty_arg_span, "in hide/reveal, type arguments are ignored, replace them with `_`")
                                                    .emit();
                                            }

                                            if ps.res == rustc_hir::def::Res::Err {
                                                (
                                                    Some(ty_ppath.res),
                                                    ResOrSymbol::Symbol(ps.ident.name),
                                                )
                                            } else {
                                                (Some(ty_ppath.res), ResOrSymbol::Res(ps.res))
                                            }
                                        }
                                        _ => {
                                            emit_invalid_error();
                                            return;
                                        }
                                    };
                                    let mut guard = crate::verifier::BODY_HIR_ID_TO_REVEAL_PATH_RES
                                        .write()
                                        .expect("lock failed");
                                    if guard.is_none() {
                                        *guard = Some(HashMap::new());
                                    }
                                    let Some(path_map) = &mut *guard else {
                                        unreachable!();
                                    };
                                    path_map
                                        .insert(body_id.hir_id.owner.def_id.to_def_id(), resolved);
                                })();

                                let expr = tcx.hir_arena.alloc(rustc_hir::Expr {
                                    hir_id: old_body.value.hir_id,
                                    kind: rustc_hir::ExprKind::Tup(&[]),
                                    span: old_body.value.span,
                                });
                                let body = tcx.hir_arena.alloc(rustc_hir::Body {
                                    params: old_body.params,
                                    value: expr,
                                    coroutine_kind: old_body.coroutine_kind,
                                });
                                bodies[&body_id.hir_id.local_id] = body;

                                let nodes: rustc_hir::OwnerNodes<'tcx> = rustc_hir::OwnerNodes {
                                    opt_hash_including_bodies: inner_owner
                                        .nodes
                                        .opt_hash_including_bodies,
                                    nodes: inner_owner.nodes.nodes.clone(),
                                    bodies,
                                };
                                let attrs: rustc_hir::AttributeMap<'tcx> =
                                    rustc_hir::AttributeMap {
                                        map: inner_owner.attrs.map.clone(),
                                        opt_hash: inner_owner.attrs.opt_hash,
                                    };
                                let owner_info = tcx.hir_arena.alloc(rustc_hir::OwnerInfo {
                                    nodes,
                                    parenting: inner_owner.parenting.clone(),
                                    attrs,
                                    trait_map: inner_owner
                                        .trait_map
                                        .items()
                                        .map(|(&id, traits)| {
                                            (
                                                id,
                                                traits
                                                    .iter()
                                                    .map(|trait_| rustc_hir::TraitCandidate {
                                                        def_id: trait_.def_id,
                                                        import_ids: trait_.import_ids.clone(),
                                                    })
                                                    .collect(),
                                            )
                                        })
                                        .collect(),
                                });
                                *owner = rustc_hir::MaybeOwner::Owner(owner_info);
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }
}
