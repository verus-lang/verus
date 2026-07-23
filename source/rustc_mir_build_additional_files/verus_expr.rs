use crate::thir::cx::ThirBuildCx;
use crate::verus::CallErasure;
use crate::verus::{
    erase_node, erase_node_unadjusted, erase_tree_kind, erased_ghost_value, handle_call,
    is_node_with_single_arg_erased_or_shadow,
};
use crate::verus_time_travel_prevention::try_move_head_into_shadow;
use rustc_hir::HirId;
use rustc_hir::{Expr, ExprKind, UnOp};
use rustc_middle::thir;
use rustc_middle::thir::{ExprId, LocalVarId, Pat, PatKind};
use rustc_middle::ty::TyKind;
use rustc_middle::ty::adjustment::{Adjust, Adjustment, AutoBorrow, DerefAdjustKind};

pub(crate) fn mirror_expr_adjusted_pre<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<rustc_middle::thir::ExprId> {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return None;
    };
    if erasure_ctxt.adjusted_node_erasure.contains(&expr.hir_id) {
        Some(erased_ghost_value(
            cx,
            &erasure_ctxt,
            expr.hir_id,
            expr.span,
            cx.typeck_results.expr_ty_adjusted(expr),
        ))
    } else {
        None
    }
}

// To avoid edits and conflicts in thir/cx/expr.rs, postprocess some of the work for expr.rs here
pub(crate) fn apply_adjustment_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
    adjustment: &Adjustment<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
) -> rustc_middle::thir::ExprKind<'tcx> {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return kind;
    };

    // This has to go first because:
    //  try_move_head_into_shadow handles fields/dereferences for shadow values
    //  erase_node handles a variety of ops for ghost values AND shadow values
    // If try_move_head_ito_shadow applies, it needs to take priority.
    if let Some(kind) = try_move_head_into_shadow(cx, expr, adjustment.target, &kind) {
        return kind;
    }

    let kind = match adjustment.kind {
        Adjust::Deref(DerefAdjustKind::Builtin | DerefAdjustKind::Overloaded(_))
        | Adjust::Borrow(AutoBorrow::Ref(_))
        | Adjust::NeverToAny => {
            // Adjust::Deref(None) -> implicit *
            // Adjust::Borrow(AutoBorrow::Ref(_)) -> implicit &
            // Adjust::Deref(Some(_)) -> This case means inserting a Deref::deref function.
            //   In spec code that would usually be an error, except for some cases
            //   like Arc or Rc where we ignore the deref in spec code.
            //   In all those cases we also want to erase.
            if is_node_with_single_arg_erased_or_shadow(cx, &erasure_ctxt, &kind) {
                erase_node(cx, expr, adjustment.target, kind)
            } else {
                kind
            }
        }
        _ => kind,
    };
    crate::verus_time_travel_prevention::expr_post(cx, expr, adjustment.target, kind)
}

// To avoid edits and conflicts in thir/cx/expr.rs, preprocess some of the work for expr.rs here
pub(crate) fn mirror_expr_pre<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<rustc_middle::thir::ExprKind<'tcx>> {
    match expr.kind {
        ExprKind::MethodCall(..) | ExprKind::Call(..) | ExprKind::Struct(..) => {
            let (call_erasure, _) = handle_call(&cx.verus_ctxt, expr);
            match call_erasure {
                CallErasure::EraseTree(t) => Some(erase_tree_kind(cx, expr, expr.hir_id, t)),
                _ => None,
            }
        }
        _ => None,
    }
}

// To avoid edits and conflicts in thir/cx/expr.rs, postprocess some of the work for expr.rs here
pub(crate) fn mirror_expr_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
) -> rustc_middle::thir::ExprKind<'tcx> {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return kind;
    };

    let ty = cx.typeck_results.expr_ty(expr);
    if let Some(kind) = try_move_head_into_shadow(cx, expr, ty, &kind) {
        return kind;
    }

    let kind = match expr.kind {
        ExprKind::MethodCall(..) | ExprKind::Call(..) | ExprKind::Struct(..) => {
            let (call_erasure, force_treat_inhabited) = handle_call(&cx.verus_ctxt, expr);
            if force_treat_inhabited {
                // We use the id of the fun because we don't know the id of the call yet
                if let thir::ExprKind::Call { fun, .. } = kind {
                    cx.verus_ctxt.extra_thir.force_treat_inhabited.insert(fun);
                }
            }
            if call_erasure.should_erase() { erase_node_unadjusted(cx, expr, kind) } else { kind }
        }
        ExprKind::Field(..) | ExprKind::AddrOf(..) => {
            if is_node_with_single_arg_erased_or_shadow(cx, &erasure_ctxt, &kind) {
                erase_node_unadjusted(cx, expr, kind)
            } else {
                kind
            }
        }
        ExprKind::Unary(UnOp::Deref, _) if !cx.typeck_results.is_method_call(expr) => {
            if is_node_with_single_arg_erased_or_shadow(cx, &erasure_ctxt, &kind) {
                erase_node_unadjusted(cx, expr, kind)
            } else {
                kind
            }
        }
        _ => kind,
    };

    crate::verus_time_travel_prevention::expr_post(cx, expr, ty, kind)
}

pub(crate) fn enter_guard<'tcx>(cx: &mut ThirBuildCx<'tcx>, pat: &Pat<'tcx>) {
    let mut v = vec![];
    pat_get_ids(pat, &mut v);
    cx.verus_ctxt.guard_pattern_vars.push(v);
}

pub(crate) fn exit_guard<'tcx>(cx: &mut ThirBuildCx<'tcx>) {
    cx.verus_ctxt.guard_pattern_vars.pop().unwrap();
}

pub(crate) fn enter_block<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    block: &'tcx rustc_hir::Block<'tcx>,
) -> bool {
    if let Some(ctxt) = cx.verus_ctxt.ctxt.clone()
        && ctxt.local_invariant_bodies.contains_key(&block.hir_id)
    {
        cx.verus_ctxt.local_invariants.push(cx.thir.exprs.len());
        true
    } else {
        false
    }
}

pub(crate) fn exit_block<'tcx>(cx: &mut ThirBuildCx<'tcx>, block: &'tcx rustc_hir::Block<'tcx>) {
    if let Some(ctxt) = cx.verus_ctxt.ctxt.clone()
        && let Some(body) = ctxt.local_invariant_bodies.get(&block.hir_id)
    {
        let old_idx = cx.verus_ctxt.local_invariants.pop().unwrap();
        let new_idx = cx.thir.exprs.len();
        for i in old_idx..new_idx {
            let expr_id = ExprId::from_usize(i);
            if matches!(
                cx.thir.exprs[expr_id].kind,
                rustc_middle::thir::ExprKind::Call { .. }
                    | rustc_middle::thir::ExprKind::Loop { .. }
                    | rustc_middle::thir::ExprKind::LoopMatch { .. }
            ) {
                cx.verus_ctxt
                    .extra_thir
                    .local_invs_for_node
                    .entry(expr_id)
                    .or_insert_with(|| vec![])
                    .push(body.clone());
            }
        }
    } else {
        unreachable!()
    }
}

pub(crate) fn is_bound_via_pattern_guard<'tcx>(cx: &ThirBuildCx<'tcx>, var_hir_id: HirId) -> bool {
    let var = LocalVarId(var_hir_id);
    cx.verus_ctxt.guard_pattern_vars.iter().any(|v| v.iter().any(|v| v == &var))
}

fn pat_get_ids<'tcx>(pat: &Pat<'tcx>, out: &mut Vec<LocalVarId>) {
    match &pat.kind {
        PatKind::Missing => {}
        PatKind::Wild => {}
        PatKind::Binding {
            name: _,
            mode: _,
            var,
            ty: _,
            subpattern,
            is_primary: _,
            is_shorthand: _,
        } => {
            out.push(*var);
            if let Some(subpattern) = subpattern {
                pat_get_ids(subpattern, out);
            }
        }
        PatKind::Variant { adt_def: _, args: _, variant_index: _, subpatterns }
        | PatKind::Leaf { subpatterns } => {
            for field_pat in subpatterns.iter() {
                pat_get_ids(&field_pat.pattern, out);
            }
        }
        PatKind::Deref { subpattern, pin: _ } => pat_get_ids(subpattern, out),
        PatKind::DerefPattern { subpattern, borrow: _ } => {
            pat_get_ids(subpattern, out);
        }
        PatKind::Constant { value: _ } => {}
        PatKind::Range(_pat_range) => {}
        PatKind::Slice { prefix, slice, suffix } | PatKind::Array { prefix, slice, suffix } => {
            for p in prefix.iter() {
                pat_get_ids(p, out);
            }
            if let Some(sl) = slice {
                pat_get_ids(sl, out);
            }
            for p in suffix.iter() {
                pat_get_ids(p, out);
            }
        }
        PatKind::Or { pats } => {
            if pats.len() > 0 {
                pat_get_ids(&pats[0], out);
            }
        }
        PatKind::Guard { subpattern, condition: _ } => {
            pat_get_ids(subpattern, out);
        }
        PatKind::Never => {}
        PatKind::Error(_error_guaranteed) => {}
    }
}

pub(crate) fn scope_post<'tcx>(cx: &mut ThirBuildCx<'tcx>, expr_id: ExprId) -> ExprId {
    let thir::ExprKind::Scope { region_scope, value, hir_id } = cx.thir[expr_id].kind else {
        panic!("scope_post expected ExprKind::Scope");
    };

    // Replace `Scope(two_phase_mutable_reference_tie(&mut a, &mut b))` with:
    // two_phase_mutable_reference_tie(Scope(&mut a), &mut b)
    //
    // The reason to do this is that the mir_build code specifically looks for the following
    // pattern: `func_call(..., two_phase_mutable_reference_tie(...), ...)`
    // and having a Scope in between interferes with that.
    //
    // REVIEW: given the complexity of this transformation, it may be better to just handle
    // Scopes in the mir building code so we can delete this step.

    match cx.thir.exprs[value].kind {
        thir::ExprKind::Call { ty, fun, ref args, from_hir_call, fn_span } => {
            let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
                return expr_id;
            };
            match ty.kind() {
                TyKind::FnDef(fn_def_id, _)
                    if *fn_def_id == erasure_ctxt.two_phase_mutable_reference_tie_fn_def_id
                        || *fn_def_id == erasure_ctxt.mutable_reference_tie_fn_def_id =>
                {
                    assert!(args.len() == 2);
                    let arg0 = args[0];
                    let arg1 = args[1];
                    let arg = cx.thir.exprs.push(thir::Expr {
                        temp_scope_id: cx.thir[expr_id].temp_scope_id,
                        ty: cx.thir[arg0].ty,
                        span: cx.thir[arg0].span,
                        kind: thir::ExprKind::Scope { region_scope, value: arg0, hir_id },
                    });
                    let args = Box::new([arg, arg1]);
                    return cx.thir.exprs.push(thir::Expr {
                        temp_scope_id: cx.thir[value].temp_scope_id,
                        ty: cx.thir.exprs[value].ty,
                        span: cx.thir.exprs[value].span,
                        kind: thir::ExprKind::Call { ty, fun, args, from_hir_call, fn_span },
                    });
                }
                _ => {}
            }
        }
        _ => {}
    }
    return expr_id;
}
