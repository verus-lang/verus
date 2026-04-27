use crate::thir::cx::ThirBuildCx;
use crate::verus::CallErasure;
use crate::verus::{
    erase_node, erase_node_unadjusted, erase_tree_kind, erased_ghost_value, handle_call,
    is_node_with_single_arg_erased_or_shadow,
};
use crate::verus_time_travel_prevention::try_move_head_into_shadow;
use rustc_hir::HirId;
use rustc_hir::{Expr, ExprKind, UnOp};
use rustc_middle::thir::{LocalVarId, Pat, PatKind};
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
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
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
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
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
        PatKind::Never => {}
        PatKind::Error(_error_guaranteed) => {}
    }
}
