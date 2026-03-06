use crate::thir::cx::ThirBuildCx;
use crate::verus::CallErasure;
use crate::verus::{
    erase_node, erase_node_unadjusted, erase_tree_kind, erased_ghost_value, handle_call,
    is_node_with_single_arg_erased,
    is_binary_node_with_any_arg_erased,
    preferred_erasure_ty, VerusErasureCtxt,
};
use rustc_hir::{Expr, ExprKind, UnOp};
use rustc_middle::ty::adjustment::{Adjust, Adjustment, AutoBorrow};
use rustc_middle::ty::Ty;

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
            preferred_erasure_ty(cx.tcx, cx.typeck_results.expr_ty_adjusted(expr)),
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
) -> (rustc_middle::thir::ExprKind<'tcx>, Ty<'tcx>) {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return (kind, adjustment.target);
    };

    let (kind, ty) = match adjustment.kind {
        Adjust::Deref(None | Some(_)) | Adjust::Borrow(AutoBorrow::Ref(_)) | Adjust::NeverToAny => {
            // Adjust::Deref(None) -> implicit *
            // Adjust::Borrow(AutoBorrow::Ref(_)) -> implicit &
            // Adjust::Deref(Some(_)) -> This case means inserting a Deref::deref function.
            //   In spec code that would usually be an error, except for some cases
            //   like Arc or Rc where we ignore the deref in spec code.
            //   In all those cases we also want to erase.
            if is_node_with_single_arg_erased(cx, &erasure_ctxt, &kind) {
                return erase_node(cx, expr, adjustment.target, kind);
            } else {
                (kind, adjustment.target)
            }
        }
        _ => (kind, adjustment.target)
    };
    let kind = crate::verus_time_travel_prevention::expr_post(cx, expr, adjustment.target, kind);
    (kind, ty)
}

// To avoid edits and conflicts in thir/cx/expr.rs, preprocess some of the work for expr.rs here
pub(crate) fn mirror_expr_pre<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<(rustc_middle::thir::ExprKind<'tcx>, Ty<'tcx>)> {
    match expr.kind {
        ExprKind::MethodCall(..) | ExprKind::Call(..) | ExprKind::Struct(..) => {
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
            match call_erasure {
                CallErasure::EraseTree(t) => Some(erase_tree_kind(cx, expr, t)),
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
) -> (rustc_middle::thir::ExprKind<'tcx>, Ty<'tcx>) {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return (kind, cx.typeck_results.expr_ty_adjusted(expr));
    };

    let kind = match expr.kind {
        ExprKind::MethodCall(..) | ExprKind::Call(..) => {
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
            if call_erasure.should_erase() {
                return erase_node_unadjusted(cx, expr, kind);
            } else {
                let kind = fixup_call_types(cx, expr, kind);
                return (kind, cx.typeck_results.expr_ty_adjusted(expr));
            }
        }
        ExprKind::Struct(..) => {
            // structs also go into the 'call' map
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
            if call_erasure.should_erase() {
                return erase_node_unadjusted(cx, expr, kind);
            } else {
                let kind = fixup_struct_types(cx, erasure_ctxt, expr, kind);
                return (kind, cx.typeck_results.expr_ty_adjusted(expr));
            }
        }
        ExprKind::Field(..) | ExprKind::AddrOf(..) => {
            if is_node_with_single_arg_erased(cx, &erasure_ctxt, &kind) {
                return erase_node_unadjusted(cx, expr, kind);
            } else {
                kind
            }
        }
        ExprKind::Unary(UnOp::Deref | UnOp::Neg, _) if !cx.typeck_results.is_method_call(expr) => {
            if is_node_with_single_arg_erased(cx, &erasure_ctxt, &kind) {
                return erase_node_unadjusted(cx, expr, kind);
            } else {
                kind
            }
        }
        ExprKind::Binary(_, _lhs, _rhs) => {
            if is_binary_node_with_any_arg_erased(cx, &erasure_ctxt, &kind) {
                return erase_node_unadjusted(cx, expr, kind);
            } else {
                kind
            }
        }
        _ => kind,
    };

    let ty = cx.typeck_results.expr_ty(expr);
    let kind = crate::verus_time_travel_prevention::expr_post(cx, expr, ty, kind);
    (kind, ty)
}

/// If we have a non-erased call which takes erased args, the types might be wrong.
/// e.g.:
/// proof fn f(ghost x: X)
/// Then a call `f(X{})` would get turned into `f(erased_ghost_value::<()>())`.
/// This would fail to type check because the arg has type ().
/// We can't just erase `f`, since it's a proof function,
/// so we "fix up" the function type instead.
fn fixup_call_types<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
) -> rustc_middle::thir::ExprKind<'tcx> {
    // TODO: reorg code so it doesn't look like this function is only time-travel-related
    crate::verus_time_travel_prevention::call_post(cx, expr, kind)
}

/// For structs, we turn the erased arguments back to their original expected types.
/// This needs a different solution to fix inhabitness issues.
fn fixup_struct_types<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    expr: &'tcx Expr<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
) -> rustc_middle::thir::ExprKind<'tcx> {
    let mut kind = kind;
    for field in kind.fields.iter_mut() {
        if is_erased(&cx.thir.exprs[field.expr].kind) {
            let expected_ty = kind.adt_def.variants()[kind.variant_idx].fields[field.name].ty(cx.tcx, kind.args);
            let e = erased_ghost_value(cx, erasure_ctxt, expr.hir_id, expr.span, expected_ty);
            field.expr = e;
        }
    }
    kind
}
