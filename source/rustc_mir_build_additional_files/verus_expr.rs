use crate::thir::cx::ThirBuildCx;
use crate::verus::CallErasure;
use crate::verus::{
    erase_node, erase_node_unadjusted, erase_tree_kind, handle_call, is_node_with_single_arg_erased,
};
use rustc_hir::{Expr, ExprKind, UnOp};
use rustc_middle::ty::adjustment::{Adjust, Adjustment, AutoBorrow};

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

    match adjustment.kind {
        Adjust::Deref(None | Some(_)) | Adjust::Borrow(AutoBorrow::Ref(_)) => {
            // Adjust::Deref(None) -> implicit *
            // Adjust::Borrow(AutoBorrow::Ref(_)) -> implicit &
            // Adjust::Deref(Some(_)) -> This case means inserting a Deref::deref function.
            //   In spec code that would usually be an error, except for some cases
            //   like Arc or Rc where we ignore the deref in spec code.
            //   In all those cases we also want to erase.
            if is_node_with_single_arg_erased(cx, &erasure_ctxt, &kind) {
                erase_node(cx, expr, adjustment.target, kind)
            } else {
                kind
            }
        }
        _ => kind,
    }
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
                CallErasure::EraseTree => Some(erase_tree_kind(cx, expr)),
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

    match expr.kind {
        ExprKind::MethodCall(..) | ExprKind::Call(..) | ExprKind::Struct(..) => {
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
            if call_erasure.should_erase() { erase_node_unadjusted(cx, expr, kind) } else { kind }
        }
        ExprKind::Field(..) | ExprKind::AddrOf(..) => {
            if is_node_with_single_arg_erased(cx, &erasure_ctxt, &kind) {
                erase_node_unadjusted(cx, expr, kind)
            } else {
                kind
            }
        }
        ExprKind::Unary(UnOp::Deref, _) if !cx.typeck_results.is_method_call(expr) => {
            if is_node_with_single_arg_erased(cx, &erasure_ctxt, &kind) {
                erase_node_unadjusted(cx, expr, kind)
            } else {
                kind
            }
        }
        _ => kind,
    }
}
