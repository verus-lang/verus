//! Validates calls redirected by `hir_proof_with_rewrite` to the verified
//! counterparts of functions declared `#[verus_spec(with ..)]`.

use crate::attributes::{WITH_PREFIX, is_verified_counterpart};
use crate::util::err_span;
use rustc_hir::{Expr, ExprKind, QPath};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;
use vir::ast::VirErr;

/// Rejects redirected calls whose verified counterpart can differ from the method
/// selected by Rust for the compiled program.
///
/// This check runs for every call lowered to VIR. Unredirected calls return early
/// because their names lack [`WITH_PREFIX`].
pub(crate) fn check_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    types: &rustc_middle::ty::TypeckResults<'tcx>,
    expr: &Expr<'tcx>,
    resolved: DefId,
) -> Result<(), VirErr> {
    let Some(name) = call_form(types, expr) else {
        return Ok(());
    };
    let Some(name) = name.as_str().strip_prefix(WITH_PREFIX) else {
        return Ok(());
    };
    if !is_verified_counterpart(def_attrs(tcx, resolved)) {
        return err_span(
            expr.span,
            format!(
                "`{name}` does not accept extra ghost/tracked arguments: \
                 it is not declared with `#[verus_spec(with ..)]`"
            ),
        );
    }
    Ok(())
}
/// Returns the source-level method name of a call whose callee name resolution
/// leaves to type checking.
///
/// `hir_proof_with_rewrite` knows what a resolved path names and reports a callee
/// that takes no ghost/tracked arguments itself, so such a call is left out here,
/// where a name a user chose could not be told from a redirected one.
fn call_form<'tcx>(
    _types: &rustc_middle::ty::TypeckResults<'tcx>,
    expr: &Expr<'tcx>,
) -> Option<Symbol> {
    match &expr.kind {
        ExprKind::MethodCall(seg, ..) => Some(seg.ident.name),
        ExprKind::Call(callee, _) => match &callee.kind {
            ExprKind::Path(QPath::TypeRelative(_, seg)) => Some(seg.ident.name),
            _ => None,
        },
        _ => None,
    }
}

fn def_attrs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx [rustc_hir::Attribute] {
    match def_id.as_local() {
        Some(local) => tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
        None => tcx.attrs_for_def(def_id),
    }
}
