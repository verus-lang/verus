use std::collections::HashMap;
use rustc_hir as hir;
use rustc_middle::thir::{Expr, ExprKind};
use hir::HirId;
use crate::thir::cx::Cx;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArg;
use rustc_middle::ty::TyKind;

pub enum VarErase {
    Erase,
    Keep,
}

pub enum CallErase {
    Keep,
    EraseAll,
    EraseCallButNotArgs,
}

pub struct VerusCtxt {
    // For a given var (decl or use), should we erase it?
    pub vars: HashMap<HirId, VarErase>,
    pub calls: HashMap<HirId, CallErase>,
    pub arbitrary_fn_def_id: DefId,
}

fn with_verus_ctxt<R>(_f: impl FnOnce(&VerusCtxt) -> R) -> R {
    todo!();
}

pub(crate) fn handle_var<'tcx>(
    cx: &mut Cx<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    var_hir_id: HirId
) -> Option<ExprKind<'tcx>> {
    with_verus_ctxt(|verus_ctxt| {
        if matches!(verus_ctxt.vars[&var_hir_id], VarErase::Keep) {
            return None;
        }

        let typ = GenericArg::from(cx.typeck_results.expr_ty(expr));
        let args = cx.tcx.mk_args(&[typ]);
        let fn_def_id = verus_ctxt.arbitrary_fn_def_id;
        let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));

        let fun_expr_kind = ExprKind::NamedConst {
            def_id: fn_def_id,
            args,
            user_ty: None,
        };
        let temp_lifetime = cx
            .rvalue_scopes
            .temporary_scope(cx.region_scope_tree, expr.hir_id.local_id);
        let fun_expr = Expr {
            temp_lifetime,
            ty: fn_ty,
            span: expr.span,
            kind: fun_expr_kind,
        };

        Some(ExprKind::Call {
            ty: fn_ty,
            fun: cx.thir.exprs.push(fun_expr),
            args: Box::new([]),
            from_hir_call: false,
            fn_span: expr.span,
        })
    })
}
