use std::collections::HashMap;
use rustc_hir as hir;
use rustc_middle::thir::{Expr, ExprKind};
use hir::HirId;
use crate::thir::cx::Cx;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArg;
use rustc_middle::ty::TyKind;
use std::sync::{RwLock, Arc};

#[derive(Debug)]
pub enum VarErasure {
    Erase,
    Keep,
}

#[derive(Debug)]
pub enum CallErasure {
    Keep,
    EraseAll,
    EraseCallButNotArgs,
}

#[derive(Debug)]
pub struct VerusErasureCtxt {
    // For a given var (decl or use), should we erase it?
    pub vars: HashMap<HirId, VarErasure>,
    pub calls: HashMap<HirId, CallErasure>,
    pub erased_ghost_value_fn_def_id: DefId,
}

static VERUS_ERASURE_CTXT: RwLock<Option<Arc<VerusErasureCtxt>>> = RwLock::new(None);

pub fn set_verus_erasure_ctxt(erasure_ctxt: Arc<VerusErasureCtxt>) {
    let v: &mut Option<Arc<VerusErasureCtxt>> = &mut VERUS_ERASURE_CTXT.write().unwrap();
    if v.is_some() {
        panic!("VerusErasureCtxt has already been set");
    }
    *v = Some(erasure_ctxt);
}

fn get_verus_erasure_ctxt() -> Arc<VerusErasureCtxt> {
    VERUS_ERASURE_CTXT.read().unwrap().as_ref().expect("Expected VerusErasureCtxt for THIR modification pass").clone()
}

pub(crate) fn handle_var<'tcx>(
    cx: &mut Cx<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    var_hir_id: HirId
) -> Option<ExprKind<'tcx>> {
    let erasure_ctxt = get_verus_erasure_ctxt();

    if matches!(erasure_ctxt.vars.get(&expr.hir_id), None | Some(VarErasure::Keep)) {
        return None;
    }

    let typ = GenericArg::from(cx.typeck_results.expr_ty(expr));
    let args = cx.tcx.mk_args(&[typ]);
    let fn_def_id = erasure_ctxt.erased_ghost_value_fn_def_id;
    let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));

    let fun_expr_kind = ExprKind::ZstLiteral {
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
}
