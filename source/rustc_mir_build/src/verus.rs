#![allow(unused_variables)]
use std::collections::HashMap;
use rustc_hir as hir;
use rustc_middle::thir::{Expr, ExprKind, ClosureExpr};
use hir::HirId;
use crate::thir::cx::Cx;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::sync::{RwLock, Arc};
use rustc_middle::ty::{Ty, TyKind, GenericArg, CapturedPlace};

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
    return None;
    /*
    let erasure_ctxt = get_verus_erasure_ctxt();

    if matches!(erasure_ctxt.vars.get(&expr.hir_id), None | Some(VarErasure::Keep)) {
        return None;
    }

    let ty = cx.typeck_results.expr_ty(expr);
    Some(erased_ghost_value(cx, &erasure_ctxt, expr, ty))
    */
}

/// Produce an expression `builtin::erased_ghost_value::<T>()`
fn erased_ghost_value<'tcx>(
    cx: &mut Cx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    expr: &'tcx hir::Expr<'tcx>,
    ty: Ty<'tcx>,
) -> ExprKind<'tcx> {
    let arg = GenericArg::from(ty);
    let args = cx.tcx.mk_args(&[arg]);
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

    ExprKind::Call {
        ty: fn_ty,
        fun: cx.thir.exprs.push(fun_expr),
        args: Box::new([]),
        from_hir_call: false,
        fn_span: expr.span,
    }
}

pub(crate) fn should_keep_upvar<'tcx>(
    cx: &mut Cx<'tcx>,
    closure_def_id: LocalDefId,
    captured_place: &'tcx CapturedPlace<'tcx>,
    upvar_ty: &Ty<'tcx>,
) -> bool {
    let (closure_body, _expr_id) = cx.tcx.thir_body(closure_def_id).unwrap();
    let closure_body_thir = closure_body.borrow();
    dbg!(&closure_body_thir);
    /*
    for expr in closure_body_thir.exprs.iter() {
        if expr_matches_place(&expr, &captured_place.place) {
            return true;
        }
    }*/

    false
}

/*
fn expr_matches_place(thir_body: &Thir, expr: &Expr, place: &Place) -> bool {
    let mut i = place.projections.len();
    let mut expr = expr;
    while i > 0 {
        if let Some(expr_id) = expr_matches_projection(expr, &place.projections[i-1]) {
            expr = &thir_body.exprs[expr_id];
            i -= 1;
        } else {
            return false;
        }
    }
    expr_matches_place_base(expr, &place.base)
}

fn expr_matches_projection(expr: &Expr, projection: &Projection) {
    match &projection.kind {
        ProjectionKind::Field(field_idx, variant_idx) => {
            
        }
        _ => {
            panic!("unexpected ProjectionKind");
        }
    }
}
*/

pub(crate) fn fix_closure<'tcx>(
    cx: &mut Cx<'tcx>,
    closure_expr: ClosureExpr<'tcx>
) -> ClosureExpr<'tcx> {
    //dbg!(&cx.thir);
    //dbg!(&closure_expr);
    let ClosureExpr { closure_id, args, upvars, movability, fake_reads } = closure_expr;

    let def_id = closure_expr.closure_id;
    /*for (hir_id, cl) in self.typeck_results.closure_min_captures[&def_id].iter() {
        dbg!(&hir_id);
        dbg!(&cl);
    }
    for cf in self.typeck_results.closure_min_captures_flattened(def_id) {
        dbg!(&cf);
    }
    dbg!(&upvars);
    dbg!(&fake_reads);*/

    let (closure_body, _expr_id) = cx.tcx.thir_body(closure_id).unwrap();
    let closure_body = closure_body.borrow();
    //dbg!(closure_body);

    /*
    for e in closure_body.iter() {
        
    }

    let filtered_upvars = upvars.iter().filter(|upv| is_upvar_actually_used(upv, closure_body)*/

    ClosureExpr { closure_id, args, upvars, movability, fake_reads: vec![] }
}
