#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]

use std::collections::HashMap;
use rustc_hir as hir;
use rustc_middle::thir::{Expr, ExprKind, ClosureExpr, TempLifetime, ExprId};
use hir::HirId;
use crate::thir::cx::ThirBuildCx;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::sync::{RwLock, Arc};
use rustc_middle::ty::{Ty, TyKind, GenericArg, CapturedPlace, Region, RegionKind};
use rustc_span::Span;

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
    pub dummy_capture_struct_def_id: DefId,
    pub dummy_capture_cons_fn_def_id: DefId,
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

pub(crate) fn handle_call<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> (bool, bool) {
    let erasure_ctxt = get_verus_erasure_ctxt();
    match erasure_ctxt.calls.get(&expr.hir_id) {
        None => (false, false),
        Some(CallErasure::Keep) => (false, false),
        Some(CallErasure::EraseAll) => (true, true),
        Some(CallErasure::EraseCallButNotArgs) => (false, true),
    }
}

pub(crate) fn handle_var<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    var_hir_id: HirId
) -> Option<ExprKind<'tcx>> {
    let erasure_ctxt = get_verus_erasure_ctxt();
    if matches!(erasure_ctxt.vars.get(&expr.hir_id), None | Some(VarErasure::Keep)) {
        return None;
    }
    let ty = cx.typeck_results.expr_ty(expr);
    Some(erased_ghost_value(cx, &erasure_ctxt, expr.hir_id, expr.span, ty))
}

pub(crate) fn fix_upvars<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    closure_expr: &'tcx hir::Expr<'tcx>,
    upvars: &Vec<ExprId>,
    tys: &'tcx [Ty<'tcx>],
) -> Vec<ExprId>
{
    let erasure_ctxt = get_verus_erasure_ctxt();

    if tys.len() == 0 {
        assert!(upvars.len() == 0);
        return vec![];
    }

    let upvar_dc_idx = get_upvar_dummy_capture_idx(cx, &erasure_ctxt, upvars);
    let ty_dc_idx = get_ty_dummy_capture_idx(&erasure_ctxt, tys);

    let mut new_dc_expr = upvars[upvar_dc_idx];
    for (i, upvar) in upvars.iter().enumerate() {
        if i != upvar_dc_idx {
            let kind = dummy_capture_cons(cx, &erasure_ctxt, closure_expr.hir_id, closure_expr.span, new_dc_expr, *upvar);

            let dc_ty = cx.thir.exprs[new_dc_expr].ty;

            let (temp_lifetime, backwards_incompatible) = cx
                .rvalue_scopes
                .temporary_scope(cx.region_scope_tree, closure_expr.hir_id.local_id);
            let e = Expr { temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible }, ty: dc_ty, span: closure_expr.span, kind };

            new_dc_expr = cx.thir.exprs.push(e);
        }
    }

    let mut res = vec![];

    for (i, ty) in tys.iter().enumerate() {
        if i == ty_dc_idx {
            res.push(new_dc_expr);
        } else {
            let kind = erased_ghost_value(cx, &erasure_ctxt, closure_expr.hir_id, closure_expr.span, *ty);

            let (temp_lifetime, backwards_incompatible) = cx
                .rvalue_scopes
                .temporary_scope(cx.region_scope_tree, closure_expr.hir_id.local_id);
            let e = Expr { temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible }, ty: *ty, span: closure_expr.span, kind };

            res.push(cx.thir.exprs.push(e));
        }
    }

    /*for ty in tys.iter() {
        let kind = erased_ghost_value(cx, &erasure_ctxt, closure_expr.hir_id, closure_expr.span, *ty);

        let (temp_lifetime, backwards_incompatible) = cx
            .rvalue_scopes
            .temporary_scope(cx.region_scope_tree, closure_expr.hir_id.local_id);
        let e = Expr { temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible }, ty: *ty, span: closure_expr.span, kind };

        res.push(cx.thir.exprs.push(e));
    }*/

    /*for (i, e) in cx.thir.exprs.iter().enumerate() {
        dbg!((i, e));
    }
    dbg!(upvars);
    dbg!(tys);
    dbg!(&res);*/

    res
}

fn get_upvar_dummy_capture_idx<'tcx>(
    cx: &ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    upvars: &Vec<ExprId>,
) -> usize {
    for i in 0 .. upvars.len() {
        match cx.thir.exprs[upvars[i]].ty.kind() {
            TyKind::Adt(adt_def, _) => {
                if adt_def.did() == erasure_ctxt.dummy_capture_struct_def_id {
                    return i;
                }
            }
            _ => { }
        }
    }
    panic!("MISSING DummyCapture (upvar)");
}

fn get_ty_dummy_capture_idx<'tcx>(
    erasure_ctxt: &VerusErasureCtxt,
    tys: &'tcx [Ty<'tcx>],
) -> usize {
    for i in 0 .. tys.len() {
        match tys[i].kind() {
            TyKind::Adt(adt_def, _) => {
                if adt_def.did() == erasure_ctxt.dummy_capture_struct_def_id {
                    return i;
                }
            }
            _ => { }
        }
    }
    panic!("MISSING DummyCapture (ty)");
}

/*
pub(crate) fn fix_upvars<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    closure_expr: &'tcx hir::Expr<'tcx>,
    upvars: &[ExprId],
) -> Box<[ExprId]> {
    let erasure_ctxt = get_verus_erasure_ctxt();

    let mut res = vec![];

    dbg!(upvars);

    for id in upvars.iter() {
        let ty = cx.thir.exprs[*id].ty;
        let kind = erased_ghost_value(cx, &erasure_ctxt, closure_expr.hir_id, closure_expr.span, ty);

        let (temp_lifetime, backwards_incompatible) = cx
            .rvalue_scopes
            .temporary_scope(cx.region_scope_tree, closure_expr.hir_id.local_id);
        let e = Expr { temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible }, ty, span: closure_expr.span, kind };

        res.push(cx.thir.exprs.push(e));
    }

    res.into_boxed_slice()
}
*/

fn dummy_capture_cons<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    dc_arg: ExprId,
    second_arg: ExprId,
) -> ExprKind<'tcx> {
    let lt = Region::new_from_kind(cx.tcx, RegionKind::ReErased);
    let lt_arg = GenericArg::from(lt);

    let ty = cx.thir.exprs[second_arg].ty;
    let ty_arg = GenericArg::from(ty);

    let args = cx.tcx.mk_args(&[lt_arg, ty_arg]);
    let fn_def_id = erasure_ctxt.dummy_capture_cons_fn_def_id;
    let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));

    let fun_expr_kind = ExprKind::ZstLiteral {
        user_ty: None,
    };
    let (temp_lifetime, backwards_incompatible) = cx
        .rvalue_scopes
        .temporary_scope(cx.region_scope_tree, hir_id.local_id);
    let fun_expr = Expr {
        temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible },
        ty: fn_ty,
        span: span,
        kind: fun_expr_kind,
    };

    ExprKind::Call {
        ty: fn_ty,
        fun: cx.thir.exprs.push(fun_expr),
        args: Box::new([dc_arg, second_arg]),
        from_hir_call: false,
        fn_span: span,
    }
}

pub(crate) fn erased_value<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> ExprKind<'tcx> {
    let erasure_ctxt = get_verus_erasure_ctxt();
    let ty = cx.typeck_results.expr_ty(expr);
    erased_ghost_value(cx, &erasure_ctxt, expr.hir_id, expr.span, ty)
}

/// Produce an expression `builtin::erased_ghost_value::<T>()`
fn erased_ghost_value<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    ty: Ty<'tcx>,
) -> ExprKind<'tcx> {
    let arg = GenericArg::from(ty);
    let args = cx.tcx.mk_args(&[arg]);
    let fn_def_id = erasure_ctxt.erased_ghost_value_fn_def_id;
    let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));

    let fun_expr_kind = ExprKind::ZstLiteral {
        user_ty: None,
    };
    let (temp_lifetime, backwards_incompatible) = cx
        .rvalue_scopes
        .temporary_scope(cx.region_scope_tree, hir_id.local_id);
    let fun_expr = Expr {
        temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible },
        ty: fn_ty,
        span: span,
        kind: fun_expr_kind,
    };

    ExprKind::Call {
        ty: fn_ty,
        fun: cx.thir.exprs.push(fun_expr),
        args: Box::new([]),
        from_hir_call: false,
        fn_span: span,
    }
}

/*
pub(crate) fn should_keep_upvar<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    closure_def_id: LocalDefId,
    captured_place: &'tcx CapturedPlace<'tcx>,
    upvar_ty: &Ty<'tcx>,
) -> bool {
    let (closure_body, _expr_id) = cx.tcx.thir_body(closure_def_id).unwrap();
    let closure_body_thir = closure_body.borrow();
    //dbg!(&closure_body_thir);
    /*
    for expr in closure_body_thir.exprs.iter() {
        if expr_matches_place(&expr, &captured_place.place) {
            return true;
        }
    }*/

    //false
    true
}
*/

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

/*
pub(crate) fn fix_closure<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
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
    */
    //dbg!(&cx.thir.exprs);
    //dbg!(&upvars);
    //dbg!(&fake_reads);

    //let (closure_body, _expr_id) = cx.tcx.thir_body(closure_id).unwrap();
    //let closure_body = closure_body.borrow();
    //dbg!(closure_body);

    /*
    for e in closure_body.iter() {
        
    }
    let filtered_upvars = upvars.iter().filter(|upv| is_upvar_actually_used(upv, closure_body)*/

    ClosureExpr { closure_id, args, upvars, movability, fake_reads }
}
*/

pub(crate) fn get_closure_captures_accounting_for_ghost<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    closure_expr: &'tcx hir::Expr<'tcx>,
    closure_def_id: LocalDefId,
) ->
(&'tcx rustc_middle::ty::List<&'tcx CapturedPlace<'tcx>>,
Vec<Ty<'tcx>>,
Vec<(rustc_middle::hir::place::Place<'tcx>, rustc_middle::mir::FakeReadCause, HirId)>)
{
    let tcx = cx.tcx;

    let mut fn_ctxt = crate::upvar::FnCtxt {
        ph: std::marker::PhantomData,
        tcx,
        param_env: cx.typing_env,
        closure_def_id,
        typeck_results: cx.typeck_results,
        fake_reads: vec![],
        closure_min_captures: Some(Default::default()),
        upvar_tys: vec![],
    };

    let hir::ExprKind::Closure(hir::Closure { body: body_id, capture_clause, .. }) = &closure_expr.kind else {
        unreachable!()
    };

    let body = tcx.hir_body(*body_id);

    fn_ctxt.analyze_closure(closure_expr.hir_id, closure_expr.span, *body_id, body, *capture_clause);
    //(fn_ctxt.closure_min_captures.unwrap(), fn_ctxt.fake_reads)

    let closure_min_captures = fn_ctxt.closure_min_captures;

    //let closure_min_captures = Box::leak(Box::new(closure_min_captures));

    let closure_min_captures = closure_min_captures.unwrap();
    let closure_min_captures = Box::leak(Box::new(closure_min_captures));
    let closure_min_captures = closure_min_captures.values().flat_map(|v| v.iter());

    let captures = tcx.mk_captures_from_iter(closure_min_captures);

    (captures, fn_ctxt.upvar_tys, fn_ctxt.fake_reads)
}

pub(crate) fn skip_var_for_closure_capturing<'tcx>(
    hir_id: HirId
) -> bool {
    let erasure_ctxt = get_verus_erasure_ctxt();
    matches!(erasure_ctxt.vars.get(&hir_id), Some(VarErasure::Erase))
}
