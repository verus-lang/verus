#![allow(dead_code)]
#![allow(unused_imports)]

mod unification_table;
mod constraints;
mod reduce_projection;
mod substitutions;
mod reverse_type_map;

mod method_probe;

mod check_expr;
mod check_special_calls;
mod check_ty;
mod check_pat;
mod check_ctors;
mod check_closures;
mod check_path;

mod finalize_expr;

// See README for explanation

pub struct State<'a, 'tcx> {
    param_name_to_param_ty: std::collections::HashMap<vir::ast::Ident, rustc_middle::ty::Term<'tcx>>,
    bctx: &'a crate::context::BodyCtxt<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    whole_span: rustc_span::Span,

    // Stateful context throughout the first past
    scope_map: air::scope_map::ScopeMap<vir::ast::VarIdent, vir::ast::Typ>,
    unifier: unification_table::UnificationTable<constraints::Entry>,

    // Obligations collected in the first pass to be discharged at the end
    deferred_projection_obligations: Vec<(constraints::Projection, vir::ast::Typ)>,

    any_error_found: bool,
}

pub fn typecheck<'tcx>(
    bctx: &crate::context::BodyCtxt<'tcx>,
    expr: &'tcx rustc_hir::Expr<'tcx>,
    expected_typ: &vir::ast::Typ,
) -> Result<vir::ast::Expr, vir::ast::VirErr>
{
    let mut state = State {
        scope_map: bctx.scope_map.borrow().clone(),
        unifier: unification_table::UnificationTable::new(),
        param_name_to_param_ty: reverse_type_map::make_param_map(bctx),
        param_env: bctx.ctxt.tcx.param_env(bctx.fun_id),
        bctx: bctx,
        tcx: bctx.ctxt.tcx,
        whole_span: expr.span,
        deferred_projection_obligations: vec![],
        any_error_found: false,
    };

    let e = state.check_expr(expr)?;
    state.expect_allowing_coercion(&e.typ, expected_typ)?;

    state.finish_unification()?;

    if state.any_error_found {
        return crate::util::err_span(expr.span, "found error");
    }

    let e = state.finalize_expr(&e)?;

    if state.any_error_found {
        return crate::util::err_span(expr.span, "found error");
    }

    Ok(e)

    //dbg!(e);

    // do substitutions
    // match exhaustiveness
    // int literal bounds checking
    // trait checks, impl paths, static resolutions

    // deprecated, visibility checks...?
}
