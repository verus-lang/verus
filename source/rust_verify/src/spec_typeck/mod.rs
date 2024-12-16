#![allow(dead_code)]
#![allow(unused_imports)]

mod check_expr;
mod check_ty;
mod check_pat;
mod check_path;
mod unifier;
mod substitutions;
mod finalize_expr;

mod reverse_type_map;

mod method_probe;
//mod project;

pub struct State<'a, 'tcx> {
    scope_map: air::scope_map::ScopeMap<vir::ast::VarIdent, vir::ast::Typ>,
    param_name_to_param_ty: std::collections::HashMap<vir::ast::Ident, rustc_middle::ty::Ty<'tcx>>,
    unifier: unifier::Unifier,
    bctx: &'a crate::context::BodyCtxt<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    whole_span: rustc_span::Span,

    deferred_projection_obligations: Vec<(unifier::Alias, vir::ast::Typ)>,
}

pub fn typecheck<'tcx>(
    bctx: &crate::context::BodyCtxt<'tcx>,
    expr: &'tcx rustc_hir::Expr<'tcx>,
    expected_typ: &vir::ast::Typ,
) -> Result<vir::ast::Expr, vir::ast::VirErr>
{
    let mut state = State {
        scope_map: air::scope_map::ScopeMap::new(),
        unifier: unifier::Unifier::new(),
        param_name_to_param_ty: reverse_type_map::make_param_map(bctx),
        bctx: bctx,
        tcx: bctx.ctxt.tcx,
        whole_span: expr.span,
        deferred_projection_obligations: vec![],
    };

    let e = state.check_expr(expr)?;
    state.expect_allowing_coercion(&e.typ, expected_typ)?;

    state.finish_unification()?;

    let e = state.finalize_expr(&e)?;

    dbg!(e);

    // do substitutions
    // match exhaustiveness
    // int literal bounds checking
    // trait checks, impl paths, static resolutions

    // deprecated, visibility checks...?

    crate::util::err_span(expr.span, "done")
}
