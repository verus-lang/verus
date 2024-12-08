mod check_expr;
mod check_ty;
mod unifier;

pub struct State<'tcx> {
    scope_map: air::scope_map::ScopeMap<vir::ast::VarIdent, vir::ast::Typ>,
    unifier: unifier::Unifier,
    bctx: crate::context::BodyCtxt<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
}

pub fn typecheck<'tcx>(
    bctx: crate::context::BodyCtxt<'tcx>,
    expr: &rustc_hir::Expr,
    expected_typ: &vir::ast::Typ,
) -> Result<vir::ast::Expr, vir::ast::VirErr>
{
    let state = State {
        scope_map: air::scope_map::ScopeMap::new(),
        unifier: unifier::Unifier::new(),
        bctx: bctx,
        tcx: bctx.ctxt.tcx,
    };

    let e = state.check_expr(expr);
    state.unifier.expect(&e.typ, expected_typ);

    todo!();
}
