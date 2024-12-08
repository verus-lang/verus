mod check_expr;
mod check_ty;
mod unifier;

pub fn typecheck<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    expr: &rustc_hir::Expr,
    _expected_typ: &vir::ast::Typ,
) -> Result<vir::ast::Expr, vir::ast::VirErr>
{
    check_expr::check(tcx, expr);
    todo!();
}
