#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

pub fn typecheck<'tcx>(
    _tcx: rustc_middle::ty::TyCtxt<'tcx>,
    _expr: &rustc_hir::Expr,
    _expected_typ: &vir::ast::Typ,
) -> Result<vir::ast::Expr, vir::ast::VirErr>
{
    todo!();
}
