use super::State;
use vir::ast::{Expr, VirErr, Stmt, Typ, SpannedTyped, TypX};
use air::scope_map::ScopeMap;

impl State<'_, '_> {
    pub fn finalize_expr(&mut self, expr: &Expr) -> Result<Expr, VirErr> {
        vir::ast_visitor::map_expr_visitor_env(expr, &mut ScopeMap::new(), self,
            &|state: &mut Self, _, e: &Expr| state.finalize_one_expr(e),
            &|_, _, s: &Stmt| Ok(vec![s.clone()]),
            &|state, t: &Typ| state.finalize_one_typ(t)
        )
    }

    fn finalize_one_typ(&mut self, t: &Typ) -> Result<Typ, VirErr> {
        Ok(match &**t {
            TypX::UnificationVar(_) => self.get_finished_typ(t),
            _ => t.clone(),
        })
    }

    fn finalize_one_expr(&mut self, e: &Expr) -> Result<Expr, VirErr> {
        Ok(e.clone())
    }
}
