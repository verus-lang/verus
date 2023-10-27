use air::scope_map::ScopeMap;

use crate::{
    ast::{FunctionX, Krate, Mode, VirErr},
    ast_visitor::{self, expr_visitor_dfs},
    context::Ctx,
    scc::Graph,
};

pub fn alternation_check(ctx: &Ctx, krate: &Krate) -> Result<(), VirErr> {
    // let alternation_graph = Graph::new();
    for f in krate.functions.iter().filter(|f| f.x.mode == Mode::Proof) {
        let FunctionX { require, ensure, decrease, body, broadcast_forall, attrs, .. } = &f.x;
        let Some(body) = body else { return Ok(()) };
        for expr in ensure.iter() {
            expr_visitor_dfs(expr, &mut ScopeMap::new(), &mut |scope_map, expr| match expr.x {
                crate::ast::ExprX::Call(_, _) => todo!(),
                crate::ast::ExprX::Unary(_, _) => todo!(),
                crate::ast::ExprX::Binary(_, _, _) => todo!(),
                crate::ast::ExprX::BinaryOpr(_, _, _) => todo!(),
                crate::ast::ExprX::Quant(_, _, _) => todo!(),
                crate::ast::ExprX::Closure(_, _) => todo!(),
                crate::ast::ExprX::Choose { params, cond, body } => todo!(),
            });
        }
    }
    Ok(())
}
