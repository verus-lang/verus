use air::scope_map::ScopeMap;
use ast_visitor::VisitorControlFlow;

use crate::{
    ast::{FunctionX, Krate, Mode, VirErr},
    ast_visitor::{self, expr_visitor_dfs},
    context::Ctx,
    scc::Graph, messages::error,
};

pub fn alternation_check(ctx: &Ctx, krate: &Krate) -> Result<(), VirErr> {
    // let alternation_graph = Graph::new();
    for f in krate.functions.iter().filter(|f| f.x.mode == Mode::Proof) {
        let FunctionX { require, ensure, decrease, body, broadcast_forall, attrs, .. } = &f.x;
        let Some(body) = body else { return Ok(()) };
        for expr in ensure.iter() {
            use crate::ast::ExprX::*;
            expr_visitor_dfs::<VirErr, _>(expr, &mut ScopeMap::new(), &mut |scope_map, expr| match &expr.x {
                Call(_, _) => todo!(),
                Unary(_, _) => todo!(),
                UnaryOpr(_, _) => todo!(),
                Binary(_, _, _) => todo!(),
                BinaryOpr(_, _, _) => todo!(),
                Quant(_, _, _) => todo!(),
                Closure(_, _) => todo!(),
                Choose { params, cond, body } => todo!(),

                Loc(..) |
                Tuple(..) |
                Ctor(..) |
                Multi(..) |
                WithTriggers { .. } |
                Assign { .. } |
                AssertAssume { .. } |
                If(..) |
                Match(..) |
                Loop { .. } |
                Return(..) |
                Ghost { .. } |
                Block(..) => VisitorControlFlow::Recurse,

                Const(_) |
                Var(_) |
                VarLoc(_) |
                VarAt(_, _) |
                ConstVar(_, _) |
                StaticVar(_) |
                Fuel(_, _) |
                Header(_) |
                BreakOrContinue { .. } => VisitorControlFlow::Return,

                NullaryOpr(..) |
                ExecClosure { .. } |
                AssertBy { .. } |
                AssertQuery { .. } |
                AssertCompute(..) |
                RevealString(..) |
                OpenInvariant(..) => VisitorControlFlow::Stop(error(&expr.span, "unsupported in EPR fragment")),
            });
        }
    }
    Ok(())
}
