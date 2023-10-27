use air::scope_map::ScopeMap;
use ast_visitor::VisitorControlFlow;

use crate::{
    ast::{FunctionX, Krate, Mode, VirErr, Expr},
    ast_visitor::{self, expr_visitor_dfs},
    context::Ctx,
    scc::Graph, messages::error,
};

pub fn alternation_check(ctx: &Ctx, krate: &Krate, /* TODO: &mut graph ? */) -> Result<(), VirErr> {
    fn build_graph_visit(ctx: &Ctx, expr: &Expr) -> Result<(), VirErr> {
        use crate::ast::ExprX::*;
        expr_visitor_dfs::<VirErr, _>(expr, &mut ScopeMap::new(), &mut |scope_map, expr| match &expr.x {
            Call(target, _) => match target {
                crate::ast::CallTarget::Fun(call_target_kind, fun, _, impl_paths, _) => {
                    if impl_paths.len() > 0 {
                        VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
                    } else {
                        if let Some(fun) = (match call_target_kind {
                            crate::ast::CallTargetKind::Static => Some(fun),
                            crate::ast::CallTargetKind::Method(Some((fun, _, impl_paths))) => {
                                if impl_paths.len() > 0 {
                                    None
                                } else {
                                    Some(fun)
                                }
                            }
                            crate::ast::CallTargetKind::Method(None) => None,
                        }) {
                            let f = &ctx.func_map[fun];
                            if let Some(f_body) = &f.x.body {
                                match build_graph_visit(ctx, f_body) {
                                    Ok(_) => VisitorControlFlow::Return,
                                    Err(err) => VisitorControlFlow::Stop(err),
                                }
                            } else {
                                VisitorControlFlow::Return
                            }
                        } else {
                            VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
                        }
                    }
                }
                crate::ast::CallTarget::FnSpec(_) |
                crate::ast::CallTarget::BuiltinSpecFun(_, _) => VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
            }
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
        Ok(())
    }
    // let alternation_graph = Graph::new();
    for f in krate.functions.iter().filter(|f| f.x.mode == Mode::Proof) {
        let FunctionX { require, ensure, decrease, body, broadcast_forall, attrs, .. } = &f.x;
        let Some(body) = body else { return Ok(()) };
        for expr in ensure.iter() {
            build_graph_visit(ctx, expr);
        }
    }
    Ok(())
}
