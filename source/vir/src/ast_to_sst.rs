use crate::ast::{BinaryOp, Expr, ExprX, Ident, Mode, Stmt, StmtX, VirErr};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Exp, ExpX, Stm, StmX};
use crate::util::vec_map_result;
use std::rc::Rc;

pub(crate) fn expr_to_exp(ctx: &Ctx, expr: &Expr) -> Result<Exp, VirErr> {
    match &expr.x {
        ExprX::Const(c) => Ok(Spanned::new(expr.span.clone(), ExpX::Const(c.clone()))),
        ExprX::Var(x) => Ok(Spanned::new(expr.span.clone(), ExpX::Var(x.clone()))),
        ExprX::Call(x, args) => {
            match ctx.func_map.get(x) {
                None => {
                    return Err(Spanned::new(
                        expr.span.clone(),
                        format!("could not find function {}", &x),
                    ));
                }
                Some(fun) => match fun.x.mode {
                    Mode::Spec => {}
                    _ => {
                        unimplemented!("call to non-spec function {} {:?}", &x, expr.span)
                    }
                },
            }
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Spanned::new(expr.span.clone(), ExpX::Call(x.clone(), Rc::new(exps))))
        }
        ExprX::Unary(op, expr) => {
            Ok(Spanned::new(expr.span.clone(), ExpX::Unary(*op, expr_to_exp(ctx, expr)?)))
        }
        ExprX::Binary(op, lhs, rhs) => {
            let bin = ExpX::Binary(*op, expr_to_exp(ctx, lhs)?, expr_to_exp(ctx, rhs)?);
            Ok(Spanned::new(expr.span.clone(), bin))
        }
        ExprX::Block(stmts, Some(expr)) if stmts.len() == 0 => expr_to_exp(ctx, expr),
        ExprX::Field(lhs, name) => {
            Ok(Spanned::new(expr.span.clone(), ExpX::Field(expr_to_exp(ctx, lhs)?, name.clone())))
        }
        _ => {
            todo!("{:?}", expr)
        }
    }
}

pub fn expr_to_stm(ctx: &Ctx, expr: &Expr, dest: &Option<Ident>) -> Result<Stm, VirErr> {
    match &expr.x {
        ExprX::Call(x, args) => {
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Spanned::new(expr.span.clone(), StmX::Call(x.clone(), Rc::new(exps))))
        }
        ExprX::Assume(expr) => {
            Ok(Spanned::new(expr.span.clone(), StmX::Assume(expr_to_exp(ctx, expr)?)))
        }
        ExprX::Assert(expr) => {
            Ok(Spanned::new(expr.span.clone(), StmX::Assert(expr_to_exp(ctx, expr)?)))
        }
        ExprX::Assign(lhs, rhs) => Ok(Spanned::new(
            expr.span.clone(),
            StmX::Assign(expr_to_exp(ctx, lhs)?, expr_to_exp(ctx, rhs)?),
        )),
        ExprX::Fuel(x, fuel) => Ok(Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel))),
        ExprX::Block(stmts, expr_opt) => {
            let mut stms = vec_map_result(stmts, |s| stmt_to_stm(ctx, s))?;
            match (dest, expr_opt) {
                (None, None) => {}
                (Some(dest), Some(expr)) => {
                    let _ = expr_to_exp(ctx, expr);
                    let x_dest = Spanned::new(expr.span.clone(), ExpX::Var(dest.clone()));
                    let eq = ExpX::Binary(BinaryOp::Eq, x_dest, expr_to_exp(ctx, expr)?);
                    let assign = StmX::Assume(Spanned::new(expr.span.clone(), eq));
                    stms.push(Spanned::new(expr.span.clone(), assign));
                }
                _ => panic!("internal error: ExprX::Block {}", expr.span.as_string),
            }
            Ok(Spanned::new(expr.span.clone(), StmX::Block(Rc::new(stms))))
        }
        _ => {
            todo!("{}", expr.span.as_string)
        }
    }
}

pub fn stmt_to_stm(ctx: &Ctx, stmt: &Stmt) -> Result<Stm, VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => expr_to_stm(ctx, &expr, &None),
        StmtX::Decl { param, mutable } => Ok(Spanned::new(
            stmt.span.clone(),
            StmX::Decl { ident: param.name.clone(), typ: param.typ.clone(), mutable: *mutable },
        )),
    }
}
