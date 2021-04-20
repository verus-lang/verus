use crate::ast::{Expr, ExprX, Mode, Stmt, StmtX, VirErr};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Exp, ExpX, Stm, StmX};
use crate::util::box_slice_map_result;
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
            let exps = box_slice_map_result(args, |e| expr_to_exp(ctx, e))?;
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
        _ => {
            todo!("{:?}", expr)
        }
    }
}

pub fn expr_to_stm(ctx: &Ctx, expr: &Expr) -> Result<Stm, VirErr> {
    match &expr.x {
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
        ExprX::Block(stmts, None) => {
            let stms = Rc::new(box_slice_map_result(stmts, |s| stmt_to_stm(ctx, s))?);
            Ok(Spanned::new(expr.span.clone(), StmX::Block(stms)))
        }
        _ => {
            todo!()
        }
    }
}

pub fn stmt_to_stm(ctx: &Ctx, stmt: &Stmt) -> Result<Stm, VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => expr_to_stm(ctx, &expr),
        StmtX::Decl { param, mutable } => Ok(Spanned::new(
            stmt.span.clone(),
            StmX::Decl { ident: param.name.clone(), typ: param.typ, mutable: *mutable },
        )),
    }
}
