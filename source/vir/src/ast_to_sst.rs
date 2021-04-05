use crate::ast::{Expr, ExprX, Stmt, StmtX};
use crate::def::Spanned;
use crate::sst::{Exp, ExpX, Stm, StmX};
use crate::util::box_slice_map;
use std::rc::Rc;

fn expr_to_exp(expr: &Expr) -> Exp {
    match &expr.x {
        ExprX::Const(c) => Spanned::new(expr.span.clone(), ExpX::Const(c.clone())),
        ExprX::Var(x) => Spanned::new(expr.span.clone(), ExpX::Var(x.clone())),
        ExprX::Unary(op, expr) => {
            Spanned::new(expr.span.clone(), ExpX::Unary(*op, expr_to_exp(expr)))
        }
        ExprX::Binary(op, lhs, rhs) => {
            Spanned::new(expr.span.clone(), ExpX::Binary(*op, expr_to_exp(lhs), expr_to_exp(rhs)))
        }
        _ => {
            todo!()
        }
    }
}

pub fn expr_to_stm(expr: &Expr) -> Stm {
    match &expr.x {
        ExprX::Assume(expr) => Spanned::new(expr.span.clone(), StmX::Assume(expr_to_exp(expr))),
        ExprX::Assert(expr) => Spanned::new(expr.span.clone(), StmX::Assert(expr_to_exp(expr))),
        ExprX::Block(stmts) => {
            let stms = Rc::new(box_slice_map(stmts, stmt_to_stm));
            Spanned::new(expr.span.clone(), StmX::Block(stms))
        }
        _ => {
            todo!()
        }
    }
}

pub fn stmt_to_stm(stmt: &Stmt) -> Stm {
    match &stmt.x {
        StmtX::Expr(expr) => expr_to_stm(&expr),
    }
}
