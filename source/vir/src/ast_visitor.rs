use crate::ast::{Expr, ExprX, Stmt, StmtX, VirErr};
use crate::def::Spanned;
use std::rc::Rc;

pub(crate) fn map_expr_visitor<F>(expr: &Expr, f: &mut F) -> Result<Expr, VirErr>
where
    F: FnMut(&Expr) -> Result<Expr, VirErr>,
{
    match &expr.x {
        ExprX::Const(_) => f(expr),
        ExprX::Var(_) => f(expr),
        ExprX::Call(x, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f)?);
            }
            let expr = Spanned::new(expr.span.clone(), ExprX::Call(x.clone(), Rc::new(exprs)));
            f(&expr)
        }
        ExprX::Assume(e1) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr = Spanned::new(expr.span.clone(), ExprX::Assume(expr1));
            f(&expr)
        }
        ExprX::Assert(e1) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr = Spanned::new(expr.span.clone(), ExprX::Assert(expr1));
            f(&expr)
        }
        ExprX::Unary(op, e1) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr = Spanned::new(expr.span.clone(), ExprX::Unary(*op, expr1));
            f(&expr)
        }
        ExprX::Binary(op, e1, e2) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr2 = map_expr_visitor(e2, f)?;
            let expr = Spanned::new(expr.span.clone(), ExprX::Binary(*op, expr1, expr2));
            f(&expr)
        }
        ExprX::Assign(e1, e2) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr2 = map_expr_visitor(e2, f)?;
            let expr = Spanned::new(expr.span.clone(), ExprX::Assign(expr1, expr2));
            f(&expr)
        }
        ExprX::Fuel(_, _) => f(&expr),
        ExprX::Block(ss, e1) => {
            let mut exprs: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                exprs.push(map_stmt_expr_visitor(s, f)?);
            }
            let expr1 = match e1 {
                None => None,
                Some(e) => Some(map_expr_visitor(e, f)?),
            };
            let expr = Spanned::new(expr.span.clone(), ExprX::Block(Rc::new(exprs), expr1));
            f(&expr)
        }
    }
}

pub(crate) fn map_stmt_expr_visitor<F>(stmt: &Stmt, f: &mut F) -> Result<Stmt, VirErr>
where
    F: FnMut(&Expr) -> Result<Expr, VirErr>,
{
    match &stmt.x {
        StmtX::Expr(e) => {
            let expr = map_expr_visitor(e, f)?;
            Ok(Spanned::new(stmt.span.clone(), StmtX::Expr(f(&expr)?)))
        }
        StmtX::Decl { .. } => Ok(stmt.clone()),
    }
}
