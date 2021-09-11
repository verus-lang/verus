use crate::ast::{Expr, ExprX, Stmt, StmtX, VirErr};
use crate::def::Spanned;
use crate::util::vec_map_result;
use std::sync::Arc;

pub(crate) fn map_expr_visitor<F>(expr: &Expr, f: &mut F) -> Result<Expr, VirErr>
where
    F: FnMut(&Expr) -> Result<Expr, VirErr>,
{
    match &expr.x {
        ExprX::Const(_) => f(expr),
        ExprX::Var(_) => f(expr),
        ExprX::Call(x, typs, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f)?);
            }
            let expr = expr.new_x(ExprX::Call(x.clone(), typs.clone(), Arc::new(exprs)));
            f(&expr)
        }
        ExprX::Ctor(path, ident, binders) => {
            let mapped_binders = binders
                .iter()
                .map(|b| b.map_result(|a| map_expr_visitor(a, f)))
                .collect::<Result<Vec<_>, _>>()?;
            let expr =
                expr.new_x(ExprX::Ctor(path.clone(), ident.clone(), Arc::new(mapped_binders)));
            f(&expr)
        }
        ExprX::Field { lhs, datatype, field_name } => {
            let lhs1 = map_expr_visitor(lhs, f)?;
            let expr = expr.new_x(ExprX::Field {
                lhs: lhs1,
                datatype: datatype.clone(),
                field_name: field_name.clone(),
            });
            f(&expr)
        }
        ExprX::Unary(op, e1) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr = expr.new_x(ExprX::Unary(*op, expr1));
            f(&expr)
        }
        ExprX::UnaryOpr(op, e1) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr = expr.new_x(ExprX::UnaryOpr(op.clone(), expr1));
            f(&expr)
        }
        ExprX::Binary(op, e1, e2) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr2 = map_expr_visitor(e2, f)?;
            let expr = expr.new_x(ExprX::Binary(*op, expr1, expr2));
            f(&expr)
        }
        ExprX::Quant(quant, binders, e1) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr = expr.new_x(ExprX::Quant(*quant, binders.clone(), expr1));
            f(&expr)
        }
        ExprX::Assign(e1, e2) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr2 = map_expr_visitor(e2, f)?;
            let expr = expr.new_x(ExprX::Assign(expr1, expr2));
            f(&expr)
        }
        ExprX::Fuel(_, _) => f(&expr),
        ExprX::Header(_) => panic!("internal error: Header shouldn't exist here"),
        ExprX::Admit => f(&expr),
        ExprX::If(e1, e2, e3) => {
            let expr1 = map_expr_visitor(e1, f)?;
            let expr2 = map_expr_visitor(e2, f)?;
            let expr3 = e3.as_ref().map(|e| map_expr_visitor(e, f)).transpose()?;
            let expr = expr.new_x(ExprX::If(expr1, expr2, expr3));
            f(&expr)
        }
        ExprX::While { cond, body, invs } => {
            let cond = map_expr_visitor(cond, f)?;
            let body = map_expr_visitor(body, f)?;
            let invs = Arc::new(vec_map_result(invs, |e| map_expr_visitor(e, f))?);
            let expr = expr.new_x(ExprX::While { cond, body, invs });
            f(&expr)
        }
        ExprX::Block(ss, e1) => {
            let mut exprs: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                exprs.push(map_stmt_expr_visitor(s, f)?);
            }
            let expr1 = match e1 {
                None => None,
                Some(e) => Some(map_expr_visitor(e, f)?),
            };
            let expr = expr.new_x(ExprX::Block(Arc::new(exprs), expr1));
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
        StmtX::Decl { param, mutable, init } => {
            let param = param.clone();
            let init = init.as_ref().map(|expr| f(expr)).transpose()?;
            Ok(Spanned::new(stmt.span.clone(), StmtX::Decl { param, mutable: *mutable, init }))
        }
    }
}
