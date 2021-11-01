use crate::ast::{Arm, ArmX, Expr, ExprX, Stmt, StmtX, VirErr};
use crate::def::Spanned;
use crate::util::vec_map_result;
use std::sync::Arc;

pub(crate) fn map_expr_visitor_env<E, F, FS>(
    expr: &Expr,
    env: &mut E,
    f: &F,
    fs: &FS,
) -> Result<Expr, VirErr>
where
    F: Fn(&mut E, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &Stmt) -> Result<Vec<Stmt>, VirErr>,
{
    match &expr.x {
        ExprX::Const(_) => f(env, expr),
        ExprX::Var(_) => f(env, expr),
        ExprX::Call(x, typs, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor_env(e, env, f, fs)?);
            }
            let expr = expr.new_x(ExprX::Call(x.clone(), typs.clone(), Arc::new(exprs)));
            f(env, &expr)
        }
        ExprX::Ctor(path, ident, binders) => {
            let mapped_binders = binders
                .iter()
                .map(|b| b.map_result(|a| map_expr_visitor_env(a, env, f, fs)))
                .collect::<Result<Vec<_>, _>>()?;
            let expr =
                expr.new_x(ExprX::Ctor(path.clone(), ident.clone(), Arc::new(mapped_binders)));
            f(env, &expr)
        }
        ExprX::Unary(op, e1) => {
            let expr1 = map_expr_visitor_env(e1, env, f, fs)?;
            let expr = expr.new_x(ExprX::Unary(*op, expr1));
            f(env, &expr)
        }
        ExprX::UnaryOpr(op, e1) => {
            let expr1 = map_expr_visitor_env(e1, env, f, fs)?;
            let expr = expr.new_x(ExprX::UnaryOpr(op.clone(), expr1));
            f(env, &expr)
        }
        ExprX::Binary(op, e1, e2) => {
            let expr1 = map_expr_visitor_env(e1, env, f, fs)?;
            let expr2 = map_expr_visitor_env(e2, env, f, fs)?;
            let expr = expr.new_x(ExprX::Binary(*op, expr1, expr2));
            f(env, &expr)
        }
        ExprX::Quant(quant, binders, e1) => {
            let expr1 = map_expr_visitor_env(e1, env, f, fs)?;
            let expr = expr.new_x(ExprX::Quant(*quant, binders.clone(), expr1));
            f(env, &expr)
        }
        ExprX::Assign(e1, e2) => {
            let expr1 = map_expr_visitor_env(e1, env, f, fs)?;
            let expr2 = map_expr_visitor_env(e2, env, f, fs)?;
            let expr = expr.new_x(ExprX::Assign(expr1, expr2));
            f(env, &expr)
        }
        ExprX::Fuel(_, _) => f(env, &expr),
        ExprX::Header(_) => panic!("internal error: Header shouldn't exist here"),
        ExprX::Admit => f(env, &expr),
        ExprX::If(e1, e2, e3) => {
            let expr1 = map_expr_visitor_env(e1, env, f, fs)?;
            let expr2 = map_expr_visitor_env(e2, env, f, fs)?;
            let expr3 = e3.as_ref().map(|e| map_expr_visitor_env(e, env, f, fs)).transpose()?;
            let expr = expr.new_x(ExprX::If(expr1, expr2, expr3));
            f(env, &expr)
        }
        ExprX::Match(e1, arms) => {
            let expr1 = map_expr_visitor_env(e1, env, f, fs)?;
            let arms: Result<Vec<Arm>, VirErr> = vec_map_result(arms, |arm| {
                let pattern = arm.x.pattern.clone();
                let guard = map_expr_visitor_env(&arm.x.guard, env, f, fs)?;
                let body = map_expr_visitor_env(&arm.x.body, env, f, fs)?;
                Ok(Spanned::new(arm.span.clone(), ArmX { pattern, guard, body }))
            });
            let expr = expr.new_x(ExprX::Match(expr1, Arc::new(arms?)));
            f(env, &expr)
        }
        ExprX::While { cond, body, invs } => {
            let cond = map_expr_visitor_env(cond, env, f, fs)?;
            let body = map_expr_visitor_env(body, env, f, fs)?;
            let invs = Arc::new(vec_map_result(invs, |e| map_expr_visitor_env(e, env, f, fs))?);
            let expr = expr.new_x(ExprX::While { cond, body, invs });
            f(env, &expr)
        }
        ExprX::Block(ss, e1) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.append(&mut map_stmt_expr_visitor_env(s, env, f, fs)?);
            }
            let expr1 = match e1 {
                None => None,
                Some(e) => Some(map_expr_visitor_env(e, env, f, fs)?),
            };
            let expr = expr.new_x(ExprX::Block(Arc::new(stmts), expr1));
            f(env, &expr)
        }
    }
}

pub(crate) fn map_stmt_expr_visitor_env<E, F, FS>(
    stmt: &Stmt,
    env: &mut E,
    f: &F,
    fs: &FS,
) -> Result<Vec<Stmt>, VirErr>
where
    F: Fn(&mut E, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &Stmt) -> Result<Vec<Stmt>, VirErr>,
{
    match &stmt.x {
        StmtX::Expr(e) => {
            let expr = map_expr_visitor_env(e, env, f, fs)?;
            fs(env, &Spanned::new(stmt.span.clone(), StmtX::Expr(expr)))
        }
        StmtX::Decl { pattern, mode, init } => {
            let pattern = pattern.clone();
            let init = init.as_ref().map(|e| map_expr_visitor_env(e, env, f, fs)).transpose()?;
            let decl = StmtX::Decl { pattern, mode: *mode, init };
            fs(env, &Spanned::new(stmt.span.clone(), decl))
        }
    }
}

pub(crate) fn map_expr_visitor<F>(expr: &Expr, f: &mut F) -> Result<Expr, VirErr>
where
    F: FnMut(&Expr) -> Result<Expr, VirErr>,
{
    map_expr_visitor_env(expr, f, &|f, e| f(e), &|_, s| Ok(vec![s.clone()]))
}
