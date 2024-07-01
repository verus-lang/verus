use crate::ast::{BindX, Binder, BinderX, Expr, ExprX, Stmt, StmtX, Trigger};
use std::sync::Arc;

pub(crate) fn map_expr_visitor<F: FnMut(&Expr) -> Expr>(expr: &Expr, f: &mut F) -> Expr {
    match &**expr {
        ExprX::Const(_) => f(expr),
        ExprX::Var(_) => f(expr),
        ExprX::Old(_, _) => f(expr),
        ExprX::Apply(x, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f));
            }
            let expr = Arc::new(ExprX::Apply(x.clone(), Arc::new(exprs)));
            f(&expr)
        }
        ExprX::ApplyFun(t, e0, es) => {
            let expr0 = map_expr_visitor(e0, f);
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f));
            }
            let expr = Arc::new(ExprX::ApplyFun(t.clone(), expr0, Arc::new(exprs)));
            f(&expr)
        }
        ExprX::Unary(op, e1) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr = Arc::new(ExprX::Unary(*op, expr1));
            f(&expr)
        }
        ExprX::Binary(op, e1, e2) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr2 = map_expr_visitor(e2, f);
            let expr = Arc::new(ExprX::Binary(*op, expr1, expr2));
            f(&expr)
        }
        ExprX::Multi(op, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f));
            }
            let expr = Arc::new(ExprX::Multi(*op, Arc::new(exprs)));
            f(&expr)
        }
        ExprX::IfElse(e1, e2, e3) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr2 = map_expr_visitor(e2, f);
            let expr3 = map_expr_visitor(e3, f);
            let expr = Arc::new(ExprX::IfElse(expr1, expr2, expr3));
            f(&expr)
        }
        ExprX::Array(es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f));
            }
            let expr = Arc::new(ExprX::Array(Arc::new(exprs)));
            f(&expr)
        }
        ExprX::Bind(bind, e1) => {
            let bind = match &**bind {
                BindX::Let(bs) => {
                    let mut binders: Vec<Binder<Expr>> = Vec::new();
                    for b in bs.iter() {
                        let a = map_expr_visitor(&b.a, f);
                        binders.push(Arc::new(BinderX { name: b.name.clone(), a }));
                    }
                    BindX::Let(Arc::new(binders))
                }
                BindX::Quant(quant, binders, ts, qid) => {
                    let mut triggers: Vec<Trigger> = Vec::new();
                    for t in ts.iter() {
                        let mut exprs: Vec<Expr> = Vec::new();
                        for expr in t.iter() {
                            exprs.push(map_expr_visitor(expr, f));
                        }
                        triggers.push(Arc::new(exprs));
                    }
                    BindX::Quant(*quant, binders.clone(), Arc::new(triggers), qid.clone())
                }
                BindX::Lambda(binders, ts, qid) => {
                    let mut triggers: Vec<Trigger> = Vec::new();
                    for t in ts.iter() {
                        let mut exprs: Vec<Expr> = Vec::new();
                        for expr in t.iter() {
                            exprs.push(map_expr_visitor(expr, f));
                        }
                        triggers.push(Arc::new(exprs));
                    }
                    BindX::Lambda(binders.clone(), Arc::new(triggers), qid.clone())
                }
                BindX::Choose(binders, ts, qid, e2) => {
                    let mut triggers: Vec<Trigger> = Vec::new();
                    for t in ts.iter() {
                        let mut exprs: Vec<Expr> = Vec::new();
                        for expr in t.iter() {
                            exprs.push(map_expr_visitor(expr, f));
                        }
                        triggers.push(Arc::new(exprs));
                    }
                    let e2 = map_expr_visitor(e2, f);
                    BindX::Choose(binders.clone(), Arc::new(triggers), qid.clone(), e2)
                }
            };
            let e1 = map_expr_visitor(e1, f);
            let expr = Arc::new(ExprX::Bind(Arc::new(bind), e1));
            f(&expr)
        }
        ExprX::LabeledAssertion(aid, l, filter, e1) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr =
                Arc::new(ExprX::LabeledAssertion(aid.clone(), l.clone(), filter.clone(), expr1));
            f(&expr)
        }
        ExprX::LabeledAxiom(l, filter, e1) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr = Arc::new(ExprX::LabeledAxiom(l.clone(), filter.clone(), expr1));
            f(&expr)
        }
    }
}

pub(crate) fn map_stmt_expr_visitor<F: FnMut(&Expr) -> Expr>(stmt: &Stmt, f: &mut F) -> Stmt {
    match &**stmt {
        StmtX::Assume(e) => {
            let expr = map_expr_visitor(e, f);
            Arc::new(StmtX::Assume(f(&expr)))
        }
        StmtX::Assert(aid, span, filter, e) => {
            let expr = map_expr_visitor(e, f);
            Arc::new(StmtX::Assert(aid.clone(), span.clone(), filter.clone(), f(&expr)))
        }
        StmtX::Havoc(_) => stmt.clone(),
        StmtX::Assign(x, e) => {
            let expr = map_expr_visitor(e, f);
            Arc::new(StmtX::Assign(x.clone(), f(&expr)))
        }
        StmtX::Snapshot(_) => stmt.clone(),
        StmtX::DeadEnd(_) => stmt.clone(),
        StmtX::Breakable(..) => stmt.clone(),
        StmtX::Break(_) => stmt.clone(),
        StmtX::Block(_) => stmt.clone(),
        StmtX::Switch(_) => stmt.clone(),
    }
}

/*
pub(crate) fn map_stmt_visitor<F: FnMut(&Stmt) -> Stmt>(stmt: &Stmt, f: &mut F) -> Stmt {
    match &**stmt {
        StmtX::Assume(_) => f(stmt),
        StmtX::Assert(..) => f(stmt),
        StmtX::Havoc(_) => f(stmt),
        StmtX::Assign(_, _) => f(stmt),
        StmtX::Snapshot(_) => f(stmt),
        StmtX::Block(ss) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.push(map_stmt_visitor(s, f));
            }
            f(&Arc::new(StmtX::Block(Arc::new(stmts))))
        }
        StmtX::Switch(ss) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.push(map_stmt_visitor(s, f));
            }
            f(&Arc::new(StmtX::Switch(Arc::new(stmts))))
        }
    }
}
*/
