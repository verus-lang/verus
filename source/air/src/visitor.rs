use crate::ast::{BindX, Binder, BinderX, Expr, ExprX, Stmt, StmtX, Trigger};
use std::rc::Rc;

pub(crate) fn map_expr_visitor<F: FnMut(&Expr) -> Expr>(expr: &Expr, f: &mut F) -> Expr {
    match &**expr {
        ExprX::Const(_) => f(expr),
        ExprX::Var(_) => f(expr),
        ExprX::Apply(x, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f));
            }
            let expr = Rc::new(ExprX::Apply(x.clone(), Rc::new(exprs.into_boxed_slice())));
            f(&expr)
        }
        ExprX::Unary(op, e1) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr = Rc::new(ExprX::Unary(*op, expr1));
            f(&expr)
        }
        ExprX::Binary(op, e1, e2) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr2 = map_expr_visitor(e2, f);
            let expr = Rc::new(ExprX::Binary(*op, expr1, expr2));
            f(&expr)
        }
        ExprX::Multi(op, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor(e, f));
            }
            let expr = Rc::new(ExprX::Multi(*op, Rc::new(exprs.into_boxed_slice())));
            f(&expr)
        }
        ExprX::Bind(bind, e1) => {
            let bind = match &**bind {
                BindX::Let(bs) => {
                    let mut binders: Vec<Binder<Expr>> = Vec::new();
                    for b in bs.iter() {
                        let a = map_expr_visitor(&b.a, f);
                        binders.push(Rc::new(BinderX { name: b.name.clone(), a }));
                    }
                    BindX::Let(Rc::new(binders.into_boxed_slice()))
                }
                BindX::Quant(quant, binders, ts) => {
                    let mut triggers: Vec<Trigger> = Vec::new();
                    for t in ts.iter() {
                        let mut exprs: Vec<Expr> = Vec::new();
                        for expr in t.iter() {
                            exprs.push(map_expr_visitor(expr, f));
                        }
                        triggers.push(Rc::new(exprs.into_boxed_slice()));
                    }
                    BindX::Quant(*quant, binders.clone(), Rc::new(triggers.into_boxed_slice()))
                }
            };
            let e1 = map_expr_visitor(e1, f);
            let expr = Rc::new(ExprX::Bind(Rc::new(bind), e1));
            f(&expr)
        }
        ExprX::LabeledAssertion(span, e1) => {
            let expr1 = map_expr_visitor(e1, f);
            let expr = Rc::new(ExprX::LabeledAssertion(span.clone(), expr1));
            f(&expr)
        }
    }
}

pub(crate) fn map_stmt_expr_visitor<F: FnMut(&Expr) -> Expr>(stmt: &Stmt, f: &mut F) -> Stmt {
    match &**stmt {
        StmtX::Assume(e) => {
            let expr = map_expr_visitor(e, f);
            Rc::new(StmtX::Assume(f(&expr)))
        }
        StmtX::Assert(span, e) => {
            let expr = map_expr_visitor(e, f);
            Rc::new(StmtX::Assert(span.clone(), f(&expr)))
        }
        StmtX::Assign(x, e) => {
            let expr = map_expr_visitor(e, f);
            Rc::new(StmtX::Assign(x.clone(), f(&expr)))
        }
        StmtX::Block(_) => stmt.clone(),
    }
}

pub(crate) fn map_stmt_visitor<F: FnMut(&Stmt) -> Stmt>(stmt: &Stmt, f: &mut F) -> Stmt {
    match &**stmt {
        StmtX::Assume(_) => f(stmt),
        StmtX::Assert(_, _) => f(stmt),
        StmtX::Assign(_, _) => f(stmt),
        StmtX::Block(ss) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.push(map_stmt_visitor(s, f));
            }
            let stmt = Rc::new(StmtX::Block(Rc::new(stmts.into_boxed_slice())));
            f(&stmt)
        }
    }
}
