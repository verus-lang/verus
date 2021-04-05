use crate::ast::{BinaryOp, Const, Expr, ExprX, LogicalOp, Stmt, StmtX};
use std::rc::Rc;

pub fn stmt_to_expr(stmt: &Stmt, pred: Expr) -> Expr {
    match &**stmt {
        StmtX::Assume(expr) => {
            // wp((assume Q), P) = Q ==> P
            Rc::new(ExprX::Binary(BinaryOp::Implies, expr.clone(), pred))
        }
        StmtX::Assert(span, expr) => {
            // wp((assert Q), P) = Q /\ P
            let assertion = Rc::new(ExprX::LabeledAssertion(span.clone(), expr.clone()));
            Rc::new(ExprX::Logical(LogicalOp::And, Rc::new(Box::new([assertion, pred]))))
        }
        StmtX::Block(stmts) => {
            // wp((s1; s2), P) = wp(s1, wp(s2, P))
            let mut p = pred;
            for stmt in stmts.iter().rev() {
                p = stmt_to_expr(stmt, p);
            }
            p
        }
    }
}

pub fn block_to_assert(stmt: &Stmt) -> Stmt {
    let span = Rc::new(None);
    let tru = Rc::new(ExprX::Const(Const::Bool(true)));
    let expr = stmt_to_expr(&stmt, tru);
    Rc::new(StmtX::Assert(span, expr))
}
