use crate::ast::{
    BinaryOp, Constant, Decl, DeclX, Expr, ExprX, MultiOp, Query, QueryX, Stmt, StmtX, UnaryOp,
};
use crate::ast_util::bool_typ;
use crate::def::SWITCH_LABEL;
use std::sync::Arc;

fn stmt_to_expr(label_n: &mut u64, locals: &mut Vec<Decl>, stmt: &Stmt, pred: Expr) -> Expr {
    match &**stmt {
        StmtX::Assume(expr) => {
            // wp((assume Q), P) = Q ==> P
            Arc::new(ExprX::Binary(BinaryOp::Implies, expr.clone(), pred))
        }
        StmtX::Assert(span, expr) => {
            // wp((assert Q), P) = Q /\ P
            let assertion = Arc::new(ExprX::LabeledAssertion(span.clone(), expr.clone()));
            Arc::new(ExprX::Multi(MultiOp::And, Arc::new(vec![assertion, pred])))
        }
        StmtX::Havoc(_) => panic!("internal error: Havoc in block_to_assert"),
        StmtX::Assign(_, _) => panic!("internal error: Assign in block_to_assert"),
        StmtX::Snapshot(_) => panic!("internal error: Snapshot in block_to_assert"),
        StmtX::Block(stmts) => {
            // wp((s1; s2), P) = wp(s1, wp(s2, P))
            let mut p = pred;
            for stmt in stmts.iter().rev() {
                p = stmt_to_expr(label_n, locals, stmt, p);
            }
            p
        }
        StmtX::Switch(stmts) => {
            // wp((s1 or s2), P) = wp(s1, P) /\ wp(s2, P)
            // To avoid duplicating P, we use:
            // wp((s1 or s2), P) = (P ==> label) ==> wp(s1, label) /\ wp(s2, label)
            //                   = (wp(s1, label) /\ wp(s2, label)) \/ (!label /\ P)
            let label = Arc::new(format!("{}{}", SWITCH_LABEL, label_n));
            *label_n += 1;
            locals.push(Arc::new(DeclX::Const(label.clone(), bool_typ())));
            let exp_label = Arc::new(ExprX::Var(label));
            let mut exprs: Vec<Expr> = Vec::new();
            for stmt in stmts.iter() {
                exprs.push(stmt_to_expr(label_n, locals, stmt, exp_label.clone()));
            }
            let neg_label = Arc::new(ExprX::Unary(UnaryOp::Not, exp_label));
            let and1 = Arc::new(ExprX::Multi(MultiOp::And, Arc::new(exprs)));
            let and2 = Arc::new(ExprX::Multi(MultiOp::And, Arc::new(vec![neg_label, pred])));
            Arc::new(ExprX::Multi(MultiOp::Or, Arc::new(vec![and1, and2])))
        }
    }
}

pub(crate) fn lower_query(query: &Query) -> Query {
    let mut locals: Vec<Decl> = (*query.local).clone();
    let mut switch_label: u64 = 0;
    let tru = Arc::new(ExprX::Const(Constant::Bool(true)));
    let expr = stmt_to_expr(&mut switch_label, &mut locals, &query.assertion, tru);
    let assertion = Arc::new(StmtX::Assert(Arc::new(None), expr));
    Arc::new(QueryX { local: Arc::new(locals), assertion })
}
