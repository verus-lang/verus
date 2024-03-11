use crate::ast::{Decl, DeclX, Expr, ExprX, Query, QueryX, Stmt, StmtX, UnaryOp};
use crate::ast_util::bool_typ;
use crate::ast_util::{mk_and, mk_implies, mk_or, mk_true};
use crate::def::{break_label, SWITCH_LABEL};
use std::sync::Arc;

fn stmt_to_expr(label_n: &mut u64, locals: &mut Vec<Decl>, stmt: &Stmt, pred: Expr) -> Expr {
    match &**stmt {
        StmtX::Assume(expr) => {
            // wp((assume Q), P) = Q ==> P
            mk_implies(&expr, &pred)
        }
        StmtX::Assert(assert_id, span, filter, expr) => {
            // wp((assert Q), P) = Q /\ P
            let assertion: Expr = Arc::new(ExprX::LabeledAssertion(
                assert_id.clone(),
                span.clone(),
                filter.clone(),
                expr.clone(),
            ));
            mk_and(&vec![assertion, pred])
        }
        StmtX::Havoc(_) => panic!("internal error: Havoc in block_to_assert"),
        StmtX::Assign(_, _) => panic!("internal error: Assign in block_to_assert"),
        StmtX::Snapshot(_) => panic!("internal error: Snapshot in block_to_assert"),
        StmtX::DeadEnd(stmt) => {
            // wp(deadend(s), P) = wp(s, true) /\ P
            let wps = stmt_to_expr(label_n, locals, stmt, mk_true());
            mk_and(&vec![wps, pred])
        }
        StmtX::Breakable(label, stmt) => {
            // wp((s; label:), P) = (P ==> label) ==> wp(s, label)
            //                    = wp(s, label) \/ (!label /\ P)
            let label = break_label(label);
            locals.push(Arc::new(DeclX::Const(label.clone(), bool_typ())));
            let exp_label = Arc::new(ExprX::Var(label));
            let lhs = stmt_to_expr(label_n, locals, stmt, exp_label.clone());
            let neg_label = Arc::new(ExprX::Unary(UnaryOp::Not, exp_label));
            let and = mk_and(&vec![neg_label, pred]);
            // mk_or(&vec![lhs, and])
            // Z3 is sometimes reporting spurious "true" for assertion labels in stmt.
            // We can try variations, such as putting lhs second,
            // so that stmt's assertion labels are sorted second when smt_verify scans the labels.
            // We could also try (P == label) rather than (P ==> label), or try let label = P.
            mk_or(&vec![and, lhs])
        }
        StmtX::Break(label) => {
            // wp((break label), P) = label
            Arc::new(ExprX::Var(break_label(label)))
        }
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
            let and1 = mk_and(&exprs);
            let and2 = mk_and(&vec![neg_label, pred]);
            mk_or(&vec![and1, and2])
        }
    }
}

pub(crate) fn lower_query(
    message_interface: &dyn crate::messages::MessageInterface,
    query: &Query,
) -> Query {
    let mut locals: Vec<Decl> = (*query.local).clone();
    let mut switch_label: u64 = 0;
    let expr = stmt_to_expr(&mut switch_label, &mut locals, &query.assertion, mk_true());
    let assertion = Arc::new(StmtX::Assert(None, message_interface.empty(), None, expr));
    Arc::new(QueryX { local: Arc::new(locals), assertion })
}
