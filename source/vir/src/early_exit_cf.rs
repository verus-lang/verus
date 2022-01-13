use crate::ast::{ArmX, CallTarget, Expr, ExprX, Stmt, StmtX, VirErr};
use air::ast::Span;
use air::errors::error;

#[derive(Copy, Clone, Debug)]
enum StatementType {
    Return, // TODO add Break and Continue when they are supported
}

#[derive(Clone, Debug)]
struct EarlyExitInst {
    pub span: Span,
    pub statement: StatementType,
}

pub fn assert_no_early_exit_in_inv_block(inv_span: &Span, expr: &Expr) -> Result<(), VirErr> {
    let v = expr_get_early_exits(expr);
    if v.len() == 0 {
        return Ok(());
    } else {
        return Err(error("invariant block might exit early", inv_span)
            .primary_label(&v[0].span, "would exit from here"));
    }
}

/// Walk the AST and find all return/break/continue statements that would cause an
/// 'early exit' from the expression. Does *not* recurse into nested Invariant blocks,
/// to avoid quadratic behavior, and to avoid doubling up the errors.

fn expr_get_early_exits(expr: &Expr) -> Vec<EarlyExitInst> {
    let mut v = Vec::new();
    expr_get_early_exits_rec(expr, false, &mut v);
    return v;
}

/// While recursing, we keep track of whether we entered a loop or not; then we can know
/// if a break/continue would cause an exit at the high-level expr.
/// (Well, it will be useful when we implement break/continue, anyway.)

fn expr_get_early_exits_rec(expr: &Expr, in_loop: bool, results: &mut Vec<EarlyExitInst>) {
    match &expr.x {
        ExprX::Const(_) => {}
        ExprX::Var(_) => {}
        ExprX::VarAt(_, _) => {}
        ExprX::Call(CallTarget::Static(_, _), es) => {
            for e in es.iter() {
                expr_get_early_exits_rec(e, in_loop, results);
            }
        }
        ExprX::Call(CallTarget::FnSpec(e0), es) => {
            expr_get_early_exits_rec(e0, in_loop, results);
            for e in es.iter() {
                expr_get_early_exits_rec(e, in_loop, results);
            }
        }
        ExprX::Tuple(es) => {
            for e in es.iter() {
                expr_get_early_exits_rec(e, in_loop, results);
            }
        }
        ExprX::Ctor(_path, _variant, binders, update) => {
            for arg in binders.iter() {
                expr_get_early_exits_rec(&arg.a, in_loop, results);
            }
            match update {
                None => {}
                Some(u) => {
                    expr_get_early_exits_rec(u, in_loop, results);
                }
            }
        }
        ExprX::Unary(_, e1) => {
            expr_get_early_exits_rec(e1, in_loop, results);
        }
        ExprX::UnaryOpr(_, e1) => {
            expr_get_early_exits_rec(e1, in_loop, results);
        }
        ExprX::Binary(_, e1, e2) => {
            expr_get_early_exits_rec(e1, in_loop, results);
            expr_get_early_exits_rec(e2, in_loop, results);
        }
        ExprX::Quant(_, _, _) => {}
        ExprX::Closure(_, _) => {}
        ExprX::Choose(_, _) => {}
        ExprX::Assign(lhs, rhs) => {
            expr_get_early_exits_rec(lhs, in_loop, results);
            expr_get_early_exits_rec(rhs, in_loop, results);
        }
        ExprX::Fuel(_, _) => {}
        ExprX::Header(_) => {}
        ExprX::Admit => {}
        ExprX::Forall { .. } => {}
        ExprX::If(e1, e2, e3) => {
            expr_get_early_exits_rec(e1, in_loop, results);
            expr_get_early_exits_rec(e2, in_loop, results);
            match e3 {
                None => {}
                Some(e) => {
                    expr_get_early_exits_rec(e, in_loop, results);
                }
            }
        }
        ExprX::Match(e1, arms) => {
            expr_get_early_exits_rec(e1, in_loop, results);
            for arm in arms.iter() {
                match &arm.x {
                    ArmX { pattern: _, guard, body } => {
                        expr_get_early_exits_rec(guard, in_loop, results);
                        expr_get_early_exits_rec(body, in_loop, results);
                    }
                }
            }
        }
        ExprX::While { cond, body, invs: _ } => {
            expr_get_early_exits_rec(cond, in_loop, results);
            expr_get_early_exits_rec(body, true, results);
        }
        ExprX::Return(e1) => {
            match e1 {
                None => {}
                Some(e) => {
                    expr_get_early_exits_rec(e, in_loop, results);
                }
            }
            results
                .push(EarlyExitInst { span: expr.span.clone(), statement: StatementType::Return });
        }
        ExprX::Block(ss, e1) => {
            for stmt in ss.iter() {
                stmt_get_early_exits_rec(stmt, in_loop, results);
            }
            match e1 {
                None => {}
                Some(e) => {
                    expr_get_early_exits_rec(e, in_loop, results);
                }
            };
        }
        ExprX::OpenInvariant(inv, _binder, _body) => {
            expr_get_early_exits_rec(inv, in_loop, results);
            // Skip checking nested loops to avoid quadratic behavior:
            // expr_get_early_exits_rec(body, in_loop, results);
        }
    }
}

fn stmt_get_early_exits_rec(stmt: &Stmt, in_loop: bool, results: &mut Vec<EarlyExitInst>) {
    match &stmt.x {
        StmtX::Expr(e) => {
            expr_get_early_exits_rec(e, in_loop, results);
        }
        StmtX::Decl { init, .. } => match init {
            None => {}
            Some(e) => {
                expr_get_early_exits_rec(e, in_loop, results);
            }
        },
    }
}
