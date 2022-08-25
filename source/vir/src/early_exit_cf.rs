use crate::ast::{CallTarget, Expr, ExprX, VirErr};
use crate::ast_visitor::{expr_visitor_dfs, VisitorControlFlow, VisitorScopeMap};
use air::ast::Span;
use air::errors::error;
use air::scope_map::ScopeMap;

#[derive(Copy, Clone, Debug)]
enum StatementType {
    Return, // TODO add Break and Continue when they are supported
}

#[derive(Clone, Debug)]
struct EarlyExitInst {
    span: Span,
    _statement: StatementType,
}

pub fn assert_no_early_exit_in_inv_block(inv_span: &Span, expr: &Expr) -> Result<(), VirErr> {
    let v = expr_get_early_exits(expr);
    if v.len() == 0 {
        Ok(())
    } else {
        Err(error("invariant block might exit early", inv_span)
            .primary_label(&v[0].span, "would exit from here"))
    }
}

/// Walk the AST and find all return/break/continue statements that would cause an
/// 'early exit' from the expression. Does *not* recurse into nested Invariant blocks,
/// to avoid quadratic behavior, and to avoid doubling up the errors.

fn expr_get_early_exits(expr: &Expr) -> Vec<EarlyExitInst> {
    let mut v = Vec::new();
    let mut scope_map = ScopeMap::new();
    expr_get_early_exits_rec(expr, false, &mut scope_map, &mut v);
    v
}

/// While recursing, we keep track of whether we entered a loop or not; then we can know
/// if a break/continue would cause an exit at the high-level expr.
/// (Well, it will be useful when we implement break/continue, anyway.)

fn expr_get_early_exits_rec(
    expr: &Expr,
    in_loop: bool,
    scope_map: &mut VisitorScopeMap,
    results: &mut Vec<EarlyExitInst>,
) {
    expr_visitor_dfs::<(), _>(expr, scope_map, &mut |scope_map, expr| {
        match &expr.x {
            ExprX::Const(..)
            | ExprX::Var(..)
            | ExprX::VarLoc(..)
            | ExprX::VarAt(..)
            | ExprX::ConstVar(..)
            | ExprX::Loc(..)
            | ExprX::Call(CallTarget::Static(..), _)
            | ExprX::Call(CallTarget::FnSpec(..), _)
            | ExprX::Tuple(..)
            | ExprX::Ctor(..)
            | ExprX::Unary(..)
            | ExprX::UnaryOpr(..)
            | ExprX::Binary(..)
            | ExprX::Multi(..)
            | ExprX::Assign { .. }
            | ExprX::If(..)
            | ExprX::Match(..)
            | ExprX::Ghost { .. }
            | ExprX::Block(..) => VisitorControlFlow::Recurse,
            ExprX::Quant(..)
            | ExprX::Closure(..)
            | ExprX::Choose { .. }
            | ExprX::WithTriggers { .. }
            | ExprX::Fuel(..)
            | ExprX::Header(..)
            | ExprX::Admit
            | ExprX::Forall { .. }
            | ExprX::RevealString(_) => VisitorControlFlow::Return,
            ExprX::AssertQuery { .. } => VisitorControlFlow::Return,
            ExprX::While { cond, body, invs: _ } => {
                expr_get_early_exits_rec(cond, in_loop, scope_map, results);
                expr_get_early_exits_rec(body, true, scope_map, results);
                VisitorControlFlow::Return
            }
            ExprX::Return(_) => {
                results.push(EarlyExitInst {
                    span: expr.span.clone(),
                    _statement: StatementType::Return,
                });
                VisitorControlFlow::Recurse
            }
            ExprX::OpenInvariant(inv, _binder, _body, _atomicity) => {
                expr_get_early_exits_rec(inv, in_loop, scope_map, results);
                // Skip checking nested loops to avoid quadratic behavior:
                VisitorControlFlow::Return
            }
        }
    });
}
