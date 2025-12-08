use crate::ast::*;
use crate::ast_util::*;
use crate::def::Spanned;
use crate::messages::{Message, Span};
use crate::sst::*;
use crate::sst_util::*;
use std::sync::Arc;

/// Precondition (AST) for a PlaceX::Index expression that needs a bound-check.
/// Input expressions must be side-effect-free.
pub(crate) fn index_bound(span: &Span, e1: &Expr, e2: &Expr, kind: ArrayKind) -> Stmt {
    let int_typ = Arc::new(TypX::Int(IntRange::Int));
    let zero = SpannedTyped::new(span, &int_typ, ExprX::Const(const_int_from_u128(0)));
    let len = SpannedTyped::new(span, &int_typ, ExprX::Unary(UnaryOp::Length(kind), e1.clone()));
    let lower = mk_ineq(span, &zero, e2, InequalityOp::Le);
    let upper = mk_ineq(span, e2, &len, InequalityOp::Lt);
    let condition = conjoin(span, &vec![lower, upper]);

    let assert_expr = SpannedTyped::new(
        span,
        &unit_typ(),
        ExprX::AssertAssume { is_assume: false, expr: condition, msg: Some(index_msg(span)) },
    );
    Spanned::new(span.clone(), StmtX::Expr(assert_expr))
}

/// Precondition (SST) for a PlaceX::Index expression that needs a bound-check.
pub(crate) fn sst_index_bound(span: &Span, e1: &Exp, e2: &Exp, kind: ArrayKind) -> (Exp, Message) {
    let int_typ = Arc::new(TypX::Int(IntRange::Int));
    let zero = SpannedTyped::new(span, &int_typ, ExpX::Const(const_int_from_u128(0)));
    let len = SpannedTyped::new(span, &int_typ, ExpX::Unary(UnaryOp::Length(kind), e1.clone()));
    let lower = sst_le(span, &zero, e2);
    let upper = sst_lt(span, e2, &len);
    let condition = sst_and(span, &lower, &upper);

    (condition, index_msg(span))
}

fn index_msg(span: &Span) -> Message {
    crate::messages::error(span, "precondition not met: index in bounds for this access")
}
