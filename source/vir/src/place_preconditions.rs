/*!
### Place evaluation order and side-effects (more than you wanted to know)

A Place expression can have arbitrary side-effects, INCLUDING modifying the place that
is being referred to. As a result, we have to be very careful about evaluation order.
In general, you evaluate the "place" first, then read/write whatever from the place.
That means if you write something like `a[{ a = b; i }]` this is equivalent to `a = b; a[i]`.

Things get more complicated when dealing with bounds-checks.
Consider: `a[i][{ a = b; j }]`. In this expression, we bounds-check `a[i]` first, then
evaluate the second index. Does that mean the `a = b` assignment could invalidate the
bounds-check that was performed previously?
 - If `a` is an array then no, because the length of the array is fixed
 - If `a` is a slice then yes, so rustc checks for this case and disallows it.
   (See [https://doc.rust-lang.org/1.93.0/nightly-rustc/rustc_middle/mir/enum.FakeReadCause.html#variant.ForIndex])
Either way this is fine for us; either we don't have to worry about it or the bounds-check
is unaffected by the assignment.

What about unions? In Verus, we naturally have a precondition that a union access, but
in Rust there's no actual check (except in the Abstract Machine state to determine UB).
Anyway, despite the fact that union fields have a "precondition",
there's no analogous check like there is for slice indexing.
Thus, Rust's borrow-checker accepts this: `a.union_field[{a = b}]`
and reading this is non-UB provided `b.union_field` is a valid union field read.
Counter-intuitively, it doesn't even matter if `a.union_field` is valid _before_ the assignment,
since that memory location isn't actually read from.
Note, though, that the ordering of the bounds-check and the ordering of the field access
depends on whether the index is for an array or slice (since for the slice, we need to do
the field access to get the length).

To summarize, the evaluation order for a place expression with only array accesses:
  local.foo[e1].bar[e2]
Would be:
  - evaluate e1
  - bounds-check e1
  - evaluate e2
  - bounds-check e2
  - check all field accesses are safe
However, if any of the indices are _slice_ indices, then the relevant field safety checks
need to be moved earlier. (Though, again, index checks actually block subsequent mutations,
so we wouldn't need to do any field safety check more than once.)
Also, the order of the checks doesn't really matter to Verus, as long as both are hard
requirements, but it might matter if we model unwinding.

TODO(new_mut_ref): fix or error on these cases and then document what we actually support
*/

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

/// Precondition (AST) for a FieldOpr expression that needs a variant-check.
/// Input expressions must be side-effect-free.
pub(crate) fn field_check(span: &Span, e1: &Expr, field_opr: &FieldOpr) -> Stmt {
    let FieldOpr { datatype, variant, field: _, get_variant: _, check: _ } = field_opr;
    let unary = UnaryOpr::IsVariant { datatype: datatype.clone(), variant: variant.clone() };
    let condition = ExprX::UnaryOpr(unary, e1.clone());
    let condition = SpannedTyped::new(&e1.span, &Arc::new(TypX::Bool), condition);
    let assert_expr = SpannedTyped::new(
        span,
        &unit_typ(),
        ExprX::AssertAssume { is_assume: false, expr: condition, msg: Some(field_msg(span)) },
    );
    Spanned::new(span.clone(), StmtX::Expr(assert_expr))
}

pub(crate) fn sst_field_check(span: &Span, e1: &Exp, field_opr: &FieldOpr) -> (Exp, Message) {
    let FieldOpr { datatype, variant, field: _, get_variant: _, check: _ } = field_opr;
    let unary = UnaryOpr::IsVariant { datatype: datatype.clone(), variant: variant.clone() };
    let condition = ExpX::UnaryOpr(unary, e1.clone());
    let condition = SpannedTyped::new(&e1.span, &Arc::new(TypX::Bool), condition);
    (condition, field_msg(span))
}

fn field_msg(span: &Span) -> Message {
    crate::messages::error(
        span,
        "requirement not met: to access this field, the union must be in the correct variant",
    )
}
