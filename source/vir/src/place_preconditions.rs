/*!
### How to evaluate a place expression

Consider an arbitrary place expresssion, with an arbitrary combination of
dereferences, field projections (including union field projections),
and array/slice indices.

```
local.*.*.f1.*.f2[IDX].f3.*[IDX2].f4.*
```

(I use postfix `.*` here for readability)

How do you evaluate this, accounting for all of:
 * The side-effects of the index expressions
 * bounds-checks inserted by Rust
 * precondition needed to ensure pointer accesses are safe

It's tempting to think you just start at the left, walking down the pointers and then
evaluating subexpressions when you reach them. In reality, the entire place expression is emitted
at the end, after all side-effects have run. So you end up with something like this:

```
let i1 = IDX;
let i2 = IDX2;
local.*.*.f1.*.f2[i1].f3.*[i2].f4 .* // place is read-to or written-from or whatnot
```

Note, in particular, that `IDX` and `IDX2` expressions _are_ allowed to mutate `local`.
Therefore, it is important that we do not evaluate validity of the access to
`local.*.*.f1.*.f2` _before_ evaluating `IDX`, as the evaluation of `IDX` could end up
invalidating that access.

Things get more complicated when dealing with bounds checks because the bounds-check
requires computation of the length. For an array, the length is known at compiler time, but
for a slice, we must look up the length at runtime, and this potentially requires unsafe
accesses, which requires us to check the well-formedness of the lookup at that point.

Fortunately, Rust _does_ ensure that the bounds-check cannot be invalidated after it is performed
the first time. For example, if the `[IDX]` in `local.*.*.f1.*.f2[IDX].f3.*[IDX2].f4.*`
is a slice index, then `IDX2` is not allowed to overwrite `local`, because the bounds-check
locks it in place. (Not true of `[IDX]` is an array index!)

So basically, the ordering goes something like:

1.
 * Evaluate `IDX`
 * If `[IDX]` is a slice, assert the well-formedness of the lookup `local.*.*.f1.*.f2`
 * Compute the length and perform the bounds-check, panic on failure
   (We don't support the panic behavior right now, so for us,
    this amounts to asserting the bounds-check holds.)
2.
 * Evalute `IDX2`
 * If `[IDX2]` is a slice, assert the well-formedness of the lookup `local.*.*.f1.*.f2[_].f3.*`
   (Don't need to repeat any conditions already checked in Step 1)
 * Compute the length and perform the bounds-check, panic on failure

### How do we check that these places are well-formed?

For a union field, we want to check that the union is "in" the correct variant
(we model unions as enums, though this is technically incorrect, see
<https://github.com/verus-lang/verus/issues/2503>).

For a raw pointer, we check that the associated pointer permission object (`PointsTo`) has
the right pointer and is in an initialized state.

TODO(native_raw_ptrs): even though Rust will check that an access doesn't get invalidated
by mutating the target place, it doesn't know about our permission objects, so we will have to check
those ourselves.

### How is the length computed?

For an array, we just get it off the type, and for the slice, we get it off the length of
the sequence view of the slice.

This is actually slightly more restrictive than it needs to be. Rust uses fat pointers,
so in the actual runtime, Rust gets the slice length off the pointer metadata.
This means that, if the last dereference before the slice index _doesn't need to be dereferenced_,
and in particular: if it's a raw pointer, we don't need to check that it's safe to dereference
(at this program point).

TODO(native_raw_ptrs): check that the borrow checker and the VC gen agree on this matter

### But what about the well-formedness of the last part after the index, (`f4.*`)? When do we check that?

We check this immediately after the place expression finishes.

_Technically_, this should depend on how the place expression is used. To read or write,
you need the place to be dereferencable, which includes having the memory be well-typed.
(Note that a write does a drop on the existing contents which asserts their well-formedness.)

But if you do something like `let _ = PLACE_EXPRESSION`, then the place ends up not getting
accessed at all and there is no need to check that any access is well-formed.

And if the place you're writing to is a union field, there is no drop, so there's no requirement
on the memory being initialized, just that you have write access.

All that said, we don't bother with these nuances right now, and we just assert the well-formedness
immediately after the place expression.

There's just one problem: this can _still be too early_.

This only comes up with the `match` expression, which is the only kind of expression where
we can contrive a situation where more code gets executed before the first access to the place:

```rust
match *x {
  _ if ({ ... }) => { ... }
  (a, b) => { ... }
}
```

Since `*x` isn't accessed until the second arm, we can still mutate `*x` in the guard block.
That means that trying to evalute the well-formedness of the `*x` access at the top of the match
is too early: that check might be invalidated before the first access to `*x`. After the first
access, Rust will ensure it can't change or be invalidated, but it's fair game until the first
access.

To deal with this, we make our own check (see `MatchGuardFreeze`) that this doesn't happen.
*/

use crate::ast::*;
use crate::ast_to_sst::State;
use crate::ast_util::*;
use crate::context::Ctx;
use crate::def::Spanned;
use crate::messages::{Message, Span};
use crate::points_to::permission_place_to_friendly_string;
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

/// `get_variant` accessors are total - just a recommends-only nudge for a likely mistake.
pub(crate) fn sst_field_recommends_check(
    span: &Span,
    e1: &Exp,
    field_opr: &FieldOpr,
) -> (Exp, Message) {
    let FieldOpr { datatype, variant, field: _, get_variant: _, check: _ } = field_opr;
    let unary = UnaryOpr::IsVariant { datatype: datatype.clone(), variant: variant.clone() };
    let condition = ExpX::UnaryOpr(unary, e1.clone());
    let condition = SpannedTyped::new(&e1.span, &Arc::new(TypX::Bool), condition);
    (condition, field_recommends_msg(span, variant))
}

fn field_recommends_msg(span: &Span, variant: &Ident) -> Message {
    crate::messages::error(
        span,
        format!(
            "recommendation not met: cannot show that this value is variant `{variant}` before accessing this field"
        ),
    )
}

impl ArrayKind {
    pub(crate) fn getting_len_requires_read(&self) -> bool {
        match self {
            ArrayKind::Array => false,
            ArrayKind::Slice => true,
        }
    }
}

fn check_variants_correct(
    ctx: &Ctx,
    state: &mut State,
    span: &Span,
    place: &Place,
) -> (Exp, Vec<(Exp, Message)>) {
    let mk_exp = |expx: ExpX| SpannedTyped::new(&place.span, &place.typ, expx);
    match &place.x {
        PlaceX::Field(field_opr, p) => {
            let (e, mut checks) = check_variants_correct(ctx, state, span, p);
            let FieldOpr { datatype, variant, field: _, get_variant: _, check: _ } = field_opr;
            let unary =
                UnaryOpr::IsVariant { datatype: datatype.clone(), variant: variant.clone() };

            let condition = ExpX::UnaryOpr(unary, e.clone());
            let condition = SpannedTyped::new(span, &Arc::new(TypX::Bool), condition);
            checks.push((condition, crate::messages::error(span,
                format!("cannot show that `{:}` has variant `{variant}`, needed to access the pointer permission", permission_place_to_friendly_string(p)))));

            let e = mk_exp(ExpX::UnaryOpr(UnaryOpr::Field(field_opr.clone()), e));
            (e, checks)
        }
        PlaceX::DerefMut(p) => {
            let (e, checks) = check_variants_correct(ctx, state, span, p);
            let e = mk_exp(ExpX::Unary(UnaryOp::MutRefCurrent, e));
            (e, checks)
        }
        PlaceX::ModeUnwrap(p, mwm) => {
            assert!(matches!(mwm, ModeWrapperMode::Proof));
            check_variants_correct(ctx, state, span, p)
        }
        PlaceX::Local(x) => {
            let unique_id = state.get_var_unique_id(&x);
            let e = mk_exp(ExpX::Var(unique_id));
            (e, vec![])
        }
        PlaceX::Index(..) => {
            panic!("check_variants_correct: Index");
        }
        PlaceX::Temporary(..) => {
            panic!("check_variants_correct: Temporary");
        }
        PlaceX::WithExpr(..) => {
            panic!("check_variants_correct: WithExpr");
        }
        PlaceX::UserDefinedTypInvariantObligation(..) => {
            panic!("check_variants_correct: UserDefinedTypInvariantObligation");
        }
        PlaceX::DerefRaw(..) => {
            panic!("check_variants_correct: DerefRaw");
        }
    }
}

pub(crate) fn sst_raw_deref_check(
    ctx: &Ctx,
    state: &mut State,
    span: &Span,
    ptr: &Exp,
    permission_place: &Option<Place>,
    physical_place: &Place,
) -> Vec<(Exp, Message)> {
    let Some(permission_place) = permission_place else {
        return vec![(sst_bool(span, false), {
            let mut err = crate::messages::error(
                span,
                "possible memory safety violation: no `PointsTo` set for this pointer operation",
            );
            if let Some(desc) = crate::points_to::get_place_descriptor(physical_place) {
                err = err.help(format!(
                    "You can set a permission using `#[verifier::permission(\"{desc:}\")]`"
                ));
            }
            err
        })];
    };

    let (perm, mut checks) = check_variants_correct(ctx, state, span, permission_place);

    let p1 = crate::points_to::sst_get_ptr(&perm);
    let ptrs_eq = sst_equal(span, ptr, &p1);

    checks.push((
        ptrs_eq,
        crate::messages::error(
            span,
            "possible memory safety violation: unable to prove the pointer agrees with the given `PointsTo`",
        ),
    ));

    let is_init = crate::points_to::sst_get_is_init(&perm);
    checks.push((
        is_init,
        crate::messages::error(
            span,
            "possible memory safety violation: unable to prove the `PointsTo` is initialized",
        ),
    ));

    checks
}
