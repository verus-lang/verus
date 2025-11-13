use crate::ast::{LetKind, SpecialOp, SplitKind, Transition, TransitionKind, TransitionStmt};
use syn_verus::parse::Error;

// Here we check the following rules related to `birds_eye` let-bindings:
//
// 1. A `birds_eye let` should not appear unless the state machine is 'concurrent'.
//
// 2. A `birds_eye let` should not appear in an 'init' transition.
//
// 3. A Guard statement cannot be declared in the scope of a `birds_eye let`.
//
// 4. A 'requires', or any special op that might expand to a 'requires'
//    cannot be declared in the scope of a `birds_eye let`.
//
// 5. A 'requires', or any special op that might expand to a 'requires'
//    cannot be sequenced after any 'assert' which is in
//    the scope of a `birds_eye let`.
//
// Note also that for these purposes, a variable bound in a 'withdraw' counts as birds_eye.
//
// The rationale for these rules is as follows:
//
// 1. This is self-explanatory. `birds_eye` is a feature for tokenized state machines.
//    It only affects the token exchange functions, not the atomic transition relations.
//
// 2. We can't even access `pre` in an 'init' transition, so `birds_eye` wouldn't
//    do anything.
//
// 3. This is a soundness issue. For the guarding rule to work, the guard has to be a
//    deterministic function of the inputs to the exchange function.
//
//    (Note: this rule may actually be stronger than necessary right now. For example,
//    in the StorageMap case, suppose we have `guard_kv(key, val)`. Then token being
//    guarded has value `val`, but it does not depend on the `key` argument.
//    This means that, in principle, we could have the key depend on a `birds_eye` value
//    as long as `val` does not. Making this distinction would require more fine-grained
//    dependency analysis.)
//
// 4. The point here is that if we have something like,
//
//         birds_eye let x = foo;
//         require(e);
//
//    then `e` might depend on `x`. So when we try to output the precondition in the
//    exchange fn, we have to output the expression `let x = foo; e`.
//    But if the let-statement is a birds_eye statement, then the 'foo' would have
//    reference variables that don't exist in the input parameters to the exchange fn.
//    So we would end up generating a malformed expression.
//
// 5. Similar to (4), but here the idea is to prevent something like,
//
//         { birds_eye let x = foo; assert(e); } require(e2);
//
//    In this case, `e2` can't directly refer to `x`, but this would still cause
//    problems, because we would generate a precondition like,
//
//         { let x = foo; e } ==> e2
//
//    And again, we can't put `foo` in a precondition.
//    In principle, we could leave these hypotheses out entirely (this would be sound,
//    since leaving off the hypothesis only makes the precondition harder to meet).
//    But the intent is that the preconditions should match what we do for the
//    'weak' transition relation (i.e., the formal definition of the transition
//    relation) and it seems better to optimize for meeting that goal.
//
// In summary:
//
//  * (1) and (2) are basically warnings
//  * (4) and (5) are necessary, but if they were omitted, we would probably just
//    end up with errors in type-resolution of the generated code.
//  * (3) is necessary for soundness and wouldn't be caught otherwise.

pub fn check_birds_eye(trans: &Transition, concurrent: bool, errors: &mut Vec<Error>) {
    check_birds_eye_rec(
        &trans.body,
        trans.kind == TransitionKind::Init,
        concurrent,
        None,
        &mut None,
        errors,
    );
}

fn check_birds_eye_rec(
    ts: &TransitionStmt,
    is_init: bool,
    concurrent: bool,
    scoped_in_birds_eye: Option<&'static str>,
    past_assert: &mut Option<&'static str>,
    errors: &mut Vec<Error>,
) {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter() {
                check_birds_eye_rec(
                    child,
                    is_init,
                    concurrent,
                    scoped_in_birds_eye,
                    past_assert,
                    errors,
                );
            }
        }
        TransitionStmt::Split(span, SplitKind::Let(_pat, _ty, lk, _init_e), splits) => {
            assert!(splits.len() == 1);
            let child = &splits[0];

            let mut is_birds_eye = *lk == LetKind::BirdsEye;
            if is_birds_eye {
                if !concurrent {
                    errors.push(Error::new(
                        *span,
                        "`birds_eye` only makes sense for tokenized state machines; did you mean to use the tokenized_state_machine! macro?"));
                    is_birds_eye = false; // to prevent the other errors from cluttering
                }
                if is_init {
                    errors.push(Error::new(
                        *span,
                        "`birds_eye` has no effect in an init! definition",
                    ));
                    is_birds_eye = false; // to prevent the other errors from cluttering
                }
            }
            check_birds_eye_rec(
                child,
                is_init,
                concurrent,
                opt_or(scoped_in_birds_eye, is_birds_eye, "birds_eye"),
                past_assert,
                errors,
            );
        }
        TransitionStmt::Split(span, SplitKind::Special(_, op, _, _), splits) => {
            let name = op.stmt.name();
            if op.is_guard() {
                if let Some(m) = scoped_in_birds_eye {
                    errors.push(Error::new(
                        *span,
                        format!("'{name:}' statements should not be in the scope of a `{m:}` let-binding; a guard value must be a deterministic function of the local inputs")));
                }
            } else if affects_precondition(op) {
                if let Some(m) = scoped_in_birds_eye {
                    errors.push(Error::new(
                        *span,
                        format!("'{name:}' statements should not be in the scope of a `{m:}` let-binding; preconditions of an exchange cannot depend on such bindings")));
                } else if let Some(m) = *past_assert {
                    errors.push(Error::new(
                        *span,
                        format!("'{name:}' statements should not be preceeded by an assert which is in the scope of a `{m:}` let-binding; preconditions of an exchange cannot depend on such bindings")));
                }
            }

            if splits.len() > 0 {
                assert!(splits.len() == 1);
                let child = &splits[0];

                let is_withdraw = op.stmt.is_withdraw();

                check_birds_eye_rec(
                    child,
                    is_init,
                    concurrent,
                    opt_or(scoped_in_birds_eye, is_withdraw, "withdraw"),
                    past_assert,
                    errors,
                );
            }
        }
        TransitionStmt::Split(_span, _split_kind, splits) => {
            let mut new_past_assert = None;
            for split in splits {
                let mut past_assert1 = *past_assert;
                check_birds_eye_rec(
                    split,
                    is_init,
                    concurrent,
                    scoped_in_birds_eye,
                    &mut past_assert1,
                    errors,
                );
                new_past_assert = new_past_assert.or(past_assert1);
            }
            *past_assert = new_past_assert;
        }
        TransitionStmt::Assert(..) => {
            if scoped_in_birds_eye.is_some() {
                *past_assert = scoped_in_birds_eye;
            }
        }

        TransitionStmt::Require(span, _) => {
            if let Some(m) = scoped_in_birds_eye {
                errors.push(Error::new(
                    *span,
                    format!("'require' statements should not be in the scope of a `{m:}` let-binding; preconditions of an exchange cannot depend on such bindings")));
            } else if let Some(m) = *past_assert {
                errors.push(Error::new(
                    *span,
                    format!("'require' statements should not be preceeded by an assert which is in the scope of a `{m:}` let-binding; preconditions of an exchange cannot depend on such bindings")));
            }
        }

        TransitionStmt::Update(..) => {}
        TransitionStmt::SubUpdate(..) => {}
        TransitionStmt::Initialize(..) => {}
        TransitionStmt::PostCondition(..) => {}
    }
}

/// True if it's the case that an expression in the op
/// might appear in the _precondition_ of an exchange method.
/// Should return 'true' for remove, have, and deposit ops.
fn affects_precondition(op: &SpecialOp) -> bool {
    op.is_remove() || op.is_have() || op.is_deposit()
}

fn opt_or<'a>(o: Option<&'a str>, b: bool, s: &'a str) -> Option<&'a str> {
    match o {
        Some(_) => o,
        None => {
            if b {
                Some(s)
            } else {
                None
            }
        }
    }
}
