use crate::ast::{AssertProof, TransitionStmt};
use quote::quote_spanned;
use syn::{Expr, Ident};

// Given a transition, we convert it into a lemma that will create the correct
// verification conditions for its 'assert' statement.
//
// For example, a transition, written in our state machine DSL:
//
//     require(A);
//     assert(B);
//
// would turn into Verus code:
//
//     assume(A);
//     assert(B);
//
// If the resulting sequence of statements passes verification, one can conclude that
// the 'weak' version of the transition is equivalent to the 'strong' version
// (conditional on the invariant holding).
//
// Notably, this wouldn't actually be safe Verus code for a user to produce;
// it doesn't produce a lemma that would be callable as it would be if it had requires/ensures,
// so this only makes sense as long as we're willing to "trust" the macro expansion code.
//
// Still, it's a very easy transformation to do, and doesn't require us to write even
// more weakest-precondition-esque conditions than we already do, so it's what I'm going
// with for now.

pub fn safety_condition_body(ts: &TransitionStmt) -> Option<Expr> {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut h = Vec::new();
            for t in v.iter() {
                if let Some(q) = safety_condition_body(t) {
                    h.push(q);
                }
            }
            if h.len() > 0 {
                Some(Expr::Verbatim(quote_spanned! { *span => #(#h)* }))
            } else {
                None
            }
        }
        TransitionStmt::Let(span, id, _lk, v, child) => {
            let t = safety_condition_body(child);
            Some(Expr::Verbatim(quote_spanned! {*span =>
                { let #id = #v; #t }
            }))
        }
        TransitionStmt::If(span, cond, thn, els) => {
            let t1 = safety_condition_body(thn);
            let t2 = safety_condition_body(els);
            match (t1, t2) {
                (None, None) => None,
                (Some(e), None) => Some(Expr::Verbatim(quote_spanned! {*span =>
                    if #cond {
                        #e
                    }
                })),
                (None, Some(e)) => Some(Expr::Verbatim(quote_spanned! {*span =>
                    if #cond {
                    } else {
                        #e
                    }
                })),
                (Some(e1), Some(e2)) => Some(Expr::Verbatim(quote_spanned! {*span =>
                    if #cond {
                        #e1
                    } else {
                        #e2
                    }
                })),
            }
        }
        TransitionStmt::Require(span, e) => Some(Expr::Verbatim(quote_spanned! {*span =>
            crate::pervasive::assume(#e);
        })),
        TransitionStmt::Assert(span, e, AssertProof { proof: None, error_msg }) => {
            let assert_fn = Ident::new(error_msg, *span);
            Some(Expr::Verbatim(quote_spanned! {*span =>
                crate::pervasive::state_machine_internal::#assert_fn(#e);
            }))
        }
        TransitionStmt::Assert(span, e, AssertProof { proof: Some(proof), error_msg }) => {
            let assert_fn = Ident::new(error_msg, *span);
            Some(Expr::Verbatim(quote_spanned! {*span =>
                ::builtin::assert_by(#e, {
                    #proof
                    crate::pervasive::state_machine_internal::#assert_fn(#e);
                });
            }))
        }
        TransitionStmt::Initialize(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::Special(..) => {
            panic!("should have been removed at earlier processing stage");
        }
        TransitionStmt::PostCondition(..) => {
            // These may have been created during simplification, but we can ignore
            // them. The updated values are irrelevant for safety conditions.
            None
        }
    }
}

/// Returns true if there are any 'assert' statements.

pub fn has_any_assert(ts: &TransitionStmt) -> bool {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for t in v.iter() {
                if has_any_assert(t) {
                    return true;
                }
            }
            false
        }
        TransitionStmt::Let(_, _, _, _, child) => has_any_assert(child),
        TransitionStmt::If(_span, _cond, thn, els) => has_any_assert(thn) || has_any_assert(els),
        TransitionStmt::Require(_, _) => false,
        TransitionStmt::Assert(..) => true,
        TransitionStmt::Initialize(..) => false,
        TransitionStmt::Update(..) => false,
        TransitionStmt::Special(..) => false,
        TransitionStmt::PostCondition(..) => false,
    }
}
