use crate::ast::{AssertProof, SimplStmt, SplitKind};
use crate::to_relation::emit_match;
use quote::{quote, quote_spanned};
use syn_verus::{Expr, Ident};

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

pub fn safety_condition_body_simpl_vec(sops: &Vec<SimplStmt>) -> Option<Expr> {
    let mut h = Vec::new();
    for (i, t) in sops.iter().enumerate() {
        let is_last = i == sops.len() - 1;
        if let Some(q) = safety_condition_body_simpl(t, is_last) {
            h.push(q);
        }
    }
    if h.len() > 0 { Some(Expr::Verbatim(quote! { #(#h)* })) } else { None }
}

pub fn safety_condition_body_simpl(sop: &SimplStmt, let_skip_brace: bool) -> Option<Expr> {
    match sop {
        SimplStmt::Let(span, pat, None, v, child, _) => {
            let t = safety_condition_body_simpl_vec(child);
            if let_skip_brace {
                Some(Expr::Verbatim(quote_spanned! {*span =>
                    let #pat = #v; #t
                }))
            } else {
                Some(Expr::Verbatim(quote_spanned! {*span =>
                    { let #pat = #v; #t }
                }))
            }
        }
        SimplStmt::Let(span, pat, Some(ty), v, child, _) => {
            let t = safety_condition_body_simpl_vec(child);
            if let_skip_brace {
                Some(Expr::Verbatim(quote_spanned! {*span =>
                    let #pat: #ty = #v; #t
                }))
            } else {
                Some(Expr::Verbatim(quote_spanned! {*span =>
                    { let #pat: #ty = #v; #t }
                }))
            }
        }
        SimplStmt::Split(span, SplitKind::If(cond), es, _) => {
            assert!(es.len() == 2);
            let t1 = safety_condition_body_simpl_vec(&es[0].1);
            let t2 = safety_condition_body_simpl_vec(&es[1].1);
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
        SimplStmt::Split(span, SplitKind::Match(match_e, arms), es, _) => {
            let cases: Vec<Option<Expr>> =
                es.iter().map(|e| safety_condition_body_simpl_vec(&e.1)).collect();
            if cases.iter().any(|c| c.is_some()) {
                // Any case which is empty will just look like
                //      `... => { }`
                Some(emit_match(*span, match_e, arms, &cases))
            } else {
                None
            }
        }
        SimplStmt::Split(..) => {
            panic!("should SplitKind should have been translated out");
        }
        SimplStmt::Require(span, e) => Some(Expr::Verbatim(quote_spanned_vstd! {vstd, *span =>
            #vstd::prelude::assume_(#e);
        })),
        SimplStmt::PostCondition(_span, _e, _reason) => None,
        SimplStmt::Assert(span, e, AssertProof { proof: None, error_msg }) => {
            let assert_fn = Ident::new(error_msg, *span);
            Some(Expr::Verbatim(quote_spanned_vstd! {vstd, *span =>
                #vstd::state_machine_internal::#assert_fn(#e);
            }))
        }
        SimplStmt::Assert(span, e, AssertProof { proof: Some(proof), error_msg }) => {
            let assert_fn = Ident::new(error_msg, *span);
            Some(Expr::Verbatim(quote_spanned_vstd! {vstd, *span =>
                assert(#e) by {
                    #proof
                    #vstd::state_machine_internal::#assert_fn(#e);
                };
            }))
        }
        SimplStmt::Assign(span, iden, ty, e, _prelude) => {
            // TODO need to handle scoped assigns
            // (not a problem right now because assigns are only used for
            //  - outputs
            //  - special ops
            // But we don't care about outputs, and special ops can't be scoped right now

            Some(Expr::Verbatim(quote_spanned! {*span =>
                let #iden: #ty = #e;
            }))
        }
    }
}

/// Returns true if there are any 'assert' statements.

pub fn has_any_assert_simpl_vec(sops: &Vec<SimplStmt>) -> bool {
    for sop in sops.iter() {
        if has_any_assert_simpl(sop) {
            return true;
        }
    }
    false
}

pub fn has_any_assert_simpl(sop: &SimplStmt) -> bool {
    match sop {
        SimplStmt::Let(_, _, _, _, child, _) => has_any_assert_simpl_vec(child),
        SimplStmt::Split(_span, _cond, es, _) => {
            for e in es {
                if has_any_assert_simpl_vec(&e.1) {
                    return true;
                }
            }
            false
        }
        SimplStmt::Require(..) => false,
        SimplStmt::PostCondition(..) => false,
        SimplStmt::Assert(..) => true,
        SimplStmt::Assign(..) => false,
    }
}
