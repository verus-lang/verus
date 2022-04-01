use crate::ast::TransitionStmt;
use proc_macro2::TokenStream;
use quote::quote;

/// Converts a transition description into a relation between `self` and `post`.
/// Overall, this process has two steps:
///
/// 1. Process all 'update' statements and special ops, turning them into
///    require, assert, and postcondition operations. (See `simplification.rs`.)
/// 2. Walk the tree and straightforwardly convert it to a relation.
///
/// This function performs step (2) (and it assumes that step (1) has already been applied.
/// See `simplification.rs`.)
///
/// There are actually two different relations we can form, the "weak" relation and
/// the "strong" one.
///
/// These differ only in how they handle "assert" statements. (Thus if there are no assert
/// statements, then the two versions are the same.) In short, the 'strong' version treats
/// an 'assert' like it does any other enabling condition, while the 'weak' version puts
/// the 'asserts' on the _left_ side of the implication.
///
/// For example, consider a transition like,
///
///   require(A);
///   assert(B);
///   require(C);
///
/// Then the weak relation would become
///
///   A && (B ==> C)
///
/// While the strong relation would become simply,
///
///   A && B && C
///
/// Note that we require the user to prove that any asserts follow from the invariant.
/// (In this case, that means showing that (Inv && A ==> B).
/// Thus, subject to the invariant, the weak & strong versions will actually be equivalent.

pub fn to_relation(ts: &TransitionStmt, weak: bool) -> TokenStream {
    match to_relation_rec(&ts, None, weak, false) {
        Some(e) => e,
        None => quote! { true },
    }
}

// Recursive traversal, post-order.

fn to_relation_rec(
    ts: &TransitionStmt,
    p: Option<TokenStream>,
    weak: bool,
    let_skip_brace: bool,
) -> Option<TokenStream> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut p = p;
            for e in v.iter().rev() {
                p = to_relation_rec(e, p, weak, false);
            }
            p
        }
        TransitionStmt::Let(_span, id, ty, _lk, e, child) => {
            let x = to_relation_rec(child, None, weak, true);
            let ty_tokens = match ty {
                None => TokenStream::new(),
                Some(ty) => quote! { : #ty },
            };
            let t = match x {
                None => None,
                Some(r) => {
                    if let_skip_brace {
                        Some(quote! { let #id #ty_tokens = #e; #r })
                    } else {
                        Some(quote! { { let #id #ty_tokens = #e; #r } })
                    }
                }
            };
            // note this strategy is going to be quadratic in nesting depth or something
            if weak {
                conjunct_opt(t, impl_opt(asserts_to_single_predicate(ts), p))
            } else {
                conjunct_opt(t, p)
            }
        }
        TransitionStmt::If(_span, cond, e1, e2) => {
            let x1 = to_relation_rec(e1, None, weak, false);
            let x2 = to_relation_rec(e2, None, weak, false);
            let t = match (x1, x2) {
                (None, None) => None,
                (Some(e1), None) => Some(quote! { ::builtin::imply(#cond, #e1) }),
                (None, Some(e2)) => Some(quote! { ::builtin::imply(!(#cond), #e2) }),
                (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
            };
            // note this strategy is going to be quadratic in nesting depth or something
            if weak {
                conjunct_opt(t, impl_opt(asserts_to_single_predicate(ts), p))
            } else {
                conjunct_opt(t, p)
            }
        }
        TransitionStmt::PostCondition(_span, e) | TransitionStmt::Require(_span, e) => match p {
            None => Some(quote! { (#e) }),
            Some(r) => Some(quote! { ((#e) && #r) }),
        },
        TransitionStmt::Assert(_span, e, _) => {
            if weak {
                match p {
                    None => None,
                    Some(r) => Some(quote! { ::builtin::imply(#e, #r) }),
                }
            } else {
                match p {
                    None => Some(quote! { (#e) }),
                    Some(r) => Some(quote! { ((#e) && (#r)) }),
                }
            }
        }
        TransitionStmt::Initialize(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::Special(..) => {
            panic!("should have been removed in pre-processing step");
        }
    }
}

fn conjunct_opt(a: Option<TokenStream>, b: Option<TokenStream>) -> Option<TokenStream> {
    match a {
        None => b,
        Some(x) => match b {
            None => Some(x),
            Some(y) => Some(quote! { (#x && #y) }),
        },
    }
}

fn impl_opt(a: Option<TokenStream>, b: Option<TokenStream>) -> Option<TokenStream> {
    match a {
        None => b,
        Some(x) => match b {
            None => None,
            Some(y) => Some(quote! { ::builtin::imply(#x, #y) }),
        },
    }
}

pub fn asserts_to_single_predicate(ts: &TransitionStmt) -> Option<TokenStream> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut o = None;
            for t in v {
                o = conjunct_opt(o, asserts_to_single_predicate(t));
            }
            o
        }
        TransitionStmt::Let(_span, id, ty, _, e, child) => {
            let ty_tokens = match ty {
                None => TokenStream::new(),
                Some(ty) => quote! { : #ty },
            };
            match asserts_to_single_predicate(child) {
                None => None,
                Some(r) => Some(quote! { { let #id #ty_tokens = #e; #r } }),
            }
        }
        TransitionStmt::If(_span, cond, e1, e2) => {
            let x1 = asserts_to_single_predicate(e1);
            let x2 = asserts_to_single_predicate(e2);
            match (x1, x2) {
                (None, None) => None,
                (Some(e1), None) => Some(quote! { ::builtin::imply(#cond, #e1) }),
                (None, Some(e2)) => Some(quote! { ::builtin::imply(!(#cond), #e2) }),
                (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
            }
        }
        TransitionStmt::Assert(_span, e, _) => Some(quote! { (#e) }),
        TransitionStmt::PostCondition(..)
        | TransitionStmt::Require(..)
        | TransitionStmt::Initialize(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::Special(..) => None,
    }
}
