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
    match to_relation_rec(&ts, None, weak) {
        Some(e) => e,
        None => quote! { true },
    }
}

// Recursive traversal, post-order.

fn to_relation_rec(
    trans: &TransitionStmt,
    p: Option<TokenStream>,
    weak: bool,
) -> Option<TokenStream> {
    match trans {
        TransitionStmt::Block(_span, v) => {
            let mut p = p;
            for e in v.iter().rev() {
                p = to_relation_rec(e, p, weak);
            }
            p
        }
        TransitionStmt::Let(_span, id, e) => match p {
            None => None,
            Some(r) => Some(quote! { { let #id = #e; #r } }),
        },
        TransitionStmt::If(_span, cond, e1, e2) => match p {
            None => {
                let x1 = to_relation_rec(e1, None, weak);
                let x2 = to_relation_rec(e2, None, weak);
                match (x1, x2) {
                    (None, None) => None,
                    (Some(e1), None) => Some(quote! { ((#cond) >>= #e1) }),
                    (None, Some(e2)) => Some(quote! { (!(#cond) >>= #e2) }),
                    (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
                }
            }
            Some(_e) => {
                panic!("not implemented");
            }
        },
        TransitionStmt::PostCondition(_span, e) |
        TransitionStmt::Require(_span, e) => match p {
            None => Some(quote! { (#e) }),
            Some(r) => Some(quote! { ((#e) && #r) }),
        },
        TransitionStmt::Assert(_span, e) => {
            if weak {
                match p {
                    None => None,
                    Some(r) => Some(quote! { ((#e) >>= #r) }),
                }
            } else {
                match p {
                    None => Some(quote! { (#e) }),
                    Some(r) => Some(quote! { ((#e) && #r) }),
                }
            }
        }
        TransitionStmt::Initialize(_, _, _)
        | TransitionStmt::Update(_, _, _)
        | TransitionStmt::Special(_, _, _) => {
            panic!("should have been removed in pre-processing step");
        }
    }
}
