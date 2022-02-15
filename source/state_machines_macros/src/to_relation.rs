#![allow(unused_imports)]

use crate::ast::{
    Extras, Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind,
    TransitionStmt, SM,
};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Colon2;
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, FieldsNamed, FnArg, Ident, ImplItemMethod, Meta,
    MetaList, NestedMeta, Path, PathArguments, PathSegment, Type,
};

// Converts a transition description into a relation between `self` and `post`.
// We proceed in two steps.
//
// 1. Process and remove all 'update' statements (`add_noop_updates` and `replace_updates`).
// 2. Walk the tree and straightforwardly convert it to a relation.
// 
// There are actually two different relations we can form, the "weak" relation and
// the "strong" one.
//
// These differ only in how they handle "assert" statements. (Thus if there are no assert
// statements, then the two versions are the same.) In short, the 'strong' version treats
// an 'assert' like it does any other enabling condition, while the 'weak' version puts
// the 'asserts' on the _left_ side of the implication.
//
// For example, consider a transition like,
//
//   require(A);
//   assert(B);
//   require(C);
//
// Then the weak relation would become
//
//   A && (B ==> C)
//
// While the strong relation would become simply,
//
//   A && B && C
//
// Note that we require the user to prove that any asserts follow from the invariant.
// (In this case, that means showing that (Inv && A ==> B).
// Thus, subject to the invariant, the weak & strong versions will actually be equivalent.

pub fn to_relation(sm: &SM, trans: &Transition, weak: bool) -> TokenStream {
    let ts = add_noop_updates(sm, &trans.body);
    let ts = replace_updates(&ts);
    match to_relation_rec(&ts, None, weak) {
        Some(e) => e,
        None => quote! { true },
    }
}

fn to_relation_rec(trans: &TransitionStmt, p: Option<TokenStream>, weak: bool) -> Option<TokenStream> {
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
        },
        TransitionStmt::Update(_span, _id, _e) => {
            panic!("should have been removed in pre-processing step");
        }
    }
}

// Turns implicit updates into explicit 'update' statements.
//
//  - For any field `f` which is not updated at all, add an `update(f, self.f)`
//    statement at the root node of the transition AST.
//  - For any field `f` which is updated in one branch of a conditional, but not the other,
//    add a trivial update statement

fn add_noop_updates(sm: &SM, ts: &TransitionStmt) -> TransitionStmt {
    let (mut ts, idents) = add_noop_updates_rec(ts);
    for f in &sm.fields {
        if !idents.contains(&f.ident) {
            let span = ts.get_span().clone();
            let ident = &f.ident;
            ts = append_stmt_front(
                ts,
                TransitionStmt::Update(span, f.ident.clone(), Expr::Verbatim(quote!{ self.#ident })),
            );
        }
    }
    return ts;
}

fn add_noop_updates_rec(ts: &TransitionStmt) -> (TransitionStmt, Vec<Ident>) {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut h = Vec::new();
            let mut v1 = Vec::new();
            for t in v.iter() {
                let (t1, q) = add_noop_updates_rec(t);
                v1.push(t1);
                h.extend(q)
            }
            (TransitionStmt::Block(span.clone(), v1), h)
        }
        TransitionStmt::Let(_, _, _)
        | TransitionStmt::Require(_, _)
        | TransitionStmt::Assert(_, _) => {
            return (ts.clone(), Vec::new());
        }
        TransitionStmt::If(span, cond, thn, els) => {
            let (mut s1, h1) = add_noop_updates_rec(thn);
            let (mut s2, h2) = add_noop_updates_rec(els);

            for ident in &h1 {
                if !h2.contains(ident) {
                    s1 = append_stmt_front(
                        s1,
                        TransitionStmt::Update(
                            span.clone(),
                            ident.clone(),
                            Expr::Verbatim(quote!{ self.#ident }),
                        ),
                    );
                }
            }
            let mut union = h1.clone();
            for ident in &h2 {
                if !h1.contains(ident) {
                    s2 = append_stmt_front(
                        s2,
                        TransitionStmt::Update(
                            span.clone(),
                            ident.clone(),
                            Expr::Verbatim(quote!{ self.#ident }),
                        ),
                    );
                    union.push(ident.clone());
                }
            }

            return (
                TransitionStmt::If(span.clone(), cond.clone(), Box::new(s1), Box::new(s2)),
                union,
            );
        }
        TransitionStmt::Update(_, ident, _) => {
            return (ts.clone(), vec![ident.clone()]);
        }
    }
}

fn append_stmt_front(t1: TransitionStmt, t2: TransitionStmt) -> TransitionStmt {
    match t1 {
        TransitionStmt::Block(span, mut v) => {
            let mut w: Vec<TransitionStmt> = vec![t2];
            w.append(&mut v);
            TransitionStmt::Block(span, w)
        }
        _ => TransitionStmt::Block(t1.get_span().clone(), vec![t2, t1]),
    }
}

// Turn all 'update' statements into ordinary enabling conditions like:
//
//        update(f, x)      -->       require(post.f == x)
//
// Note that ordinary, user-defined 'require' statements wouldn't have been allowed
// to reference `post`.

pub fn replace_updates(ts: &TransitionStmt) -> TransitionStmt {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut h = Vec::new();
            for t in v.iter() {
                let q = replace_updates(t);
                h.push(q);
            }
            TransitionStmt::Block(*span, h)
        }
        TransitionStmt::Let(_, _, _) => ts.clone(),
        TransitionStmt::If(span, cond, thn, els) => {
            let t1 = replace_updates(thn);
            let t2 = replace_updates(els);
            TransitionStmt::If(*span, cond.clone(), Box::new(t1), Box::new(t2))
        }
        TransitionStmt::Require(_, _) => ts.clone(),
        TransitionStmt::Assert(_, _) => ts.clone(),
        TransitionStmt::Update(span, ident, e) => TransitionStmt::Require(
            *span,
            Expr::Verbatim(quote!{ ::builtin::equal(post.#ident, #e) })
        ),
    }
}
