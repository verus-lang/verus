#![allow(unused_imports)]

use crate::parse_token_stream::{MaybeSM, SMAndFuncs};
use crate::transitions::{add_noop_updates, replace_updates};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use smir::ast::{
    Extras, Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind,
    TransitionStmt, SM,
};
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Colon2;
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, FieldsNamed, FnArg, Ident, ImplItemMethod, Meta,
    MetaList, NestedMeta, Path, PathArguments, PathSegment, Type,
};

pub fn to_weakest(
    sm: &SM<Span, Ident, ImplItemMethod, Expr, Type>,
    trans: &Transition<Span, Ident, Expr, Type>,
) -> TokenStream {
    let ts = add_noop_updates(sm, &trans.body);
    let ts = replace_updates(&ts);
    match to_weakest_rec(&ts, None) {
        Some(e) => e,
        None => quote! { true },
    }
}

fn to_weakest_rec(
    trans: &TransitionStmt<Span, Ident, Expr>,
    p: Option<TokenStream>,
) -> Option<TokenStream> {
    match trans {
        TransitionStmt::Block(span, v) => {
            let mut p = p;
            for e in v.iter().rev() {
                p = to_weakest_rec(e, p);
            }
            p
        }
        TransitionStmt::Let(span, id, e) => match p {
            None => None,
            Some(r) => Some(quote! { { let #id = #e; #r } }),
        },
        TransitionStmt::If(span, cond, e1, e2) => match p {
            None => {
                let x1 = to_weakest_rec(e1, None);
                let x2 = to_weakest_rec(e2, None);
                match (x1, x2) {
                    (None, None) => None,
                    (Some(e1), None) => Some(quote! { ((#cond) >>= e1) }),
                    (None, Some(e2)) => Some(quote! { (!(#cond) >>= e2) }),
                    (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
                }
            }
            Some(e) => {
                panic!("not implemented");
            }
        },
        TransitionStmt::Require(span, e) => match p {
            None => Some(quote! { (#e) }),
            Some(r) => Some(quote! { ((#e) && #r) }),
        },
        TransitionStmt::Assert(span, e) => match p {
            None => None,
            Some(r) => Some(quote! { ((#e) >>= #r) }),
        },
        TransitionStmt::Update(span, id, e) => {
            panic!("should have been removed in pre-processing step");
        }
    }
}

pub fn get_safety_conditions(ts: &TransitionStmt<Span, Ident, Expr>) -> Vec<TokenStream> {
    let v = get_safety_conditions_ts(ts);
    v.iter()
        .map(|ts| match to_weakest_rec(&ts, None) {
            Some(e) => e,
            None => quote! { true },
        })
        .collect()
}

fn get_safety_conditions_ts(
    ts: &TransitionStmt<Span, Ident, Expr>,
) -> Vec<TransitionStmt<Span, Ident, Expr>> {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut res: Vec<TransitionStmt<Span, Ident, Expr>> = Vec::new();
            let mut prefix: Vec<TransitionStmt<Span, Ident, Expr>> = Vec::new();
            for t in v {
                let suffs = get_safety_conditions_ts(t);
                res.append(
                    &mut suffs
                        .iter()
                        .map(|suff| {
                            let mut x = prefix.clone();
                            x.push(suff.clone());
                            TransitionStmt::Block(*span, x)
                        })
                        .collect(),
                );
                prefix.push(to_asserts(t));
            }
            res
        }
        TransitionStmt::Let(_span, _id, _e) => Vec::new(),
        TransitionStmt::If(span, cond, e1, e2) => {
            let v1 = get_safety_conditions_ts(e1);
            let v2 = get_safety_conditions_ts(e2);
            let mut m: Vec<TransitionStmt<Span, Ident, Expr>> = v1
                .iter()
                .map(|t| {
                    TransitionStmt::If(
                        *span,
                        cond.clone(),
                        Box::new(t.clone()),
                        Box::new(TransitionStmt::Block(*span, Vec::new())),
                    )
                })
                .collect();
            m.append(
                &mut v2
                    .iter()
                    .map(|t| {
                        TransitionStmt::If(
                            *span,
                            cond.clone(),
                            Box::new(TransitionStmt::Block(*span, Vec::new())),
                            Box::new(t.clone()),
                        )
                    })
                    .collect(),
            );
            m
        }
        TransitionStmt::Require(_span, _e) => Vec::new(),
        TransitionStmt::Assert(span, e) => {
            vec![TransitionStmt::Require(*span, e.clone())]
        }
        TransitionStmt::Update(span, _id, _e) => Vec::new(),
    }
}

fn to_asserts(ts: &TransitionStmt<Span, Ident, Expr>) -> TransitionStmt<Span, Ident, Expr> {
    match ts {
        TransitionStmt::Block(span, v) => {
            TransitionStmt::Block(*span, v.iter().map(|t| to_asserts(t)).collect())
        }
        TransitionStmt::Let(_span, _id, _e) => ts.clone(),
        TransitionStmt::If(span, cond, e1, e2) => TransitionStmt::If(
            *span,
            cond.clone(),
            Box::new(to_asserts(e1)),
            Box::new(to_asserts(e2)),
        ),
        TransitionStmt::Require(span, e) => TransitionStmt::Assert(*span, e.clone()),
        TransitionStmt::Assert(_span, _e) => ts.clone(),
        TransitionStmt::Update(span, _id, _e) => TransitionStmt::Block(*span, Vec::new()),
    }
}
