#![allow(unused_imports)]

use crate::ast::{
    Extras, Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind,
    TransitionStmt, SM,
};
use crate::transitions::{add_noop_updates, replace_updates};
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
