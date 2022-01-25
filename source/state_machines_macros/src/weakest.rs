#![allow(unused_imports)]

use crate::parse_token_stream::{MaybeSM, SMAndFuncs};
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
use crate::transitions::{add_noop_updates, replace_updates};

pub fn to_weakest(
    sm: &SM<Span, Ident, ImplItemMethod, Expr, Type>,
    trans: &Transition<Span, Ident, Expr, Type>
) -> TokenStream {
    let ts = add_noop_updates(sm, &trans.body);
    let ts = replace_updates(&ts);
    match to_weakest_rec(&ts, None) {
        Some(e) => e,
        None => quote! { true },
    }
}

fn to_weakest_rec(trans: &TransitionStmt<Span, Ident, Expr>, p: Option<TokenStream>) -> Option<TokenStream> {
    match trans {
        TransitionStmt::Block(span, v) => {
            let mut p = p;
            for e in v.iter().rev() {
                p = to_weakest_rec(e, p);
            }
            p
        }
        TransitionStmt::Let(span, id, e) => {
            match p {
                None => None,
                Some(r) => {
                    Some(quote! { let #id = #e; #r })
                }
            }
        }
        TransitionStmt::If(span, cond, e1, e2) => {
            match p {
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
            }
        }
        TransitionStmt::Require(span, e) => {
            match p {
                None => Some(quote! { (#e) }),
                Some(r) => Some(quote! { ((#e) && #r) }),
            }
        }
        TransitionStmt::Assert(span, e) => {
            match p {
                None => None,
                Some(r) => Some(quote! { ((#e) >>= #r) }),
            }
        }
        TransitionStmt::Update(span, id, e) => {
            panic!("should have been removed in pre-processing step");
        }
    }
}
