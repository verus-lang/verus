#![allow(unused_imports)]

use crate::ast::{
    Extras, Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind,
    TransitionStmt, SM,
};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use std::collections::HashMap;
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::{Colon2, Dot, Paren};
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, ExprCall, ExprField, ExprPath, FieldsNamed, FnArg,
    Ident, ImplItemMethod, Member, Meta, MetaList, NestedMeta, Path, PathArguments, PathSegment,
    Type,
};

pub fn fields_contain(fields: &Vec<Field>, ident: &Ident) -> bool {
    for f in fields {
        if f.ident.to_string() == ident.to_string() {
            return true;
        }
    }
    return false;
}

fn check_updates_refer_to_valid_fields(
    fields: &Vec<Field>,
    ts: &TransitionStmt,
) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_updates_refer_to_valid_fields(fields, t)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_, _, _) => Ok(()),
        TransitionStmt::If(_, _, thn, els) => {
            check_updates_refer_to_valid_fields(fields, thn)?;
            check_updates_refer_to_valid_fields(fields, els)?;
            Ok(())
        }
        TransitionStmt::Require(_, _) => Ok(()),
        TransitionStmt::Assert(_, _) => Ok(()),
        TransitionStmt::Update(sp, f, _) => {
            if !fields_contain(fields, f) {
                return Err(Error::new(sp.span(), format!("field '{}' not found", f.to_string())));
            }
            Ok(())
        }
    }
}

fn check_readonly(ts: &TransitionStmt) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_readonly(t)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_, _, _) => Ok(()),
        TransitionStmt::If(_, _, thn, els) => {
            check_readonly(thn)?;
            check_readonly(els)?;
            Ok(())
        }
        TransitionStmt::Require(_, _) => Ok(()),
        TransitionStmt::Assert(_, _) => Ok(()),
        TransitionStmt::Update(sp, _, _) => {
            return Err(Error::new(*sp, "'update' statement not allowed in readonly transitions"));
        }
    }
}

fn disjoint_union(
    h1: &Vec<(Ident, Span)>,
    h2: &Vec<(Ident, Span)>,
) -> syn::parse::Result<Vec<(Ident, Span)>> {
    let mut h1_map: HashMap<Ident, Span> = HashMap::new();
    for (ident, span) in h1 {
        h1_map.insert(ident.clone(), span.clone());
    }
    for (ident, _span2) in h2 {
        match h1_map.get(ident) {
            None => {}
            Some(span1) => {
                return Err(Error::new(
                    *span1,
                    format!("field '{}' might be updated multiple times", ident.to_string()),
                ));
            }
        }
    }
    let mut con = h1.clone();
    con.extend(h2.clone());
    return Ok(con);
}

fn update_sets_eq(h1: &Vec<(Ident, Span)>, h2: &Vec<(Ident, Span)>) -> bool {
    if h1.len() != h2.len() {
        return false;
    }
    for (ident, _) in h1 {
        if !update_set_contains(h2, ident) {
            return false;
        }
    }
    return true;
}

fn update_set_contains(h: &Vec<(Ident, Span)>, ident: &Ident) -> bool {
    for (ident2, _) in h {
        if *ident == *ident2 {
            return true;
        }
    }
    return false;
}

fn simple_union(h1: Vec<(Ident, Span)>, h2: Vec<(Ident, Span)>) -> Vec<(Ident, Span)> {
    let mut h = h1;
    for (ident, span) in h2 {
        if !update_set_contains(&h, &ident) {
            h.push((ident, span));
        }
    }
    return h;
}

fn check_has_all_fields(
    sp: Span,
    h: &Vec<(Ident, Span)>,
    fields: &Vec<Field>,
) -> syn::parse::Result<()> {
    for field in fields {
        if !update_set_contains(h, &field.ident) {
            return Err(Error::new(
                sp,
                format!(
                    "itialization procedure does not initialize field {}",
                    field.ident.to_string()
                ),
            ));
        }
    }
    Ok(())
}

fn check_init(ts: &TransitionStmt) -> syn::parse::Result<Vec<(Ident, Span)>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut h = Vec::new();
            for t in v.iter() {
                let q = check_init(t)?;
                h = disjoint_union(&h, &q)?;
            }
            Ok(h)
        }
        TransitionStmt::Let(_, _, _) => {
            return Ok(Vec::new());
        }
        TransitionStmt::If(sp, _, thn, els) => {
            let h1 = check_init(thn)?;
            let h2 = check_init(els)?;
            if !update_sets_eq(&h1, &h2) {
                return Err(Error::new(
                    *sp,
                    "for initialization, both branches of if-statement must update the same fields",
                ));
            }
            return Ok(h1);
        }
        TransitionStmt::Require(_, _) => {
            return Ok(Vec::new());
        }
        TransitionStmt::Assert(sp, _) => {
            return Err(Error::new(*sp, "'assert' statement not allowed in initialization"));
        }
        TransitionStmt::Update(sp, ident, _) => {
            let mut v = Vec::new();
            v.push((ident.clone(), sp.clone()));
            return Ok(v);
        }
    }
}

pub fn check_normal(ts: &TransitionStmt) -> syn::parse::Result<Vec<(Ident, Span)>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut h = Vec::new();
            for t in v.iter() {
                let q = check_normal(t)?;
                h = disjoint_union(&h, &q)?;
            }
            Ok(h)
        }
        TransitionStmt::Let(_, _, _) => {
            return Ok(Vec::new());
        }
        TransitionStmt::If(_, _, thn, els) => {
            let h1 = check_normal(thn)?;
            let h2 = check_normal(els)?;
            return Ok(simple_union(h1, h2));
        }
        TransitionStmt::Require(_, _) => {
            return Ok(Vec::new());
        }
        TransitionStmt::Assert(_, _) => {
            return Ok(Vec::new());
        }
        TransitionStmt::Update(sp, ident, _) => {
            let mut h = Vec::new();
            h.push((ident.clone(), sp.clone()));
            return Ok(h);
        }
    }
}

pub fn check_transitions(sm: &SM) -> syn::parse::Result<()> {
    for tr in &sm.transitions {
        check_updates_refer_to_valid_fields(&sm.fields, &tr.body)?;

        match &tr.kind {
            TransitionKind::Readonly => {
                check_readonly(&tr.body)?;
            }
            TransitionKind::Transition => {
                check_normal(&tr.body)?;
            }
            TransitionKind::Init => {
                let h = check_init(&tr.body)?;
                let span = tr.body.get_span();
                check_has_all_fields(*span, &h, &sm.fields)?;
            }
        }
    }

    Ok(())
}



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
        TransitionStmt::Let(span, id, v) => Some(Expr::Verbatim(quote_spanned! {*span =>
            let #id = #v;
        })),
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
                    if !(#cond) {
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
        TransitionStmt::Assert(span, e) => Some(Expr::Verbatim(quote_spanned! {*span =>
            crate::pervasive::assert(#e);
        })),
        TransitionStmt::Update(_span, _ident, _e) => None,
    }
}

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
        TransitionStmt::Let(_, _, _) => false,
        TransitionStmt::If(_span, _cond, thn, els) => has_any_assert(thn) || has_any_assert(els),
        TransitionStmt::Require(_, _) => false,
        TransitionStmt::Assert(_, _) => true,
        TransitionStmt::Update(_, _, _) => false,
    }
}
