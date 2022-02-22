use crate::ast::{TransitionStmt, SM};
use proc_macro2::Span;
use std::collections::HashMap;
use syn::{Expr, Ident};
use quote::quote;
use proc_macro2::TokenStream;

/// Simplify out `update' statements, including `add_element` etc.

pub fn simplify_updates(sm: &SM, ts: &TransitionStmt) -> TransitionStmt {
    let ts = add_finalizes(sm, ts);

    let mut field_map = HashMap::new();
    for field in &sm.fields {
        let ident = &field.ident;
        field_map.insert(ident.to_string(),
            Expr::Verbatim(quote!{ self.#ident }));
    }

    let (ts, _field_map) = simplify_updates_rec(&ts, field_map);

    ts
}

fn simplify_updates_rec(ts: &TransitionStmt, field_map: HashMap<String, Expr>)
    -> (TransitionStmt, HashMap<String, Expr>)
{
    if is_finalize_stmt(ts) {
        let (span, f) = match ts {
            TransitionStmt::Update(span, f, _) => (span, f),
            _ => panic!("shouldn't get here"),
        };
        let e = &field_map[&f.to_string()];
        let ts = TransitionStmt::Require(*span, Expr::Verbatim(quote!{
            ::builtin::equal(post.#f, #e)
        }));
        return (ts, field_map);
    }

    match ts {
        TransitionStmt::Block(span, v) => {
            let mut field_map = field_map;
            let mut res = Vec::new();
            for t in v {
                let (t, fm) = simplify_updates_rec(t, field_map);
                field_map = fm;
                res.push(t);
            }
            (TransitionStmt::Block(*span, res), field_map)
        }
        TransitionStmt::Let(_, _, _) => {
            (ts.clone(), field_map)
        }
        TransitionStmt::If(_, _, _, _) => {
            panic!("unimpl");
        }
        TransitionStmt::Require(_, _) => {
            (ts.clone(), field_map)
        }
        TransitionStmt::Assert(_, _) => {
            (ts.clone(), field_map)
        }

        TransitionStmt::HaveElement(span, f, e) => {
            let cur = &field_map[&f.to_string()];
            let safety = Expr::Verbatim(quote!{
                (#cur).count(#e) >= 1
            });
            (TransitionStmt::Assert(*span, safety), field_map)
        }
        TransitionStmt::Update(span, f, e) => {
            let mut field_map = field_map;
            field_map.insert(f.to_string(), e.clone());
            (TransitionStmt::Block(*span, Vec::new()), field_map)
        }
        TransitionStmt::AddElement(span, f, e) => {
            let mut field_map = field_map;
            let cur = field_map[&f.to_string()].clone();
            field_map.insert(f.to_string(), Expr::Verbatim(quote!{
                (#cur).insert(#e)
            }));
            (TransitionStmt::Block(*span, Vec::new()), field_map)
        }
        TransitionStmt::RemoveElement(span, f, e) => {
            let mut field_map = field_map;
            let cur = field_map[&f.to_string()].clone();
            field_map.insert(f.to_string(), Expr::Verbatim(quote!{
                (#cur).remove(#e)
            }));
            let safety = Expr::Verbatim(quote!{
                (#cur).count(#e) >= 1
            });
            (TransitionStmt::Assert(*span, safety), field_map)
        }
    }
}

/// add_finalizes

fn add_finalizes(sm: &SM, ts: &TransitionStmt) -> TransitionStmt {
    let mut ts = ts.clone();

    let mut found = Vec::new();
    add_finalizes_rec(&mut ts, &mut found);

    for field in &sm.fields {
        if !contains_ident(&found, &field.ident) {
            let fs = finalize_stmt(ts.get_span().clone(), field.ident.clone());
            append_stmt(&mut ts, fs);
        }
    }

    ts
}

fn add_finalizes_rec(ts: &mut TransitionStmt, found: &mut Vec<Ident>) {
    let mut is_update_for = None;
    match &ts {
        TransitionStmt::Block(_, _) => { }
        TransitionStmt::Let(_, _, _) => { }
        TransitionStmt::If(_, _, _, _) => { }
        TransitionStmt::Require(_, _) => { }
        TransitionStmt::Assert(_, _) => { }
        TransitionStmt::HaveElement(_, _, _) => { }

        TransitionStmt::Update(_, f, _) |
        TransitionStmt::AddElement(_, f, _) |
        TransitionStmt::RemoveElement(_, f, _) => {
            is_update_for = Some(f.clone());
        }
    }

    match is_update_for {
        Some(f) => {
            if !contains_ident(found, &f) {
                found.push(f.clone());
                append_stmt(ts, finalize_stmt(*ts.get_span(), f));
                return;
            }
        }
        None => { }
    }

    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter_mut().rev() {
                add_finalizes_rec(t, found);
            }
        }
        TransitionStmt::If(span, _, e1, e2) => {
            let mut found2 = found.clone();
            let idx = found.len();

            add_finalizes_rec(e1, found);
            add_finalizes_rec(e2, &mut found2);

            for i in idx .. found.len() {
                if !contains_ident(&found2, &found[i]) {
                    append_stmt(e2, finalize_stmt(*span, found[i].clone()));
                }
            }

            for i in idx .. found2.len() {
                if !contains_ident(found, &found2[i]) {
                    found.push(found2[i].clone());
                    append_stmt(e1, finalize_stmt(*span, found[i].clone()));
                }
            }
        }

        TransitionStmt::Let(_, _, _) => { }
        TransitionStmt::Require(_, _) => { }
        TransitionStmt::Assert(_, _) => { }
        TransitionStmt::HaveElement(_, _, _) => { }
        TransitionStmt::Update(_, _, _) |
        TransitionStmt::AddElement(_, _, _) |
        TransitionStmt::RemoveElement(_, _, _) => { }
    }
}

fn finalize_stmt(span: Span, f: Ident) -> TransitionStmt {
    TransitionStmt::Update(span, f, Expr::Verbatim(TokenStream::new()))
}

fn is_finalize_stmt(ts: &TransitionStmt) -> bool {
    match ts {
        TransitionStmt::Update(_, _, Expr::Verbatim(stream)) => stream.is_empty(),
        _ => false,
    }
}

fn contains_ident(v: &Vec<Ident>, id: &Ident) -> bool {
    for id0 in v {
        if id0.to_string() == id.to_string() {
            return true;
        }
    }
    return false;
}

fn append_stmt(t1: &mut TransitionStmt, t2: TransitionStmt) {
    match t1 {
        TransitionStmt::Block(_span, v) => {
            return v.push(t2);
        }
        _ => { }
    }
    *t1 = TransitionStmt::Block(t1.get_span().clone(),
        vec![
            t1.clone(), t2
        ]);
}

