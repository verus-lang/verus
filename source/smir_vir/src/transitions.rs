#![allow(unused_imports)]

use crate::util::fields_contain;
use air::ast::Span;
use air::errors::{error, error_with_label};
use smir::ast::{
    Field, Invariant, Lemma, LemmaPurpose, LemmaPurposeKind, ShardableType, Transition,
    TransitionKind, TransitionStmt, SM,
};
use std::collections::HashMap;
use std::collections::HashSet;
use std::ops::Index;
use std::sync::Arc;
use vir::ast::{
    CallTarget, Expr, ExprX, Function, FunctionX, Ident, KrateX, Mode, Path, PathX, Typ, TypX,
    VirErr,
};
use vir::ast_util::{conjoin, mk_and, mk_call, mk_ife, mk_implies, mk_let_in, mk_or, mk_var};

fn check_updates_refer_to_valid_fields(
    fields: &Vec<Field<Ident, Typ>>,
    ts: &TransitionStmt<Span, Ident, Expr>,
) -> Result<(), VirErr> {
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
                return Err(error(format!("field '{}' not found", *f), &sp));
            }
            Ok(())
        }
    }
}

fn check_readonly(ts: &TransitionStmt<Span, Ident, Expr>) -> Result<(), VirErr> {
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
            return Err(error("'update' statement not allowed in readonly transitions", &sp));
        }
    }
}

fn disjoint_union(
    h1: &Vec<(Ident, Span)>,
    h2: &Vec<(Ident, Span)>,
) -> Result<Vec<(Ident, Span)>, VirErr> {
    let mut h1_map: HashMap<Ident, Span> = HashMap::new();
    for (ident, span) in h1 {
        h1_map.insert(ident.clone(), span.clone());
    }
    for (ident, span2) in h2 {
        match h1_map.get(ident) {
            None => {}
            Some(span1) => {
                return Err(error_with_label(
                    format!("field '{}' might be updated multiple times", *ident),
                    &span1,
                    "updated here",
                )
                .primary_label(&span2, "updated here"));
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
    sp: &Span,
    h: &Vec<(Ident, Span)>,
    fields: &Vec<Field<Ident, Typ>>,
) -> Result<(), VirErr> {
    for field in fields {
        if !update_set_contains(h, &field.ident) {
            return Err(error(
                format!("onitialization does not initialize field {}", *field.ident),
                &sp,
            ));
        }
    }
    Ok(())
}

fn check_init(ts: &TransitionStmt<Span, Ident, Expr>) -> Result<Vec<(Ident, Span)>, VirErr> {
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
                let mut e = error(
                    "for initialization, both branches of if-statement must update the same fields",
                    &sp,
                );
                for (ident, sp) in &h1 {
                    if !update_set_contains(&h2, ident) {
                        e = e.primary_label(
                            &sp,
                            format!("only the first branch updates {}", *ident),
                        );
                    }
                }
                for (ident, sp) in &h2 {
                    if !update_set_contains(&h1, ident) {
                        e = e.primary_label(
                            &sp,
                            format!("only the second branch updates {}", *ident),
                        );
                    }
                }

                return Err(e);
            }
            return Ok(h1);
        }
        TransitionStmt::Require(_, _) => {
            return Ok(Vec::new());
        }
        TransitionStmt::Assert(sp, _) => {
            return Err(error("'assert' statement not allowed in initialization", &sp));
        }
        TransitionStmt::Update(sp, ident, _) => {
            let mut v = Vec::new();
            v.push((ident.clone(), sp.clone()));
            return Ok(v);
        }
    }
}

pub fn check_normal(ts: &TransitionStmt<Span, Ident, Expr>) -> Result<Vec<(Ident, Span)>, VirErr> {
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

pub fn check_transitions(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    fun_map: &HashMap<Ident, Function>,
) -> Result<(), VirErr> {
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
                let span = &fun_map.index(&tr.name).span;
                check_has_all_fields(span, &h, &sm.fields)?;
            }
        }
    }

    Ok(())
}

pub fn expr_is_enabled(
    ts: &TransitionStmt<Span, Ident, Expr>,
    include_asserts: bool,
    include_requires: bool,
) -> Option<Expr> {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut e: Option<Expr> = None;
            for t in v.iter().rev() {
                match t {
                    TransitionStmt::Let(let_span, let_bind, let_e) => match e {
                        None => {}
                        Some(e2) => {
                            e = Some(mk_let_in(let_span, Mode::Spec, false, let_bind, let_e, &e2));
                        }
                    },
                    _ => {
                        let e1 = expr_is_enabled(t, include_asserts, include_requires);
                        e = match (e1, e) {
                            (None, None) => None,
                            (None, Some(e)) => Some(e),
                            (Some(e), None) => Some(e),
                            (Some(e1), Some(e2)) => Some(mk_and(span, e1, &e2)),
                        };
                    }
                }
            }
            e
        }
        TransitionStmt::Let(_, _, _) => {
            None /* see previous case */
        }
        TransitionStmt::If(span, cond, thn, els) => {
            let e1 = expr_is_enabled(thn, include_asserts, include_requires);
            let e2 = expr_is_enabled(els, include_asserts, include_requires);
            match (e1, e2) {
                (None, None) => None,
                (Some(e), None) => Some(mk_implies(span, &cond, &e)),
                (None, Some(e)) => Some(mk_or(span, &cond, &e)),
                (Some(e1), Some(e2)) => Some(mk_ife(span, &cond, &e1, &e2)),
            }
        }
        TransitionStmt::Require(_, e) => {
            if include_requires {
                Some(e.clone())
            } else {
                None
            }
        }
        TransitionStmt::Assert(_, e) => {
            if include_asserts {
                Some(e.clone())
            } else {
                None
            }
        }
        TransitionStmt::Update(sp, f, _) => None,
    }
}
