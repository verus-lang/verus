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
use vir::ast_util::{
    conjoin, mk_and, mk_bool, mk_call, mk_ife, mk_implies, mk_let_in, mk_or, mk_var,
};

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

pub fn add_noop_updates_rec(
    ts: &TransitionStmt<Span, Ident, Expr>,
) -> (TransitionStmt<Span, Ident, Expr>, Vec<Ident>) {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut h = Vec::new();
            let mut v1 = Vec::new();
            for t in v.iter() {
                let (t1, q) = check_normal(t)?;
                v1.push(t1);
                h.extend(q)
            }
            Ok((TransitionStmt::Block(span.clone(), v1), h))
        }
        TransitionStmt::Let(_, _, _)
        | TransitionStmt::Require(_, _)
        | TransitionStmt::Assert(_, _) => {
            return Ok((ts.clone(), Vec::new()));
        }
        TransitionStmt::If(span, cond, thn, els) => {
            let (mut s1, h1) = check_normal(thn)?;
            let (mut s2, h2) = check_normal(els)?;

            for ident in &h1 {
                if !h2.contains(ident) {
                    s1 = append_stmt(
                        s1,
                        TransitionStmt::Update(
                            span.clone(),
                            ident.clone(),
                            self_dot_ident(ident.clone()),
                        ),
                    );
                }
            }
            let mut union = h1.clone();
            for ident in &h2 {
                if !h1.contains(ident) {
                    s2 = append_stmt(
                        s2,
                        TransitionStmt::Update(
                            span.clone(),
                            ident.clone(),
                            self_dot_ident(ident.clone()),
                        ),
                    );
                    union.push(ident.clone());
                }
            }

            return Ok((TransitionStmt::If(span, cond, s1, s2), union));
        }
        TransitionStmt::Update(sp, ident, _) => {
            return Ok((ts.clone(), vec![ident]));
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
) -> Expr {
    match expr_is_enabled_opt(ts, include_asserts, include_requires) {
        Some(e) => e,
        None => mk_bool(ts.get_span(), true),
    }
}

pub fn transition_to_vir_stmt(
    ts: &TransitionStmt<Span, Ident, Expr>,
    post_ident: Option<Ident>,
) -> Stmt {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut res: Vec<Stmt> = Vec::new();
            for t in v {
                res.push(transition_to_vir_stmt(t, assume_asserts, post_ident));
            }
            mk_expr_stmt(span, mk_block(span, res, None))
        }
        TransitionStmt::Let(let_span, let_bind, let_e) => match e {
            None => None,
            Some(e) => mk_decl_statement(let_span, Mode::Spec, false, let_bind, let_e),
        },
        TransitionStmt::If(span, cond, thn, els) => {
            let e1 = transition_to_vir_stmt(thn, assume_asserts, post_ident);
            let e2 = transition_to_vir_stmt(els, assume_asserts, post_ident);
            mk_expr_stmt(span, mk_ife(span, &cond, &e1, &e2))
        }
        TransitionStmt::Require(span, e) => mk_assume(span, e),
        TransitionStmt::Assert(_, e) => {
            if assume_asserts {
                mk_assume(span, e)
            } else {
                mk_assert(span, e)
            }
        }
        TransitionStmt::Update(span, f, expr) => match post_ident {
            None => mk_bool(span, true),
            Some(post_ident) => mk_assume(span, mk_eq(span, mk_var(span, typ, *f), expr)),
        },
    }
}
