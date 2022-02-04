#![allow(unused_imports)]

/*
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
    CallTarget, Expr, ExprX, Function, FunctionX, Ident, KrateX, Mode, Path, PathX, SpannedTyped,
    Stmt, Typ, TypX, VirErr,
};
use vir::ast_util::{
    conjoin, mk_and, mk_assert, mk_assume, mk_block, mk_bool, mk_call, mk_decl_stmt, mk_eq,
    mk_expr_stmt, mk_field, mk_ife, mk_implies, mk_or, mk_var,
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

fn append_stmt(
    t1: TransitionStmt<Span, Ident, Expr>,
    t2: TransitionStmt<Span, Ident, Expr>,
) -> TransitionStmt<Span, Ident, Expr> {
    match t1 {
        TransitionStmt::Block(span, mut v) => {
            v.push(t2);
            TransitionStmt::Block(span, v)
        }
        _ => TransitionStmt::Block(t1.get_span().clone(), vec![t1, t2]),
    }
}

fn self_dot_ident(ident: Ident) -> Expr {
    unimplemented!();
}

fn add_noop_updates(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    ts: &TransitionStmt<Span, Ident, Expr>,
) -> TransitionStmt<Span, Ident, Expr> {
    let (mut ts, idents) = add_noop_updates_rec(ts);
    for f in &sm.fields {
        if !idents.contains(&f.ident) {
            let span = ts.get_span().clone();
            ts = append_stmt(
                ts,
                TransitionStmt::Update(span, f.ident.clone(), self_dot_ident(f.ident.clone())),
            );
        }
    }
    return ts;
}

fn add_noop_updates_rec(
    ts: &TransitionStmt<Span, Ident, Expr>,
) -> (TransitionStmt<Span, Ident, Expr>, Vec<Ident>) {
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

            return (
                TransitionStmt::If(span.clone(), cond.clone(), Box::new(s1), Box::new(s2)),
                union,
            );
        }
        TransitionStmt::Update(sp, ident, _) => {
            return (ts.clone(), vec![ident.clone()]);
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

fn transition_to_vir_stmt(
    ts: &TransitionStmt<Span, Ident, Expr>,
    assume_asserts: bool,
    post_expr: Option<&Expr>,
) -> Stmt {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut res: Vec<Stmt> = Vec::new();
            for t in v {
                res.push(transition_to_vir_stmt(t, assume_asserts, post_expr));
            }
            mk_expr_stmt(span, &mk_block(span, res, &None))
        }
        TransitionStmt::Let(let_span, let_bind, let_e) => {
            mk_decl_stmt(let_span, Mode::Spec, false, let_bind, let_e)
        }
        TransitionStmt::If(span, cond, thn, els) => {
            let e1 = transition_to_vir_stmt(thn, assume_asserts, post_expr);
            let e2 = transition_to_vir_stmt(els, assume_asserts, post_expr);
            let s1 = mk_block(&e1.span, vec![e1.clone()], &None);
            let s2 = mk_block(&e2.span, vec![e2.clone()], &None);
            mk_expr_stmt(span, &mk_ife(span, &cond, &s1, &s2))
        }
        TransitionStmt::Require(span, e) => mk_expr_stmt(span, &mk_assume(span, e)),
        TransitionStmt::Assert(span, e) => {
            if assume_asserts {
                mk_expr_stmt(span, &mk_assume(span, e))
            } else {
                mk_expr_stmt(span, &mk_assert(span, e))
            }
        }
        TransitionStmt::Update(span, f, expr) => {
            let e = match post_expr {
                None => mk_bool(span, true),
                Some(post_expr) => {
                    let typ = &expr.typ;
                    let field_access = mk_field(span, post_expr, f, typ);
                    mk_assume(span, &mk_eq(span, Mode::Spec, &field_access, expr))
                }
            };
            mk_expr_stmt(span, &e)
        }
    }
}

pub fn assume_transition_holds(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    ts: &TransitionStmt<Span, Ident, Expr>,
    type_path: &Path,
    post_ident: &Ident,
) -> Stmt {
    let var_ty = Arc::new(TypX::Datatype(type_path.clone(), Arc::new(Vec::new())));
    let var_for_ident = SpannedTyped::new(ts.get_span(), &var_ty, ExprX::Var(post_ident.clone()));

    let ts = add_noop_updates(sm, ts);
    return transition_to_vir_stmt(&ts, true, Some(&var_for_ident));
}
*/
