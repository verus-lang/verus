#![allow(unused_imports)]

use smir::ast::{
    Field, LemmaPurpose, TransitionKind, Invariant, Lemma, Transition, ShardableType, SM,
    LemmaPurposeKind, TransitionStmt,
};
use vir::ast_util::{conjoin, mk_call, mk_var};
use vir::ast::{
    VirErr, Mode, Path, Function, FunctionX, Ident, Typ,
    PathX, TypX, CallTarget, ExprX, Expr, KrateX,
};
use air::errors::{error};
use air::ast::Span;
use std::collections::HashMap;
use std::collections::HashSet;
use std::ops::Index;
use std::sync::Arc;

pub fn get_transition<'a>(
    sm: &'a SM<Span, Ident, Ident, Expr, Typ>,
    ident: &Ident
) -> Option<&'a Transition<Span, Ident, Expr, Typ>> {
    for transition in &sm.transitions {
        if *transition.name == **ident {
            return Some(transition);
        }
    }
    return None;
}

pub fn check_wf_lemmas(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    //transition_map: map<Ident, Transition<Span, Ident, Expr, Ty>>,
    fun_map: &HashMap<Ident, Function>
) -> Result<(), VirErr> {
    for l in sm.lemmas.iter() {
        let transition_ident = &l.purpose.transition;
        match get_transition(sm, transition_ident) {
            None => {
                let span = &fun_map.index(&l.func).span;
                return Err(error(format!("no transition named {}", *transition_ident), span));
            }
            Some(l) => {
                // TODO
            }
        }
    }
    Ok(())
}

pub fn check_lemmas_cover_all_cases(sm: &SM<Span, Ident, Ident, Expr, Typ>, fun_map: &HashMap<Ident, Function>) -> Result<(), VirErr> {
    let mut need_inv_check = HashSet::new();
    let mut need_assert_check = HashSet::new();

    for t in sm.transitions.iter() {
        match &t.kind {
            TransitionKind::Init => { need_inv_check.insert(t.name.clone()); }
            TransitionKind::Transition => { need_inv_check.insert(t.name.clone()); }
            TransitionKind::Static => { }
        }

        if has_assertion(&t.body) {
            need_assert_check.insert(t.name.clone());
        }
    }

    let mut purposes_seen: HashMap<LemmaPurpose<Ident>, Ident> = HashMap::new();

    for l in sm.lemmas.iter() {
        match purposes_seen.get(&l.purpose) {
            Some(other_func) => {
                let span1 = &fun_map.index(other_func).span;
                let span2 = &fun_map.index(&l.func).span;
                return Err(error("state machine declares redundant lemmas", span1)
                    .primary_span(span2));
            }
            None => { }
        }
        purposes_seen.insert(l.purpose.clone(), l.func.clone());

        match &l.purpose {
            LemmaPurpose { transition, kind: LemmaPurposeKind::PreservesInvariant } => {
                if !need_inv_check.remove(transition) {
                    let span = &fun_map.index(transition).span;
                    return Err(error("this lemma is unnecessary transition '".to_string() + transition + "' is declared static and does not need an inductiveness check", &span));
                }
            }
            LemmaPurpose { transition, kind: LemmaPurposeKind::SatisfiesAsserts } => {
                if !need_assert_check.remove(transition) {
                    let span = &fun_map.index(transition).span;
                    return Err(error("this lemma is unnecessary because transition '".to_string() + transition + "' has no assertions", &span));
                }
            }
        }
    }

    // If there are any left over, error.

    for t in need_inv_check {
        return Err(error(format!("no lemma found to show that {} preserves invariants: declare a lemma with attribute #[inductive({})]", *t, *t), 
            &fun_map.index(&t).span));
    }

    for t in need_assert_check {
        return Err(error(format!("no lemma found to show that {} meets its assertions: declare a lemma with attribute #[safety({})]", *t, *t), 
            &fun_map.index(&t).span));
    }

    Ok(())
}

pub fn has_assertion(ts: &TransitionStmt<Span, Ident, Expr>) -> bool {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                if has_assertion(t) {
                    return true;
                }
            }
            return false;
        }
        TransitionStmt::Let(_, _, _) => false,
        TransitionStmt::If(_, _, thn, els) => has_assertion(thn) || has_assertion(els),
        TransitionStmt::Require(_, _) => false,
        TransitionStmt::Assert(_, _) => true,
        TransitionStmt::Update(_, _, _) => false,
    }
}
