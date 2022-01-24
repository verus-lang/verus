#![allow(unused_imports)]

use crate::check_wf::set_body;
use crate::check_wf::{check_wf_user_invariant, get_member_path, setup_inv};
use crate::transitions::assume_transition_holds;
use air::ast::Span;
use air::errors::error;
use smir::ast::{
    Field, Invariant, Lemma, LemmaPurpose, LemmaPurposeKind, ShardableType, Transition,
    TransitionKind, TransitionStmt, SM,
};
use std::collections::HashMap;
use std::collections::HashSet;
use std::ops::Index;
use std::sync::Arc;
use vir::ast::{
    CallTarget, DatatypeX, Expr, ExprX, FunX, Function, FunctionX, Ident, KrateX, Mode, Path,
    PathX, SpannedTyped, Typ, TypX, VirErr,
};
use vir::ast_util::{
    conjoin, mk_and, mk_assert, mk_assume, mk_block, mk_bool, mk_call, mk_decl_stmt, mk_eq,
    mk_expr_stmt, mk_ife, mk_implies, mk_or, mk_var,
};

pub fn get_transition<'a>(
    sm: &'a SM<Span, Ident, Ident, Expr, Typ>,
    ident: &Ident,
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
    fun_map: &HashMap<Ident, Function>,
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

pub fn check_lemmas_cover_all_cases(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    fun_map: &HashMap<Ident, Function>,
) -> Result<(), VirErr> {
    let mut need_inv_check = HashSet::new();
    let mut need_assert_check = HashSet::new();

    for t in sm.transitions.iter() {
        match &t.kind {
            TransitionKind::Init => {
                need_inv_check.insert(t.name.clone());
            }
            TransitionKind::Transition => {
                need_inv_check.insert(t.name.clone());
            }
            TransitionKind::Readonly => {}
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
                return Err(
                    error("state machine declares redundant lemmas", span1).primary_span(span2)
                );
            }
            None => {}
        }
        purposes_seen.insert(l.purpose.clone(), l.func.clone());

        match &l.purpose {
            LemmaPurpose { transition, kind: LemmaPurposeKind::PreservesInvariant } => {
                if !need_inv_check.remove(transition) {
                    let span = &fun_map.index(transition).span;
                    return Err(error(
                        "this lemma is unnecessary transition '".to_string()
                            + transition
                            + "' is declared readonly and thus does not need an inductiveness check",
                        &span,
                    ));
                }
            }
            LemmaPurpose { transition, kind: LemmaPurposeKind::SatisfiesAsserts } => {
                if !need_assert_check.remove(transition) {
                    let span = &fun_map.index(transition).span;
                    return Err(error(
                        "this lemma is unnecessary because transition '".to_string()
                            + transition
                            + "' has no assertions",
                        &span,
                    ));
                }
            }
        }
    }

    // If there are any left over, error.

    for t in need_inv_check {
        return Err(error(
            format!(
                "no lemma found to show that {} preserves invariants: declare a lemma with attribute #[inductive({})]",
                *t, *t
            ),
            &fun_map.index(&t).span,
        ));
    }

    for t in need_assert_check {
        return Err(error(
            format!(
                "no lemma found to show that {} meets its assertions: declare a lemma with attribute #[safety({})]",
                *t, *t
            ),
            &fun_map.index(&t).span,
        ));
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

pub fn inv_call(span: &Span, type_path: &Path, ident: &Ident) -> Expr {
    let inv_path = get_member_path(type_path, &Arc::new("invariant".to_string()));
    let fun = Arc::new(FunX { path: inv_path, trait_path: None });
    let call_target = CallTarget::Static(fun, Arc::new(Vec::new()));
    let var_ty = Arc::new(TypX::Datatype(type_path.clone(), Arc::new(Vec::new())));
    let var_for_ident = SpannedTyped::new(span, &var_ty, ExprX::Var(ident.clone()));
    return mk_call(span, &Arc::new(TypX::Bool), &call_target, &vec![var_for_ident]);
}

pub fn setup_lemmas(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    type_path: &Path,
    funs: &HashMap<Ident, Function>,
    new_funs: &mut Vec<(Ident, Function)>,
) {
    for l in sm.lemmas.iter() {
        match &l.purpose {
            LemmaPurpose { transition, kind: LemmaPurposeKind::PreservesInvariant } => {
                let function = funs.index(&l.func);
                let body = function.x.body.clone().expect("body");
                let span = function.span.clone();
                let post_ident = Arc::new("post".to_string());
                let self_ident = Arc::new("self".to_string());
                let assume_inv = mk_assume(&span, &inv_call(&span, &type_path, &self_ident));
                let ts = get_transition(sm, transition).expect("get_transition");
                let assume_transition = assume_transition_holds(sm, &ts.body, &post_ident);
                let assert_inv = mk_assume(&span, &inv_call(&span, &type_path, &post_ident));
                let stmts = vec![
                    mk_expr_stmt(&span, &assume_inv),
                    assume_transition,
                    mk_expr_stmt(&span, &body),
                    mk_expr_stmt(&span, &assert_inv),
                ];
                let new_body = mk_block(&span, stmts, &None);

                let new_f = set_body(function, new_body);
                new_funs.push((l.func.clone(), new_f));
            }
            LemmaPurpose { transition, kind: LemmaPurposeKind::SatisfiesAsserts } => {
                // TODO
            }
        }
    }
}
