#![allow(unused_imports)]

use crate::check_wf::{check_wf_user_invariant, get_member_path, setup_inv};
use crate::check_wf::{set_body, set_req_ens};
use crate::update_krate::Predicate;
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
    CallTarget, DatatypeX, Expr, ExprX, FunX, Function, FunctionX, Ident, KrateX, Mode, Param,
    ParamX, Params, Path, PathX, SpannedTyped, Typ, TypX, VirErr,
};
use vir::ast_util::{
    conjoin, mk_and, mk_assert, mk_assume, mk_bool, mk_call, mk_decl_stmt, mk_eq,
    mk_ife, mk_implies, mk_or, mk_var, types_equal,
};

pub fn get_transition_func_name(
    predicates: &Vec<(String, Predicate)>,
    ident: &Ident,
) -> Option<(Ident, bool)> {
    for (func_name, p) in predicates {
        match p {
            Predicate::Transition(n) => {
                if n.to_string() == ident.to_string() {
                    return Some((Arc::new(func_name.clone()), false));
                }
            }
            Predicate::Init(n) => {
                if n.to_string() == ident.to_string() {
                    return Some((Arc::new(func_name.clone()), true));
                }
            }
            _ => {}
        }
    }
    return None;
}

pub fn check_wf_lemmas(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    //transition_map: map<Ident, Transition<Span, Ident, Expr, Ty>>,
    predicates: &Vec<(String, Predicate)>,
    fun_map: &HashMap<Ident, Function>,
) -> Result<(), VirErr> {
    for l in sm.lemmas.iter() {
        match l.purpose.kind {
            LemmaPurposeKind::PreservesInvariant => {
                let transition_ident = &l.purpose.transition;
                match get_transition_func_name(predicates, transition_ident) {
                    None => {
                        let span = &fun_map.index(&l.func).span;
                        return Err(error(
                            format!("no transition named {}", *transition_ident),
                            span,
                        ));
                    }
                    Some((_id, _)) => {
                        // TODO check other wf-ness
                    }
                }
            }
            LemmaPurposeKind::SatisfiesAsserts => {
                // TODO
            }
        }
    }
    Ok(())
}

pub fn check_lemmas_cover_all_cases(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    predicates: &Vec<(String, Predicate)>,
    fun_map: &HashMap<Ident, Function>,
) -> Result<(), VirErr> {
    let mut need_inv_check = HashSet::new();
    let mut need_assert_check = HashSet::new();

    for p in predicates.iter() {
        match p {
            (_func_name, Predicate::Init(id)) => {
                need_inv_check.insert(id.clone());
            }
            (_func_name, Predicate::Transition(id)) => {
                need_inv_check.insert(id.clone());
            }
            (_func_name, Predicate::Safety(id, n)) => {
                need_assert_check.insert((id.clone(), *n));
            }
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
                        "this lemma is unnecessary because transition '".to_string()
                            + transition
                            + "' is declared readonly and thus does not need an inductiveness check",
                        &span,
                    ));
                }
            }
            LemmaPurpose { transition, kind: LemmaPurposeKind::SatisfiesAsserts } => {
                if !need_assert_check.remove(&(transition.clone(), 1)) {
                    // TODO the numbers
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
                t.0, t.0
            ),
            &fun_map.index(&t.0).span,
        ));
    }

    Ok(())
}

/*
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
*/

pub fn inv_call(span: &Span, type_path: &Path, ident: &Ident) -> Expr {
    let inv_path = get_member_path(type_path, &Arc::new("invariant".to_string()));
    let fun = Arc::new(FunX { path: inv_path, trait_path: None });
    let call_target = CallTarget::Static(fun, Arc::new(Vec::new()));
    let var_ty = Arc::new(TypX::Datatype(type_path.clone(), Arc::new(Vec::new())));
    let var_for_ident = SpannedTyped::new(span, &var_ty, ExprX::Var(ident.clone()));
    return mk_call(span, &Arc::new(TypX::Bool), &call_target, &vec![var_for_ident]);
}

pub fn get_transition_params(is_init: bool, func: &Function) -> Params {
    if is_init {
        Arc::new(func.x.params[1..].to_vec())
    } else {
        Arc::new(func.x.params[2..].to_vec())
    }
}

pub fn is_param_okay(param: &Param, expected_name: &String, expected_typ: &Typ) -> bool {
    let ParamX { name, typ, mode: _, is_mut } = &param.x;
    !is_mut && **name == *expected_name && types_equal(typ, expected_typ)
}

pub fn is_param_self(param: &Param, self_ty: &Typ) -> bool {
    is_param_okay(param, &"self".to_string(), self_ty)
}

pub fn is_param_post(param: &Param, self_ty: &Typ) -> bool {
    is_param_okay(param, &"post".to_string(), self_ty)
}

pub fn check_inductiveness_lemma_typ_sig(
    is_init: bool,
    trans_params: Params,
    self_ty: &Typ,
    lemma: &Function,
) -> Result<(), VirErr> {
    if lemma.x.typ_bounds.len() != 0 {
        return Err(error(
            "invariant lemma should not have additional type parameters",
            &lemma.span,
        ));
    }

    if lemma.x.mode != Mode::Proof {
        return Err(error("invariant lemma should be in 'proof' mode", &lemma.span));
    }

    if lemma.x.has_return() {
        return Err(error("invariant lemma should not have a return value", &lemma.x.ret.span));
    }

    if is_init {
        if lemma.x.params.len() < 1 || !is_param_post(&lemma.x.params[0], self_ty) {
            return Err(error(
                "first param for initialization lemma should be 'post: Self'",
                if lemma.x.params.len() < 1 { &lemma.span } else { &lemma.x.params[0].span },
            ));
        }
    } else {
        if lemma.x.params.len() < 1 || !is_param_self(&lemma.x.params[0], self_ty) {
            return Err(error(
                "first param for inductiveness lemma should be 'self: Self'",
                if lemma.x.params.len() < 1 { &lemma.span } else { &lemma.x.params[0].span },
            ));
        }

        if lemma.x.params.len() < 2 || !is_param_post(&lemma.x.params[1], self_ty) {
            return Err(error(
                "second param for inductiveness lemma should be 'post: Self'",
                if lemma.x.params.len() < 2 { &lemma.span } else { &lemma.x.params[1].span },
            ));
        }
    }

    let offset = if is_init { 1 } else { 2 };
    for i in 0..trans_params.len() {
        if offset + i >= lemma.x.params.len() {
            return Err(error(
                "not enough parameters: parameters should match the parameters of the transition",
                &lemma.span,
            ));
        }

        if !is_param_okay(
            &lemma.x.params[offset + i],
            &*trans_params[i].x.name,
            &trans_params[i].x.typ,
        ) {
            return Err(error(
                format!(
                    "parameter should match the name and type of '{}'",
                    *trans_params[i].x.name
                ),
                &lemma.x.params[offset + i].span,
            ));
        }
    }

    if offset + trans_params.len() < lemma.x.params.len() {
        return Err(error(
            "lemma has extra parameters",
            &lemma.x.params[offset + trans_params.len()].span,
        ));
    }

    for p in lemma.x.params.iter() {
        if p.x.mode != Mode::Spec {
            return Err(error("invariant lemma should only take 'spec' parameters", &p.span));
        }
    }

    Ok(())
}

pub fn setup_lemmas(
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    predicates: &Vec<(String, Predicate)>,
    type_path: &Path,
    funs: &HashMap<Ident, Function>,
    new_funs: &mut Vec<(Ident, Function)>,
) -> Result<(), VirErr> {
    for l in sm.lemmas.iter() {
        match &l.purpose {
            LemmaPurpose { transition, kind: LemmaPurposeKind::PreservesInvariant } => {
                let (trans_func_name, is_init) = get_transition_func_name(predicates, transition)
                    .expect("get_transition_func_name");
                let trans_function = funs.index(&trans_func_name);
                let lemma_function = funs.index(&l.func);
                let span = lemma_function.span.clone();

                let post_ident = Arc::new("post".to_string());
                let self_ident = Arc::new("self".to_string());

                let inv_holds_for_self = inv_call(&span, &type_path, &self_ident);
                let inv_holds_for_post = inv_call(&span, &type_path, &post_ident);

                let trans_path = get_member_path(type_path, &trans_func_name);
                let trans_fun = Arc::new(FunX { path: trans_path, trait_path: None });
                let call_target = CallTarget::Static(trans_fun, Arc::new(Vec::new()));
                let var_ty = Arc::new(TypX::Datatype(type_path.clone(), Arc::new(Vec::new())));
                let var_for_self_ident =
                    SpannedTyped::new(&span, &var_ty, ExprX::Var(self_ident.clone()));
                let var_for_post_ident =
                    SpannedTyped::new(&span, &var_ty, ExprX::Var(post_ident.clone()));
                let mut call_args = vec![];
                if !is_init {
                    call_args.push(var_for_self_ident);
                }
                call_args.push(var_for_post_ident);
                let trans_params = get_transition_params(is_init, trans_function);
                for param in trans_params.iter() {
                    call_args.push(SpannedTyped::new(
                        &span,
                        &param.x.typ,
                        ExprX::Var(param.x.name.clone()),
                    ));
                }
                let trans_holds_for_self_post =
                    mk_call(&span, &Arc::new(TypX::Bool), &call_target, &call_args);

                check_inductiveness_lemma_typ_sig(is_init, trans_params, &var_ty, lemma_function)?;

                let reqs = if is_init {
                    vec![trans_holds_for_self_post]
                } else {
                    vec![inv_holds_for_self, trans_holds_for_self_post]
                };

                let enss = vec![inv_holds_for_post];

                let new_f = set_req_ens(lemma_function, reqs, enss);

                /*
                let assume_inv = mk_assume(&span, &inv_call(&span, &type_path, &self_ident));
                let ts = get_transition(sm, transition).expect("get_transition");
                let assume_transition = assume_transition_holds(sm, &ts.body, type_path, &post_ident);
                let assert_inv = mk_assume(&span, &inv_call(&span, &type_path, &post_ident));
                let stmts = vec![
                    mk_expr_stmt(&span, &assume_inv),
                    assume_transition,
                    mk_expr_stmt(&span, &body),
                    mk_expr_stmt(&span, &assert_inv),
                ];
                let new_body = mk_block(&span, stmts, &None);
                */

                new_funs.push((l.func.clone(), new_f));
            }
            LemmaPurpose { transition: _, kind: LemmaPurposeKind::SatisfiesAsserts } => {
                // TODO
            }
        }
    }

    Ok(())
}
