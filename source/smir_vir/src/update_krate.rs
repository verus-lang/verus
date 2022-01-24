#![allow(unused_imports)]

use crate::check_wf::{check_wf_user_invariant, get_member_path, setup_inv};
use crate::lemmas::{check_lemmas_cover_all_cases, check_wf_lemmas, setup_lemmas};
use crate::transitions::check_transitions;
use air::ast::Span;
use smir::ast::{
    Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind, SM,
};
use std::collections::HashMap;
use vir::ast::{Expr, Function, Ident, KrateX, Path, Typ, VirErr};

pub fn update_krate(
    type_path: &Path,
    sm: &SM<Span, Ident, Ident, Expr, Typ>,
    krate: &mut KrateX,
) -> Result<(), VirErr> {
    let mut fun_map: HashMap<Ident, Function> = HashMap::new();
    for function in krate.functions.iter() {
        let member_name = function.x.name.path.segments.last().expect("path has last");
        if get_member_path(type_path, member_name) == function.x.name.path {
            fun_map.insert(member_name.clone(), function.clone());
        }
    }

    for inv in &sm.invariants {
        check_wf_user_invariant(type_path, &inv.func, &fun_map)?;
    }

    let mut new_funs: Vec<(Ident, Function)> = Vec::new();

    setup_inv(type_path, sm, &fun_map, &mut new_funs)?;

    check_wf_lemmas(sm, &fun_map)?;
    check_transitions(sm, &fun_map)?;
    check_lemmas_cover_all_cases(sm, &fun_map)?;

    setup_lemmas(sm, &type_path, &fun_map, &mut new_funs);

    for (ident, function) in new_funs {
        let path = get_member_path(type_path, &ident);
        update_function(&mut krate.functions, path, function);
    }

    Ok(())
}

fn update_function(v: &mut Vec<Function>, path: Path, function: Function) {
    for i in 0..v.len() {
        if v[i].x.name.path == path {
            v[i] = function;
            return;
        }
    }
    panic!("update_function: path not found");
}
