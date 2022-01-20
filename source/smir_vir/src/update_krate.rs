#![allow(unused_imports)]

use smir::ast::{
    Field, LemmaPurpose, TransitionKind, Invariant, Lemma, Transition, ShardableType, SM,
};
use vir::ast::{
    VirErr, KrateX, Ident, Expr, Typ, Path, Function,
};
use air::ast::{Span};
use crate::check_wf::{check_wf_user_invariant, setup_inv, get_member_path};
use crate::lemmas::{check_lemmas_cover_all_cases};
use crate::transitions::{check_transitions};
use std::collections::HashMap;

pub fn update_krate(type_path: &Path, sm: &SM<Span, Ident, Ident, Expr, Typ>, krate: &mut KrateX) -> Result<(), VirErr> {
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

    setup_inv(type_path, sm, krate, &fun_map, &mut new_funs)?;

    //check_wf_lemmas(sm, &fun_map)?;
    check_transitions(sm, &fun_map)?;
    check_lemmas_cover_all_cases(sm, &fun_map)?;

    Ok(())
}


