#![allow(unused_imports)]

use smir::ast::{
    Field, LemmaPurpose, TransitionKind, Invariant, Lemma, Transition, ShardableType, SM,
};
use vir::ast::{
    VirErr, KrateX, Ident, Expr, Typ, Path,
};
use crate::check_wf::{check_wf_invariant};
use std::collections::HashMap;

pub fn update_krate(type_path: &Path, sm: &SM<Ident, Ident, Expr, Typ>, krate: &mut KrateX) -> Result<(), VirErr> {
    let mut fun_map = HashMap::new();
    for function in krate.functions.iter() {
        let p = function.x.name.path.clone();
        fun_map.insert(p, function.clone());
    }

    for inv in &sm.invariants {
        check_wf_user_invariant(type_path, &inv.func, &fun_map)?;
    }

    setup_inv(type_path, sm, krate);

    Ok(())
}
