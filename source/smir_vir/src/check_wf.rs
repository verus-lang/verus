#![allow(unused_imports)]

use smir::ast::{
    Field, LemmaPurpose, TransitionKind, Invariant, Lemma, Transition, ShardableType, SM,
};
use vir::ast_util::{conjoin};
use vir::ast::{
    VirErr, Mode, Path, Function, FunctionX, Ident, Typ,
    PathX, TypX,
};
use air::errors::{error};
use std::collections::HashMap;
use std::ops::Index;
use std::sync::Arc;

// TODO put these in a util file or something

pub fn get_member_path(type_path: &Path, ident: &Ident) -> Path {
    let mut seg = (*type_path.segments).clone();
    seg.push(ident.clone());
    Arc::new(PathX {
        krate: type_path.krate.clone(),
        segments: Arc::new(seg),
    })
}

pub fn is_self_type(typ: &Typ, self_path: &Path) -> bool {
    match &**typ {
        TypX::Datatype(p, typs) => self_path == p && typs.len() == 0,
        _ => false,
    }
}

pub fn is_bool_type(typ: &Typ) -> bool {
    match &**typ {
        TypX::Bool => true,
        _ => false,
    }
}

pub fn check_wf_user_invariant(type_path: &Path, inv: &Ident, funs: &HashMap<Path, Function>) -> Result<(), VirErr> {
    let p = get_member_path(type_path, &inv);
    let f: &Function = funs.index(&p);

    match &f.x {
        FunctionX {
            name: _,
            visibility: _,
            mode,
            fuel: _,
            typ_bounds,
            params,
            ret,
            require: _,
            ensure: _,
            decrease: _,
            mask_spec: _,
            is_abstract: _,
            attrs: _,
            body: _,
        } => {
            if *mode != Mode::Spec {
                return Err(error("invariant function must be 'spec'", &f.span));
            }
            if typ_bounds.len() != 0 {
                return Err(error("invariant function has unexpected type bounds", &f.span));
            }

            if params.len() != 1 || !is_self_type(&params[0].x.typ, type_path) {
                return Err(error("invariant function should have exactly one param: self", &f.span));
            }

            if !is_bool_type(&ret.x.typ) {
                return Err(error("invariant function should return a bool", &f.span));
            }
        }
    }

    Ok(())
}

pub fn setup_inv(type_path: &Path, sm: &SM<Ident, Ident, Expr, Typ>, krate: &mut KrateX, funs: &HashMap<Path, Function>) {
    let exprs = Vec::new();

    for inv in &sm.invariants {
        let p = get_member_path(type_path, &inv);
        let f: &Function = funs.index(&p);
        exprs.push(f.span.clone(), CallTarget::Static(f.x.name.clone(), Vec::new()), vec![
            Arc::new(Var(Arc::new("self".to_string()))),
        ]);
    }

    let inv_body = conjoin(invariant_fn_span, exprs);

    let inv_path = get_member_path(type_path, Arc::new("invariant".to_string()));

    for function in krate.functions.iter() {
        let p = function.x.name.path.clone();
        fun_map.insert(p, function.clone());
    }
}
