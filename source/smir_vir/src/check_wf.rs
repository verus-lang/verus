#![allow(unused_imports)]

use smir::ast::{
    Field, LemmaPurpose, TransitionKind, Invariant, Lemma, Transition, ShardableType, SM,
};
use vir::ast_util::{conjoin, mk_call, mk_var};
use vir::ast::{
    VirErr, Mode, Path, Function, FunctionX, Ident, Typ,
    PathX, TypX, CallTarget, ExprX, Expr, KrateX,
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

pub fn set_body(f: &Function, body: Expr) -> Function {
    unimplemented!();
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
                return Err(error("user-defined invariant must be 'spec'", &f.span));
            }
            if typ_bounds.len() != 0 {
                return Err(error("user-defined invariant has unexpected type bounds", &f.span));
            }

            if params.len() != 1 || !is_self_type(&params[0].x.typ, type_path) {
                return Err(error("user-defined invariant should have exactly one param: self", &f.span));
            }

            if !is_bool_type(&ret.x.typ) {
                return Err(error("user-defined invariant should return a bool", &f.span));
            }
        }
    }

    Ok(())
}

pub fn setup_inv(type_path: &Path, sm: &SM<Ident, Ident, Expr, Typ>, krate: &KrateX, funs: &HashMap<Path, Function>, new_funs: &mut Vec<(Path, Function)>) -> Result<(), VirErr> {
    let mut exprs = Vec::new();

    for inv in &sm.invariants {
        let p = get_member_path(type_path, &inv.func);
        let f: &Function = funs.index(&p);
        exprs.push(mk_call(
            &f.span,
            &CallTarget::Static(f.x.name.clone(), Arc::new(Vec::new())),
            &Arc::new(vec![
                mk_var(&f.span, "self".to_string()),
            ]),
        ));
    }

    let inv_path = get_member_path(type_path, &Arc::new("invariant".to_string()));
    let f: &Function = funs.index(&inv_path);

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
                return Err(error("macro-generated invariant must be 'spec'", &f.span));
            }
            if typ_bounds.len() != 0 {
                return Err(error("macro-generated invariant has unexpected type bounds", &f.span));
            }

            if params.len() != 1 || !is_self_type(&params[0].x.typ, type_path) {
                return Err(error("macro-generated invariant should have exactly one param: self", &f.span));
            }

            if !is_bool_type(&ret.x.typ) {
                return Err(error("macro-generated invariant should return a bool", &f.span));
            }
        }
    }

    let inv_body = conjoin(&f.span, &exprs);
    let new_f = set_body(f, inv_body);

    new_funs.push((inv_path, new_f));

    Ok(())
}
