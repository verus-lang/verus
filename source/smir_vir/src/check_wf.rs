#![allow(unused_imports)]

use smir::ast::{
    Field, LemmaPurpose, TransitionKind, Invariant, Lemma, Transition, ShardableType, SM,
};
use vir::ast_util::{conjoin, mk_call, mk_var};
use vir::def::{Spanned};
use vir::ast::{
    VirErr, Mode, Path, Function, FunctionX, Ident, Typ,
    PathX, TypX, CallTarget, ExprX, Expr, KrateX,
};
use air::errors::{error};
use air::ast::Span;
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
    let mut fx = f.x.clone();
    fx.body = Some(body);
    Spanned::new(f.span.clone(), fx)
}

pub fn check_wf_user_invariant(type_path: &Path, inv: &Ident, funs: &HashMap<Ident, Function>) -> Result<(), VirErr> {
    let f: &Function = funs.index(inv);

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

pub fn setup_inv(type_path: &Path, sm: &SM<Span, Ident, Ident, Expr, Typ>, funs: &HashMap<Ident, Function>, new_funs: &mut Vec<(Ident, Function)>) -> Result<(), VirErr> {
    let mut exprs = Vec::new();

    for inv in &sm.invariants {
        let f: &Function = funs.index(&inv.func);
        let self_type = Arc::new(TypX::Datatype(type_path.clone(), Arc::new(Vec::new())));
        exprs.push(mk_call(
            &f.span,
            &Arc::new(TypX::Bool),
            &CallTarget::Static(f.x.name.clone(), Arc::new(Vec::new())),
            &Arc::new(vec![
                mk_var(&f.span, &self_type, "self".to_string()),
            ]),
        ));
    }

    let invariant_ident = Arc::new("invariant".to_string());
    let f: &Function = funs.index(&invariant_ident);

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

    new_funs.push((invariant_ident, new_f));

    Ok(())
}
