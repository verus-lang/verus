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

pub fn fields_contain(fields: &Vec<Field<Ident, Typ>>, ident: &Ident) -> bool {
    for f in fields {
        if *f.ident == **ident {
            return true;
        }
    }
    return false;
}
