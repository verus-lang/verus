#![allow(unused_imports)]

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
    CallTarget, Expr, ExprX, Function, FunctionX, Ident, KrateX, Mode, Path, PathX, Typ, TypX,
    VirErr,
};
use vir::ast_util::{conjoin, mk_call, mk_var};

pub fn fields_contain(fields: &Vec<Field<Ident, Typ>>, ident: &Ident) -> bool {
    for f in fields {
        if *f.ident == **ident {
            return true;
        }
    }
    return false;
}
