//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{
    BinaryOp, Constant, Fun, Path, SpannedTyped, Typ, Typs, UnaryOp, UnaryOpr, VarAt,
};
use crate::def::Spanned;
use air::ast::{Binder, Binders, Ident, Quant};
use air::errors::Error;
use std::sync::Arc;

pub type Trig = Exps;
pub type Trigs = Arc<Vec<Trig>>;

pub type Bnd = Arc<Spanned<BndX>>;
#[derive(Clone, Debug)]
pub enum BndX {
    Let(Binders<Exp>),
    Quant(Quant, Binders<Typ>, Trigs),
    Lambda(Binders<Typ>),
    Choose(Binder<Typ>, Trigs),
}

// variable name with optional unique id for renaming (equal to unique_id in LocalDeclX)
pub type UniqueIdent = (Ident, Option<u64>);

pub type Exp = Arc<SpannedTyped<ExpX>>;
pub type Exps = Arc<Vec<Exp>>;
#[derive(Debug)]
pub enum ExpX {
    Const(Constant),
    Var(UniqueIdent),
    VarAt(Ident, VarAt),
    // used only during sst_to_air to generate AIR Old
    Old(Ident, Ident),
    // call to spec function
    Call(Fun, Typs, Exps),
    CallLambda(Typ, Exp, Exps),
    Ctor(Path, Ident, Binders<Exp>),
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    If(Exp, Exp, Exp),
    Bind(Bnd, Exp),
}

#[derive(Clone, Debug)]
pub struct Dest {
    pub var: UniqueIdent,
    pub is_init: bool,
}

pub type Stm = Arc<Spanned<StmX>>;
pub type Stms = Arc<Vec<Stm>>;
#[derive(Debug)]
pub enum StmX {
    // call to exec/proof function
    Call(Fun, Typs, Exps, Option<Dest>),
    // note: failed assertion reports Stm's span, plus an optional additional span
    Assert(Option<Error>, Exp),
    AssertBV(Exp),
    Assume(Exp),
    Assign {
        lhs: UniqueIdent,
        rhs: Exp,
        is_init: bool,
    },
    Fuel(Fun, u32),
    DeadEnd(Stm),
    If(Exp, Stm, Option<Stm>),
    While {
        cond_stms: Stms,
        cond_exp: Exp,
        body: Stm,
        invs: Exps,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        modified_vars: Arc<Vec<UniqueIdent>>,
    },
    OpenInvariant(Exp, UniqueIdent, Typ, Stm),
    Block(Stms),
}

pub type LocalDecl = Arc<LocalDeclX>;
#[derive(Debug)]
pub struct LocalDeclX {
    pub ident: UniqueIdent,
    pub typ: Typ,
    pub mutable: bool,
}
