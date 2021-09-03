//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{BinaryOp, Path, Typ, Typs, UnaryOp, UnaryOpr};
use crate::def::Spanned;
use air::ast::{Binders, Ident, Quant};
use std::sync::Arc;

pub type Trig = Exps;
pub type Trigs = Arc<Vec<Trig>>;

pub type Bnd = Arc<Spanned<BndX>>;
#[derive(Clone, Debug)]
pub enum BndX {
    Let(Binders<Exp>),
    Quant(Quant, Binders<Typ>, Trigs),
}

#[derive(Clone, Debug)]
pub enum Constant {
    Bool(bool),
    Nat(Arc<String>),
}

pub type Exp = Arc<Spanned<ExpX>>;
pub type Exps = Arc<Vec<Exp>>;
#[derive(Debug)]
pub enum ExpX {
    Const(Constant),
    Var(Ident),
    Old(Ident, Ident),       // used only during sst_to_air to generate AIR Old
    Call(Ident, Typs, Exps), // call to spec function
    Ctor(Path, Ident, Binders<Exp>),
    Field { lhs: Exp, datatype_name: Ident, field_name: Ident },
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    If(Exp, Exp, Exp),
    Bind(Bnd, Exp),
}

#[derive(Debug)]
pub struct Dest {
    pub var: Ident,
    pub mutable: bool,
}

pub type Stm = Arc<Spanned<StmX>>;
pub type Stms = Arc<Vec<Stm>>;
#[derive(Debug)]
pub enum StmX {
    Call(Ident, Typs, Exps, Option<Dest>), // call to exec/proof function
    Assert(Exp),
    Assume(Exp),
    Decl {
        ident: Ident,
        typ: Typ,
        mutable: bool,
        init: bool,
    },
    Assign(Exp, Exp),
    Fuel(Ident, u32),
    If(Exp, Stm, Option<Stm>),
    While {
        cond: Exp,
        body: Stm,
        invs: Exps,
        typ_inv_vars: Arc<Vec<(Ident, Typ)>>,
        modified_vars: Arc<Vec<Ident>>,
    },
    Block(Stms),
}
