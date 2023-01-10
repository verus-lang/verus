//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{
    AssertQueryMode, BinaryOp, Constant, Fun, InvAtomicity, Mode, Path, Quant, SpannedTyped, Typ,
    Typs, UnaryOp, UnaryOpr, VarAt,
};
use crate::def::Spanned;
use crate::interpreter::InterpExp;
use air::ast::{Binders, Ident, Span};
use air::messages::Message;
use std::sync::Arc;

pub type Trig = Exps;
pub type Trigs = Arc<Vec<Trig>>;

pub struct BndInfo {
    pub span: Span,
    pub trigs: Trigs,
}

pub type Bnd = Arc<Spanned<BndX>>;
#[derive(Clone, Debug)]
pub enum BndX {
    Let(Binders<Exp>),
    Quant(Quant, Binders<Typ>, Trigs),
    Lambda(Binders<Typ>, Trigs),
    Choose(Binders<Typ>, Trigs, Exp),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniqueIdent {
    pub name: Ident,
    // None for bound vars, Some disambiguating integer for local vars
    pub local: Option<u64>,
}

pub type Exp = Arc<SpannedTyped<ExpX>>;
pub type Exps = Arc<Vec<Exp>>;
#[derive(Debug, Clone)]
pub enum ExpX {
    Const(Constant),
    Var(UniqueIdent),
    VarLoc(UniqueIdent),
    VarAt(UniqueIdent, VarAt),
    Loc(Exp),
    // used only during sst_to_air to generate AIR Old
    Old(Ident, UniqueIdent),
    // call to spec function
    Call(Fun, Typs, Exps),
    CallLambda(Typ, Exp, Exps),
    Ctor(Path, Ident, Binders<Exp>),
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    If(Exp, Exp, Exp),
    WithTriggers(Trigs, Exp),
    Bind(Bnd, Exp),
    // only used internally by the interpreter; should never be seen outside it
    Interp(InterpExp),
}

#[derive(Debug, Clone, Copy)]
pub enum ParPurpose {
    MutPre,
    MutPost,
    Regular,
}

/// Function parameter
pub type Par = Arc<Spanned<ParX>>;
pub type Pars = Arc<Vec<Par>>;
#[derive(Debug, Clone)]
pub struct ParX {
    pub name: Ident,
    pub typ: Typ,
    pub mode: Mode,
    pub purpose: ParPurpose,
}

#[derive(Clone, Debug)]
pub struct Dest {
    pub dest: Exp,
    pub is_init: bool,
}

pub type Stm = Arc<Spanned<StmX>>;
pub type Stms = Arc<Vec<Stm>>;

#[derive(Debug)]
pub enum StmX {
    // call to exec/proof function (or spec function for checking_recommends)
    Call {
        fun: Fun,
        mode: Mode,
        typ_args: Typs,
        args: Exps,
        // if split is Some, this is a dummy call to be replaced with assertions for error splitting
        split: Option<Message>,
        dest: Option<Dest>,
    },
    // note: failed assertion reports Stm's span, plus an optional additional span
    Assert(Option<Message>, Exp),
    AssertBitVector {
        requires: Exps,
        ensures: Exps,
    },
    // Assert that the post condition holds with the given return value
    AssertPostConditions(Message, Option<Exp>),
    Assume(Exp),
    Assign {
        lhs: Dest,
        rhs: Exp,
    },
    Fuel(Fun, u32),
    RevealString(Arc<String>),
    DeadEnd(Stm),
    If(Exp, Stm, Option<Stm>),
    While {
        cond_stm: Stm,
        cond_exp: Exp,
        body: Stm,
        invs: Exps,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        modified_vars: Arc<Vec<UniqueIdent>>,
    },
    OpenInvariant(Exp, UniqueIdent, Typ, Stm, InvAtomicity),
    Block(Stms),
    ClosureInner(Stm),
    AssertQuery {
        mode: AssertQueryMode,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        body: Stm,
    },
}

pub type LocalDecl = Arc<LocalDeclX>;
#[derive(Debug)]
pub struct LocalDeclX {
    pub ident: UniqueIdent,
    pub typ: Typ,
    pub mutable: bool,
}
