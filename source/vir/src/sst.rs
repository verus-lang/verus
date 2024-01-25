//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{
    AssertQueryMode, BinaryOp, Constant, Fun, InvAtomicity, Mode, NullaryOpr, Path, Quant,
    SpannedTyped, Typ, Typs, UnaryOp, UnaryOpr, VarAt,
};
use crate::def::Spanned;
use crate::interpreter::InterpExp;
use crate::messages::{Message, Span};
use air::ast::{Binders, Ident};
use std::sync::Arc;

pub type Trig = Exps;
pub type Trigs = Arc<Vec<Trig>>;

pub struct BndInfoUser {
    pub span: Span,
    pub trigs: Trigs,
}

pub struct BndInfo {
    pub fun: Fun,
    pub user: Option<BndInfoUser>,
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum InternalFun {
    ClosureReq,
    ClosureEns,
    CheckDecreaseInt,
    CheckDecreaseHeight,
    HasType,
}

#[derive(Debug, Clone, Hash)]
pub enum CallFun {
    // static/method Fun, plus an optional resolved Fun for methods
    Fun(Fun, Option<(Fun, Typs)>),
    Recursive(Fun),
    InternalFun(InternalFun),
}

pub type Exp = Arc<SpannedTyped<ExpX>>;
pub type Exps = Arc<Vec<Exp>>;
#[derive(Debug, Clone)]
pub enum ExpX {
    Const(Constant),
    Var(UniqueIdent),
    StaticVar(Fun),
    VarLoc(UniqueIdent),
    VarAt(UniqueIdent, VarAt),
    Loc(Exp),
    // used only during sst_to_air to generate AIR Old
    Old(Ident, UniqueIdent),
    // call to spec function
    Call(CallFun, Typs, Exps),
    CallLambda(Typ, Exp, Exps),
    Ctor(Path, Ident, Binders<Exp>),
    NullaryOpr(NullaryOpr),
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    BinaryOpr(crate::ast::BinaryOpr, Exp, Exp),
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

pub type LoopInvs = Arc<Vec<LoopInv>>;
#[derive(Debug, Clone)]
pub struct LoopInv {
    // "invariant": at_entry = true, at_exit = false
    // "invariant_ensures": at_entry = true, at_exit = true
    // "ensures": at_entry = false, at_exit = true
    pub at_entry: bool,
    pub at_exit: bool,
    pub inv: Exp,
}

pub type Stm = Arc<Spanned<StmX>>;
pub type Stms = Arc<Vec<Stm>>;
#[derive(Debug)]
pub enum StmX {
    // call to exec/proof function (or spec function for checking_spec_preconditions)
    Call {
        fun: Fun,
        resolved_method: Option<(Fun, Typs)>,
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
    Assume(Exp),
    Assign {
        lhs: Dest,
        rhs: Exp,
    },
    Fuel(Fun, u32),
    RevealString(Arc<String>),
    DeadEnd(Stm),
    // Assert that the postcondition holds with the given return value
    Return {
        base_error: Message,
        ret_exp: Option<Exp>,
        // If inside_body = true, we will add an assume false after the statement
        inside_body: bool,
    },
    BreakOrContinue {
        label: Option<String>,
        is_break: bool,
    },
    If(Exp, Stm, Option<Stm>),
    Loop {
        // We either have (1) a simple while loop or (2) a complex loop:
        // 1. cond = Some(...), all invs are true on entry and exit, no break statements
        // 2. cond = None, invs may have false at_entry/at_exit, may have break statements
        // Any while loop not satisfying (1) is converted to (2).
        is_for_loop: bool,
        label: Option<String>,
        cond: Option<(Stm, Exp)>,
        body: Stm,
        invs: LoopInvs,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        modified_vars: Arc<Vec<UniqueIdent>>,
    },
    OpenInvariant(Exp, UniqueIdent, Typ, Stm, InvAtomicity),
    Block(Stms),
    ClosureInner {
        body: Stm,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
    },
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
