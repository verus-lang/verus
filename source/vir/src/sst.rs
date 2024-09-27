//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{
    AssertQueryMode, BinaryOp, Constant, Fun, Mode, NullaryOpr, Path, Quant, SpannedTyped, Typ,
    Typs, UnaryOp, UnaryOpr, VarAt, VarBinders, VarIdent,
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
    Let(VarBinders<Exp>),
    Quant(Quant, VarBinders<Typ>, Trigs),
    Lambda(VarBinders<Typ>, Trigs),
    Choose(VarBinders<Typ>, Trigs, Exp),
}

// TODO: remove UniqueIdent
pub type UniqueIdent = VarIdent;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum InternalFun {
    ClosureReq,
    ClosureEns,
    CheckDecreaseInt,
    CheckDecreaseHeight,
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
    CallLambda(Exp, Exps),
    Ctor(Path, Ident, Binders<Exp>),
    NullaryOpr(NullaryOpr),
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    BinaryOpr(crate::ast::BinaryOpr, Exp, Exp),
    If(Exp, Exp, Exp),
    WithTriggers(Trigs, Exp),
    Bind(Bnd, Exp),
    ExecFnByName(Fun),
    ArrayLiteral(Exps),
    // only used internally by the interpreter; should never be seen outside it
    Interp(InterpExp),
    FuelConst(usize),
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
    pub name: VarIdent,
    pub typ: Typ,
    pub mode: Mode,
    pub is_mut: bool,
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
    // "invariant_except_break": at_entry = true, at_exit = false
    // "invariant": at_entry = true, at_exit = true
    // "ensures": at_entry = false, at_exit = true
    pub at_entry: bool,
    pub at_exit: bool,
    pub inv: Exp,
}

pub type AssertId = air::ast::AssertId;

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
        assert_id: Option<AssertId>,
    },
    // note: failed assertion reports Stm's span, plus an optional additional span
    Assert(Option<AssertId>, Option<Message>, Exp),
    AssertBitVector {
        requires: Exps,
        ensures: Exps,
    },
    AssertQuery {
        mode: AssertQueryMode,
        typ_inv_exps: Exps,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        body: Stm,
    },
    AssertCompute(Option<AssertId>, Exp, crate::ast::ComputeMode),
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
        assert_id: Option<AssertId>,
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
        loop_isolation: bool,
        is_for_loop: bool,
        id: u64,
        label: Option<String>,
        cond: Option<(Stm, Exp)>,
        body: Stm,
        invs: LoopInvs,
        decrease: Exps,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        modified_vars: Arc<Vec<UniqueIdent>>,
    },
    OpenInvariant(Exp, Stm),
    ClosureInner {
        body: Stm,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
    },
    Air(Arc<String>),
    Block(Stms),
}

pub type LocalDecl = Arc<LocalDeclX>;
#[derive(Debug)]
pub struct LocalDeclX {
    pub ident: UniqueIdent,
    pub typ: Typ,
    pub mutable: bool,
}

#[derive(Debug, Clone)]
pub enum UnwindSst {
    MayUnwind,
    NoUnwind,
    NoUnwindWhen(Exp),
}

#[derive(Debug, Clone, Copy)]
pub enum PostConditionKind {
    Ensures,
    DecreasesImplicitLemma,
    DecreasesBy,
}

#[derive(Debug, Clone)]
pub struct PostConditionSst {
    /// Identifier that holds the return value.
    /// May be referenced by `ens_exprs` or `ens_spec_precondition_stms`.
    pub dest: Option<VarIdent>,
    /// Post-conditions (only used in non-recommends-checking mode)
    pub ens_exps: Exps,
    /// Recommends checks (only used in recommends-checking mode)
    pub ens_spec_precondition_stms: Stms,
    /// Extra info about PostCondition for error reporting
    pub kind: PostConditionKind,
}

#[derive(Debug)]
pub struct FuncDeclSst {
    pub req_inv_pars: Pars,
    pub ens_pars: Pars,
    pub post_pars: Pars,
    pub reqs: Exps,
    pub enss: Exps,
    pub inv_masks: Arc<Vec<Exps>>,
    pub unwind_condition: Option<Exp>,
    pub fndef_axioms: Exps,
}

#[derive(Debug, Clone)]
pub struct FuncCheckSst {
    pub reqs: Exps,
    pub post_condition: Arc<PostConditionSst>,
    pub mask_set: Arc<crate::inv_masks::MaskSet>, // Actually AIR
    pub unwind: UnwindSst,
    pub body: Stm,
    pub local_decls: Arc<Vec<LocalDecl>>,
    pub statics: Arc<Vec<Fun>>,
}

#[derive(Debug, Clone)]
pub struct FuncSpecBodySst {
    pub decrease_when: Option<Exp>,
    pub termination_check: Option<FuncCheckSst>,
    pub body_exp: Exp,
}

#[derive(Debug, Clone)]
pub struct FuncAxiomsSst {
    pub spec_axioms: Option<FuncSpecBodySst>,
    pub proof_exec_axioms: Option<(Pars, Exp, Trigs)>,
}

#[derive(Debug, Clone)]
pub struct FunctionSstHas {
    pub has_body: bool,
    pub has_requires: bool,
    pub has_ensures: bool,
    pub has_decrease: bool,
    pub has_mask_spec: bool,
    pub has_return_name: bool,
    pub is_recursive: bool,
}

pub type FunctionSst = Arc<Spanned<FunctionSstX>>;
#[derive(Debug, Clone)]
pub struct FunctionSstX {
    pub name: Fun,
    pub kind: crate::ast::FunctionKind,
    pub vis_abs: crate::ast::Visibility,
    pub owning_module: Option<Path>,
    pub mode: crate::ast::Mode,
    pub fuel: u32,
    pub typ_params: crate::ast::Idents,
    pub typ_bounds: crate::ast::GenericBounds,
    pub pars: Pars,
    pub ret: Par,
    pub item_kind: crate::ast::ItemKind,
    pub publish: Option<bool>,
    pub attrs: crate::ast::FunctionAttrs,
    pub has: FunctionSstHas,
    pub decl: Arc<FuncDeclSst>,
    pub axioms: Arc<FuncAxiomsSst>,
    pub exec_proof_check: Option<Arc<FuncCheckSst>>,
    pub recommends_check: Option<Arc<FuncCheckSst>>,
}

pub type KrateSst = Arc<KrateSstX>;
#[derive(Debug)]
pub struct KrateSstX {
    pub functions: Vec<FunctionSst>,
    pub datatypes: Vec<crate::ast::Datatype>,
    pub traits: Vec<crate::ast::Trait>,
    pub trait_impls: Vec<crate::ast::TraitImpl>,
    pub assoc_type_impls: Vec<crate::ast::AssocTypeImpl>,
    pub reveal_groups: Vec<crate::ast::RevealGroup>,
}
