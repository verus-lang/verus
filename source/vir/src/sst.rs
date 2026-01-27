//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{
    AssertQueryMode, BinaryOp, Constant, Dt, Fun, Mode, NullaryOpr, Path, Quant, SpannedTyped, Typ,
    Typs, UnaryOp, UnaryOpr, VarAt, VarBinders, VarIdent,
};
use crate::def::Spanned;
use crate::interpreter::InterpExp;
use crate::messages::{Message, Span};
use air::ast::{Binders, Ident};
use std::sync::Arc;
use vir_macros::ToDebugSNode;

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

// For AssertBy, this records the LocalDecl vars that correspond to the VarBinders
// (used by sst_elaborate.rs and poly.rs)
pub type AssertByLocals = Option<Arc<Vec<VarIdent>>>;

pub type Bnd = Arc<Spanned<BndX>>;
#[derive(Clone, Debug, ToDebugSNode)]
pub enum BndX {
    Let(VarBinders<Exp>),
    Quant(Quant, VarBinders<Typ>, Trigs, AssertByLocals),
    Lambda(VarBinders<Typ>, Trigs),
    Choose(VarBinders<Typ>, Trigs, Exp),
}

// TODO: remove UniqueIdent
pub type UniqueIdent = VarIdent;

#[derive(Debug, Clone, Hash, PartialEq, Eq, ToDebugSNode)]
pub enum InternalFun {
    ClosureReq,
    ClosureEns,
    DefaultEns,
    CheckDecreaseInt,
    CheckDecreaseHeight,
    OpenInvariantMask(Fun, usize),
}

#[derive(Debug, Clone, Hash, ToDebugSNode)]
pub enum CallFun {
    // static/method Fun, plus an optional resolved Fun for methods
    Fun(Fun, Option<(Fun, Typs)>),
    Recursive(Fun),
    InternalFun(InternalFun),
}

pub type Exp = Arc<SpannedTyped<ExpX>>;
pub type Exps = Arc<Vec<Exp>>;
#[derive(Debug, Clone, ToDebugSNode)]
pub enum ExpX {
    /// Literal constant (integers, booleans, etc.)
    Const(Constant),
    /// Local variable reference
    Var(UniqueIdent),
    /// Reference to a static or const item
    StaticVar(Fun),
    /// L-value reference to a variable's memory location (for mutable borrows)
    VarLoc(UniqueIdent),
    /// Variable value at a specific program point (e.g., `old(x)` in postconditions)
    VarAt(UniqueIdent, VarAt),
    /// L-value derived from an expression (e.g., `(*p)` or `a[i]`)
    /// Allowed nodes inside a Loc are:
    ///  - `VarLoc`
    ///  - `Field` (unary op)
    ///  - `DerefMut` (unary op)
    ///  - `Index` (binary op) (the index argument must be a non-mutable Var)
    Loc(Exp),
    /// Snapshot reference for generating AIR Old expressions; only used during sst_to_air
    Old(Ident, UniqueIdent),
    /// Call to a spec function (pure, no side effects)
    Call(CallFun, Typs, Exps),
    /// Application of a first-class function value (spec closure)
    CallLambda(Exp, Exps),
    /// Datatype constructor with field bindings
    Ctor(Dt, Ident, Binders<Exp>),
    /// Built-in nullary operator (e.g., `ConstInt`, `TraitBound`)
    NullaryOpr(NullaryOpr),
    /// Standard unary operator (e.g., `!`, `-`)
    Unary(UnaryOp, Exp),
    /// Extended unary operator (e.g., `IsVariant`, `TupleField`)
    UnaryOpr(UnaryOpr, Exp),
    /// Standard binary operator (e.g., `+`, `&&`, `==`)
    Binary(BinaryOp, Exp, Exp),
    /// Extended binary operator (e.g., `ExtEq` for extensional equality)
    BinaryOpr(crate::ast::BinaryOpr, Exp, Exp),
    /// Conditional expression (if-then-else); all three branches are pure
    If(Exp, Exp, Exp),
    /// Attaches trigger annotations to a quantified expression
    WithTriggers(Trigs, Exp),
    /// Binding construct: let, forall, exists, lambda, or choose
    Bind(Bnd, Exp),
    /// Reference to an exec function as a first-class value
    ExecFnByName(Fun),
    /// Fixed-size array literal
    ArrayLiteral(Exps),
    /// Internal interpreter value; should never escape the interpreter
    Interp(InterpExp),
    /// Fuel constant for controlling recursive function unrolling depth
    FuelConst(usize),
}

#[derive(Debug, Clone, Copy, ToDebugSNode)]
pub enum ParPurpose {
    MutPre,
    MutPost,
    Regular,
}

/// Function parameter
pub type Par = Arc<Spanned<ParX>>;
pub type Pars = Arc<Vec<Par>>;
#[derive(Debug, Clone, ToDebugSNode)]
pub struct ParX {
    pub name: VarIdent,
    pub typ: Typ,
    pub mode: Mode,
    pub is_mut: bool,
    pub purpose: ParPurpose,
}

#[derive(Clone, Debug, ToDebugSNode)]
pub struct Dest {
    pub dest: Exp,
    pub is_init: bool,
}

pub type LoopInvs = Arc<Vec<LoopInv>>;
#[derive(Debug, Clone, ToDebugSNode)]
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
#[derive(Debug, ToDebugSNode)]
pub enum StmX {
    /// Call to exec/proof function (or spec function when checking preconditions).
    /// Unlike `ExpX::Call`, this has side effects and may modify state.
    Call {
        fun: Fun,
        /// For trait method calls, the resolved concrete implementation
        resolved_method: Option<(Fun, Typs)>,
        mode: Mode,
        /// Some(is_trait_default) for calls to dynamically-resolved functions (DynamicResolved) with a default impl
        is_trait_default: Option<bool>,
        typ_args: Typs,
        args: Exps,
        /// If Some, this is a placeholder call to be expanded into split assertions for error reporting
        split: Option<Message>,
        dest: Option<Dest>,
        assert_id: Option<AssertId>,
    },
    /// Assertion to be verified by the SMT solver; reports Stm's span on failure plus optional extra info
    Assert(Option<AssertId>, Option<Message>, Exp),
    /// Bitvector-specific assertion using a dedicated decision procedure
    AssertBitVector { requires: Exps, ensures: Exps },
    /// Isolated verification query (e.g., `assert ... by(...)`) with its own SMT context
    AssertQuery {
        mode: AssertQueryMode,
        /// Type invariant expressions to assume
        typ_inv_exps: Exps,
        /// Variables with type invariants
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        body: Stm,
    },
    /// Assertion checked by verification-time computation/interpretation
    AssertCompute(Option<AssertId>, Exp, crate::ast::ComputeMode),
    /// Add assumption to verification context (trusted, not checked)
    Assume(Exp),
    /// Assignment to a mutable variable or location
    Assign { lhs: Dest, rhs: Exp },
    /// Set fuel level for a recursive function (controls unrolling depth)
    Fuel(Fun, u32),
    /// Make a string literal available for use in specifications (hidden by default for perf reasons)
    RevealString(Arc<String>),
    /// Marks unreachable code; verification assumes this path is never taken
    DeadEnd(Stm),
    /// Function return: asserts postcondition holds, then exits function.
    /// If `inside_body` is true, adds `assume false` afterward (early return).
    Return {
        assert_id: Option<AssertId>,
        base_error: Message,
        ret_exp: Option<Exp>,
        inside_body: bool,
    },
    /// Loop control flow to a labeled or innermost loop
    BreakOrContinue { label: Option<String>, is_break: bool },
    /// Conditional statement (condition, then-branch, optional else-branch)
    If(Exp, Stm, Option<Stm>),
    /// Loop with invariants and termination measure.
    /// We either have (1) a simple while loop or (2) a complex loop:
    /// 1. cond = Some(...), all invs are true on entry and exit, no break statements
    /// 2. cond = None, invs may be false at_entry/at_exit, may have break statements
    /// Any while loop not satisfying (1) is converted to (2).
    Loop {
        /// If true, loop body is verified in isolation (no outer context)
        loop_isolation: bool,
        /// True if this was originally a for loop (affects error messages)
        is_for_loop: bool,
        /// Unique identifier for this loop instance
        id: u64,
        label: Option<String>,
        /// For simple while loops: (condition setup statements, condition expression)
        cond: Option<(Stm, Exp)>,
        body: Stm,
        /// Loop invariants with info about whether they hold at entry/exit/both
        invs: LoopInvs,
        /// Termination measure (must decrease on each iteration)
        decrease: Exps,
        /// Variables requiring type invariant assumptions
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        /// Variables potentially modified by the loop body
        modified_vars: Arc<Vec<UniqueIdent>>,
    },
    /// Atomic invariant opening for concurrent verification
    OpenInvariant(Stm),
    /// Body of an exec closure, with associated type invariants
    ClosureInner { body: Stm, typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>> },
    /// Raw AIR code injection (for internal use only)
    Air(Arc<String>),
    /// Sequential composition of statements
    Block(Stms),
}

// poly.rs uses the specific kind of each local to decide on a poly/native type for the local
#[derive(Debug, Clone, Copy, ToDebugSNode)]
pub enum LocalDeclKind {
    Param { mutable: bool },
    Return,
    StmtLet { mutable: bool },
    // temp var inherits kind of the initializer used to assign to it:
    TempViaAssign,
    Decreases,
    StmCallArg { native: bool },
    Assert,
    AssertByVar { native: bool },
    LetBinder,
    QuantBinder,
    ChooseBinder,
    ClosureBinder,
    ExecClosureId,
    ExecClosureParam,
    ExecClosureRet,
    Nondeterministic,
    OpenInvariantInnerTemp,
    BorrowMut,
}

pub type LocalDecl = Arc<LocalDeclX>;
#[derive(Debug, Clone, ToDebugSNode)]
pub struct LocalDeclX {
    pub ident: UniqueIdent,
    pub typ: Typ,
    pub kind: LocalDeclKind,
}

#[derive(Debug, Clone, ToDebugSNode)]
pub enum UnwindSst {
    MayUnwind,
    NoUnwind,
    NoUnwindWhen(Exp),
}

#[derive(Debug, Clone, Copy, ToDebugSNode)]
pub enum PostConditionKind {
    Ensures,
    DecreasesImplicitLemma,
    DecreasesBy,
    EnsuresSafeApiCheck,
}

#[derive(Debug, Clone, ToDebugSNode)]
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

#[derive(Debug, ToDebugSNode)]
pub struct FuncDeclSst {
    pub req_inv_pars: Pars,
    pub ens_pars: Pars,
    pub reqs: Exps,
    /// (regular ensures, trait-default ensures)
    pub enss: (Exps, Exps),
    pub inv_masks: Arc<Vec<Exps>>,
    pub unwind_condition: Option<Exp>,
    pub fndef_axioms: Exps,
}

#[derive(Debug, Clone, ToDebugSNode)]
pub struct FuncCheckSst {
    pub reqs: Exps,
    pub post_condition: Arc<PostConditionSst>,
    pub unwind: UnwindSst,
    pub body: Stm,
    pub local_decls: Arc<Vec<LocalDecl>>,
    /// LocalDeclKind::Decreases have an assignment that must be carried into loop_isolation(false):
    pub local_decls_decreases_init: Stms,
    pub statics: Arc<Vec<Fun>>,
}

#[derive(Debug, Clone, ToDebugSNode)]
pub struct FuncSpecBodySst {
    pub decrease_when: Option<Exp>,
    pub termination_check: Option<FuncCheckSst>,
    pub body_exp: Exp,
}

#[derive(Debug, Clone, ToDebugSNode)]
pub struct FuncAxiomsSst {
    pub spec_axioms: Option<FuncSpecBodySst>,
    pub proof_exec_axioms: Option<(Pars, Exp, Trigs)>,
}

#[derive(Debug, Clone, ToDebugSNode)]
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
#[derive(Debug, Clone, ToDebugSNode)]
pub struct FunctionSstX {
    pub name: Fun,
    pub kind: crate::ast::FunctionKind,
    pub body_visibility: crate::ast::BodyVisibility,
    pub owning_module: Option<Path>,
    pub mode: crate::ast::Mode,
    pub opaqueness: crate::ast::Opaqueness,
    pub typ_params: crate::ast::Idents,
    pub typ_bounds: crate::ast::GenericBounds,
    pub pars: Pars,
    pub ret: Par,
    pub ens_has_return: bool,
    pub item_kind: crate::ast::ItemKind,
    pub attrs: crate::ast::FunctionAttrs,
    pub has: FunctionSstHas,
    pub decl: Arc<FuncDeclSst>,
    pub axioms: Arc<FuncAxiomsSst>,
    pub exec_proof_check: Option<Arc<FuncCheckSst>>,
    pub recommends_check: Option<Arc<FuncCheckSst>>,
    pub safe_api_check: Option<Arc<FuncCheckSst>>,
}

pub type KrateSst = Arc<KrateSstX>;
#[derive(Debug)]
pub struct KrateSstX {
    pub functions: Vec<FunctionSst>,
    pub datatypes: Vec<crate::ast::Datatype>,
    pub opaque_types: Vec<crate::ast::OpaqueType>,
    pub traits: Vec<crate::ast::Trait>,
    pub trait_impls: Vec<crate::ast::TraitImpl>,
    pub assoc_type_impls: Vec<crate::ast::AssocTypeImpl>,
    pub reveal_groups: Vec<crate::ast::RevealGroup>,
}
