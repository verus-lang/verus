//! The VIR-AST Abstract Syntax Tree
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! VIR-AST follows the structure of Rust-HIR, but omits features that are not needed
//! for verification.

use crate::def::Spanned;
use crate::messages::{Message, Span};
pub use air::ast::{Binder, Binders};
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::fmt::Display;
use std::sync::Arc;
use vir_macros::{to_node_impl, ToDebugSNode};

/// Result<T, VirErr> is used when an error might need to be reported to the user
pub type VirErr = Message;

pub enum VirErrAs {
    Warning(VirErr),
    Note(VirErr),
}

/// A non-qualified name, such as a local variable name or type parameter name
pub type Ident = Arc<String>;
pub type Idents = Arc<Vec<Ident>>;

/// A fully-qualified name, such as a module name, function name, or datatype name
pub type Path = Arc<PathX>;
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PathX {
    pub krate: Option<Ident>, // None for local crate
    pub segments: Idents,
}

/// Static function identifier
pub type Fun = Arc<FunX>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunX {
    /// Path of function
    pub path: Path,
}

/// Describes what access other modules have to a function, datatype, etc.
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq)]
pub struct Visibility {
    /// None for pub
    /// Some(path) means visible to path and path's descendents
    pub restricted_to: Option<Path>,
}

/// Describes whether a variable, function, etc. is compiled or just used for verification
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Mode {
    /// Ghost (not compiled), used to represent specifications (requires, ensures, invariant)
    Spec,
    /// Ghost (not compiled), used to represent proofs of that specifications are satisfied
    Proof,
    /// Non-ghost (compiled code)
    Exec,
}

/// Describes integer types
#[derive(
    Copy,
    Clone,
    Debug,
    Serialize,
    Deserialize,
    ToDebugSNode,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord
)]
pub enum IntRange {
    /// The set of all mathematical integers Z (..., -2, -1, 0, 1, 2, ...)
    Int,
    /// The set of all natural numbers N (0, 1, 2, ...)
    Nat,
    /// n-bit unsigned numbers (natural numbers up to 2^n - 1) for the specified n: u32
    U(u32),
    /// n-bit signed numbers (integers -2^(n-1), ..., 2^(n-1) - 1) for the specified n: u32
    I(u32),
    /// Rust's usize type
    USize,
    /// Rust's isize type
    ISize,
}

/// Type information relevant to Rust but generally not relevant to the SMT encoding.
/// This information is relevant for resolving traits.
#[derive(
    Debug,
    Serialize,
    Deserialize,
    Hash,
    ToDebugSNode,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord
)]
pub enum TypDecoration {
    /// &T
    Ref,
    /// &mut T
    MutRef,
    /// Box<T>
    Box,
    /// Rc<T>
    Rc,
    /// Arc<T>
    Arc,
    /// Ghost<T>
    Ghost,
    /// Tracked<T>
    Tracked,
    /// !, represented as Never<()>
    Never,
}

#[derive(
    Copy,
    Clone,
    Debug,
    ToDebugSNode,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize
)]
pub enum Primitive {
    Array,
    Slice,
}

/// Rust type, but without Box, Rc, Arc, etc.
pub type Typ = Arc<TypX>;
pub type Typs = Arc<Vec<Typ>>;
// Because of ImplPaths in TypX::Datatype, TypX should not implement PartialEq, Eq
// See ast_util::types_equal instead
#[derive(Debug, Serialize, Deserialize, Hash, ToDebugSNode)]
pub enum TypX {
    /// Bool, Int, Datatype are translated directly into corresponding SMT types (they are not SMT-boxed)
    Bool,
    Int(IntRange),
    /// Tuple type (t1, ..., tn).  Note: ast_simplify replaces Tuple with Datatype.
    Tuple(Typs),
    /// `FnSpec` type (TODO rename from 'Lambda' to just 'FnSpec')
    /// (t1, ..., tn) -> t0.
    Lambda(Typs, Typ),
    /// Executable function types (with a requires and ensures)
    AnonymousClosure(Typs, Typ, usize),
    /// Datatype (concrete or abstract) applied to type arguments
    Datatype(Path, Typs, ImplPaths),
    /// Wrap type with extra information relevant to Rust but usually irrelevant to SMT encoding
    /// (though needed sometimes to encode trait resolution)
    Decorate(TypDecoration, Typ),
    /// Boxed for SMT encoding (unrelated to Rust Box type), can be unboxed:
    Boxed(Typ),
    /// Type parameter (inherently SMT-boxed, and cannot be unboxed)
    TypParam(Ident),
    /// Projection such as <D as T<S>>::X or <A as T>::X (SMT-boxed, and can sometimes be unboxed)
    Projection {
        // trait_typ_args[0] is Self type
        trait_typ_args: Typs,
        trait_path: Path,
        name: Ident,
    },
    /// Type of type identifiers
    TypeId,
    /// Const integer type argument (e.g. for array sizes)
    ConstInt(BigInt),
    /// AIR type, used internally during translation
    Air(air::ast::Typ),
    /// StrSlice type. Currently the pervasive StrSlice struct is "seen" as this type
    /// despite the fact that it is in fact a datatype
    StrSlice,
    /// UTF-8 character type
    Char,
    /// Other primitive type (applied to type arguments)
    Primitive(Primitive, Typs),
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum TriggerAnnotation {
    /// Automatically choose triggers for the expression containing this annotation,
    /// with no diagnostics printed
    AutoTrigger,
    AllTriggers,
    /// Each trigger group is named by either Some integer, or the unnamed group None.
    /// (None is just another name; it is no different from an integer-named group.)
    /// Example: #[trigger] expr is translated into Trigger(None) applied to expr
    /// Example: #[trigger(1, 2, 3)] expr is translated into three Trigger ops wrapped around expr
    ///   (Trigger(Some(1)), Trigger(Some(2)), Trigger(Some(3)))
    Trigger(Option<u64>),
}

/// Operations on Ghost and Tracked
#[derive(Copy, Clone, Debug, Serialize, Deserialize, Hash, PartialEq, Eq, ToDebugSNode)]
pub enum ModeCoercion {
    /// Mutable borrows (Ghost::borrow_mut and Tracked::borrow_mut) are treated specially by
    /// the mode checker when checking assignments.
    BorrowMut,
    /// All other cases are treated uniformly by the mode checker based on their op/from/to-mode.
    /// (This includes Ghost::borrow, Tracked::get, etc.)
    Other,
}

/// Primitive 0-argument operations
#[derive(Clone, Debug, Serialize, Deserialize, Hash, ToDebugSNode)]
pub enum NullaryOpr {
    /// convert a const generic into an expression, as in fn f<const N: usize>() -> usize { N }
    ConstGeneric(Typ),
    /// predicate representing a satisfied trait bound T(t1, ..., tn) for trait T
    TraitBound(Path, Typs),
}

/// Primitive unary operations
/// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum UnaryOp {
    /// boolean not
    Not,
    /// bitwise not
    BitNot,
    /// Mark an expression as a member of an SMT quantifier trigger group.
    /// Each trigger group becomes one SMT trigger containing all the expressions in the trigger group.
    Trigger(TriggerAnnotation),
    /// Force integer value into range given by IntRange (e.g. by using mod)
    Clip { range: IntRange, truncate: bool },
    /// Operations that coerce from/to builtin::Ghost or builtin::Tracked
    CoerceMode { op_mode: Mode, from_mode: Mode, to_mode: Mode, kind: ModeCoercion },
    /// Internal consistency check to make sure finalize_exp gets called
    /// (appears only briefly in SST before finalize_exp is called)
    MustBeFinalized,
    /// We don't give users direct access to the "height" function and Height types.
    /// However, it's useful to be able to trigger on the "height" function
    /// when using HeightCompare.  We manage this by having triggers.rs convert
    /// HeightCompare triggers into HeightTrigger, which is eventually translated
    /// into direct calls to the "height" function in the triggers.
    HeightTrigger,
    /// Used only for handling builtin::strslice_len
    StrLen,
    /// Used only for handling builtin::strslice_is_ascii
    StrIsAscii,
    /// Used only for handling casts from chars to ints
    CharToInt,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord, ToDebugSNode)]
pub struct FieldOpr {
    pub datatype: Path,
    pub variant: Ident,
    pub field: Ident,
    pub get_variant: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord, ToDebugSNode)]
pub enum IntegerTypeBoundKind {
    UnsignedMax,
    SignedMin,
    SignedMax,
    ArchWordBits,
}

/// More complex unary operations (requires Clone rather than Copy)
/// (Below, "boxed" refers to boxing types in the SMT encoding, not the Rust Box type)
#[derive(Clone, Debug, Serialize, Deserialize, Hash, ToDebugSNode)]
pub enum UnaryOpr {
    /// coerce Typ --> Boxed(Typ)
    Box(Typ),
    /// coerce Boxed(Typ) --> Typ
    Unbox(Typ),
    /// satisfies type invariant for Typ
    /// (should only be used when sst_to_air::typ_invariant returns Some(_))
    HasType(Typ),
    /// Test whether expression is a particular variant of a datatype
    IsVariant { datatype: Path, variant: Ident },
    /// Read .0, .1, etc. from tuple (Note: ast_simplify replaces this with Field)
    TupleField { tuple_arity: usize, field: usize },
    /// Read field from variant of datatype
    Field(FieldOpr),
    /// Bounded integer bounds. The argument is the arch word bits (16, 32, etc.)
    /// So e.g., IntegerTypeBound(SignedMax) applied to 8 would give 127
    /// The 'ArchWordBits' gives the word size in bits (ignore the argument).
    /// This can return any integer type, but that integer type needs to be large enough
    /// to hold the result.
    /// Mode is the minimum allowed mode (e.g., Spec for spec-only, Exec if allowed in exec).
    IntegerTypeBound(IntegerTypeBoundKind, Mode),
    /// Custom diagnostic message
    CustomErr(Arc<String>),
}

/// Arithmetic operation that might fail (overflow or divide by zero)
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum ArithOp {
    /// IntRange::Int +
    Add,
    /// IntRange::Int -
    Sub,
    /// IntRange::Int *
    Mul,
    /// IntRange::Int / defined as Euclidean (round towards -infinity, not round-towards zero)
    EuclideanDiv,
    /// IntRange::Int % defined as Euclidean (returns non-negative result even for negative divisor)
    EuclideanMod,
}

/// Bitwise operation
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum BitwiseOp {
    BitXor,
    BitAnd,
    BitOr,
    Shr,
    Shl,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum InequalityOp {
    /// IntRange::Int <=
    Le,
    /// IntRange::Int >=
    Ge,
    /// IntRange::Int <
    Lt,
    /// IntRange::Int >
    Gt,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum ChainedOp {
    Inequality(InequalityOp),
    MultiEq,
}

/// Primitive binary operations
/// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
/// Note that all integer operations are on mathematic integers (IntRange::Int),
/// not on finite-width integer types or nat.
/// Finite-width and nat operations are represented with a combination of IntRange::Int operations
/// and UnaryOp::Clip.
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum BinaryOp {
    /// boolean and (short-circuiting: right side is evaluated only if left side is true)
    And,
    /// boolean or (short-circuiting: right side is evaluated only if left side is false)
    Or,
    /// boolean xor (no short-circuiting)
    Xor,
    /// boolean implies (short-circuiting: right side is evaluated only if left side is true)
    Implies,
    /// the is_smaller_than builtin, used for decreases (true for <, false for ==)
    HeightCompare { strictly_lt: bool, recursive_function_field: bool },
    /// SMT equality for any type -- two expressions are exactly the same value
    /// Some types support compilable equality (Mode == Exec); others only support spec equality (Mode == Spec)
    Eq(Mode),
    /// not Eq
    Ne,
    /// arithmetic inequality
    Inequality(InequalityOp),
    /// IntRange operations that may require overflow or divide-by-zero checks
    Arith(ArithOp, Mode),
    /// Bit Vector Operators
    /// mode=Exec means we need overflow-checking
    Bitwise(BitwiseOp, Mode),
    /// Used only for handling builtin::strslice_get_char
    StrGetChar,
}

/// More complex binary operations (requires Clone rather than Copy)
#[derive(Clone, Debug, Serialize, Deserialize, Hash, ToDebugSNode)]
pub enum BinaryOpr {
    /// extensional equality ext_equal (true ==> deep extensionality)
    ExtEq(bool, Typ),
}

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum MultiOp {
    Chained(Arc<Vec<ChainedOp>>),
}

/// Use Ghost(x) or Tracked(x) to unwrap an argument
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct UnwrapParameter {
    // indicates Ghost or Tracked
    pub mode: Mode,
    // dummy name chosen for official Rust parameter name
    pub outer_name: Ident,
    // rename the parameter to a different name using a "let" binding
    pub inner_name: Ident,
}

/// Ghost annotations on functions and while loops; must appear at the beginning of function body
/// or while loop body
pub type HeaderExpr = Arc<HeaderExprX>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum HeaderExprX {
    /// Use Ghost(x) or Tracked(x) to unwrap an argument, renaming outer_name to inner_name
    UnwrapParameter(UnwrapParameter),
    /// Marker that trait declaration method body is omitted and should be erased
    NoMethodBody,
    /// Preconditions on exec/proof functions
    Requires(Exprs),
    /// Postconditions on exec/proof functions, with an optional name and type for the return value
    Ensures(Option<(Ident, Typ)>, Exprs),
    /// Recommended preconditions on spec functions, used to help diagnose mistakes in specifications.
    /// Checking of recommends is disabled by default.
    Recommends(Exprs),
    /// Invariants on loops
    Invariant(Exprs),
    /// Invariants + ensures on loops
    InvariantEnsures(Exprs),
    /// Decreases clauses for functions (possibly also for while loops, but this isn't implemented yet)
    Decreases(Exprs),
    /// Recursive function is uninterpreted when Expr is false
    DecreasesWhen(Expr),
    /// Proof function to prove termination for recursive functions
    DecreasesBy(Fun),
    /// The function might open the following invariants
    InvariantOpens(Exprs),
    /// The function might open any BUT the following invariants
    InvariantOpensExcept(Exprs),
    /// Make a function f opaque (definition hidden) within the current function body.
    /// (The current function body can later reveal f in specific parts of the current function body if desired.)
    Hide(Fun),
    /// `extra_dependency(f)` means that recursion-checking should act as if the current
    /// function calls `f`
    ExtraDependency(Fun),
}

/// Primitive constant values
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq, Hash)]
pub enum Constant {
    /// true or false
    Bool(bool),
    /// integer of arbitrary size
    Int(BigInt),
    /// Hold generated string slices in here
    StrSlice(Arc<String>),
    // Hold unicode values here
    Char(char),
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SpannedTyped<X> {
    pub span: Span,
    pub typ: Typ,
    pub x: X,
}

impl<X: Display> Display for SpannedTyped<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.x)
    }
}

/// Patterns for match expressions
pub type Pattern = Arc<SpannedTyped<PatternX>>;
pub type Patterns = Arc<Vec<Pattern>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub enum PatternX {
    /// _
    /// True if this is implicitly added from a ..
    Wildcard(bool),
    /// x or mut x
    Var {
        name: Ident,
        mutable: bool,
    },
    /// Note: ast_simplify replaces this with Constructor
    Tuple(Patterns),
    /// Match constructor of datatype Path, variant Ident
    /// For tuple-style variants, the patterns appear in order and are named "0", "1", etc.
    /// For struct-style variants, the patterns may appear in any order.
    Constructor(Path, Ident, Binders<Pattern>),
    Or(Pattern, Pattern),
}

/// Arms of match expressions
pub type Arm = Arc<Spanned<ArmX>>;
pub type Arms = Arc<Vec<Arm>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct ArmX {
    /// pattern
    pub pattern: Pattern,
    /// "if" condition on a case
    pub guard: Expr,
    /// expression or statement the executes when case matches
    pub body: Expr,
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq, ToDebugSNode)]
pub enum LoopInvariantKind {
    Invariant,
    InvariantEnsures,
    Ensures,
}

pub type LoopInvariants = Arc<Vec<LoopInvariant>>;
#[derive(Debug, Serialize, Deserialize, Clone, ToDebugSNode)]
pub struct LoopInvariant {
    pub kind: LoopInvariantKind,
    pub inv: Expr,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum BuiltinSpecFun {
    ClosureReq,
    ClosureEns,
}

/// Path of each impl that is used to satisfy a trait bound when instantiating the type parameter
/// This is used to name the "dictionary" that is (conceptually) passed along with the
/// type argument (see recursive_types.rs)
// REVIEW: should trait_typ_args also have ImplPaths?
pub type ImplPaths = Arc<Vec<Path>>;

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum CallTargetKind {
    /// Statically known function
    Static,
    /// Dynamically dispatched method.  Optionally specify the statically resolved target if known.
    Method(Option<(Fun, Typs, ImplPaths)>),
}

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum CallTarget {
    /// Regular function, passing some type arguments
    Fun(CallTargetKind, Fun, Typs, ImplPaths, AutospecUsage),
    /// Call a dynamically computed FnSpec (no type arguments allowed),
    /// where the function type is specified by the GenericBound of typ_param.
    FnSpec(Expr),
    BuiltinSpecFun(BuiltinSpecFun, Typs),
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq, Hash)]
pub enum VarAt {
    Pre,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq, Hash)]
pub enum InvAtomicity {
    Atomic,
    NonAtomic,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq, Hash)]
pub enum AssertQueryMode {
    NonLinear,
    BitVector,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Quant {
    pub quant: air::ast::Quant,
}

/// Computation mode for assert_by_compute
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum ComputeMode {
    /// After simplifying an expression as far as possible,
    /// pass the remainder as an assertion to Z3
    Z3,
    /// Asserted expression must simplify all the way to True
    ComputeOnly,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum AutospecUsage {
    /// This function should be lowered by autospec iff the
    /// target function has an autospec attribute.
    IfMarked,
    /// Do not apply autospec. (This might be because we already applied it during lowering,
    /// or because it doesn't apply to this function.)
    Final,
}

/// Expression, similar to rustc_hir::Expr
pub type Expr = Arc<SpannedTyped<ExprX>>;
pub type Exprs = Arc<Vec<Expr>>;
#[derive(Debug, Serialize, Deserialize)]
#[to_node_impl(name = ">")]
pub enum ExprX {
    /// Constant
    Const(Constant),
    /// Local variable as a right-hand side
    Var(Ident),
    /// Local variable as a left-hand side
    VarLoc(Ident),
    /// Local variable, at a different stage (e.g. a mutable reference in the post-state)
    VarAt(Ident, VarAt),
    /// Use of a const variable.  Note: ast_simplify replaces this with Call.
    ConstVar(Fun, AutospecUsage),
    /// Use of a static variable.
    StaticVar(Fun),
    /// Mutable reference (location)
    Loc(Expr),
    /// Call to a function passing some expression arguments
    Call(CallTarget, Exprs),
    /// Note: ast_simplify replaces this with Ctor
    Tuple(Exprs),
    /// Construct datatype value of type Path and variant Ident,
    /// with field initializers Binders<Expr> and an optional ".." update expression.
    /// For tuple-style variants, the field initializers appear in order and are named "_0", "_1", etc.
    /// For struct-style variants, the field initializers may appear in any order.
    Ctor(Path, Ident, Binders<Expr>, Option<Expr>),
    /// Primitive 0-argument operation
    NullaryOpr(NullaryOpr),
    /// Primitive unary operation
    Unary(UnaryOp, Expr),
    /// Special unary operator
    UnaryOpr(UnaryOpr, Expr),
    /// Primitive binary operation
    Binary(BinaryOp, Expr, Expr),
    /// Special binary operation
    BinaryOpr(BinaryOpr, Expr, Expr),
    /// Primitive multi-operand operation
    Multi(MultiOp, Exprs),
    /// Quantifier (forall/exists), binding the variables in Binders, with body Expr
    Quant(Quant, Binders<Typ>, Expr),
    /// Specification closure
    Closure(Binders<Typ>, Expr),
    /// Executable closure
    ExecClosure {
        params: Binders<Typ>,
        body: Expr,
        requires: Exprs,
        ensures: Exprs,
        ret: Binder<Typ>,
        /// The 'external spec' is an Option because it gets filled in during
        /// ast_simplify. It contains the assumptions that surrounding context
        /// can assume about a closure object after it is created.
        external_spec: Option<(Ident, Expr)>,
    },
    /// Array literal (can also be used for sequence literals in the future)
    ArrayLiteral(Exprs),
    /// Choose specification values satisfying a condition, compute body
    Choose { params: Binders<Typ>, cond: Expr, body: Expr },
    /// Manually supply triggers for body of quantifier
    WithTriggers { triggers: Arc<Vec<Exprs>>, body: Expr },
    /// Assign to local variable
    /// init_not_mut = true ==> a delayed initialization of a non-mutable variable
    Assign { init_not_mut: bool, lhs: Expr, rhs: Expr, op: Option<BinaryOp> },
    /// Reveal definition of an opaque function with some integer fuel amount
    Fuel(Fun, u32),
    /// Reveal a string
    RevealString(Arc<String>),
    /// Header, which must appear at the beginning of a function or while loop.
    /// Note: this only appears temporarily during rust_to_vir construction, and should not
    /// appear in the final Expr produced by rust_to_vir (see vir::headers::read_header).
    Header(HeaderExpr),
    /// Assert or assume
    AssertAssume { is_assume: bool, expr: Expr },
    /// Assert-forall or assert-by statement
    AssertBy { vars: Binders<Typ>, require: Expr, ensure: Expr, proof: Expr },
    /// `assert_by` with a dedicated prover option (nonlinear_arith, bit_vector)
    AssertQuery { requires: Exprs, ensures: Exprs, proof: Expr, mode: AssertQueryMode },
    /// Assertion discharged via computation
    AssertCompute(Expr, ComputeMode),
    /// If-else
    If(Expr, Expr, Option<Expr>),
    /// Match (Note: ast_simplify replaces Match with other expressions)
    Match(Expr, Arms),
    /// Loop (either "while", cond = Some(...), or "loop", cond = None), with invariants
    Loop { label: Option<String>, cond: Option<Expr>, body: Expr, invs: LoopInvariants },
    /// Open invariant
    OpenInvariant(Expr, Binder<Typ>, Expr, InvAtomicity),
    /// Return from function
    Return(Option<Expr>),
    /// break or continue
    BreakOrContinue { label: Option<String>, is_break: bool },
    /// Enter a Rust ghost block, which will be erased during compilation.
    /// In principle, this is not needed, because we can infer which code to erase using modes.
    /// However, we can't easily communicate the inferred modes back to rustc for erasure
    /// and lifetime checking -- rustc needs syntactic annotations for these, and the mode checker
    /// needs to confirm that these annotations agree with what would have been inferred.
    Ghost { alloc_wrapper: bool, tracked: bool, expr: Expr },
    /// Sequence of statements, optionally including an expression at the end
    Block(Stmts, Option<Expr>),
}

/// Statement, similar to rustc_hir::Stmt
pub type Stmt = Arc<Spanned<StmtX>>;
pub type Stmts = Arc<Vec<Stmt>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum StmtX {
    /// Single expression
    Expr(Expr),
    /// Declare a local variable, which may be mutable, and may have an initial value
    /// The declaration may contain a pattern;
    /// however, ast_simplify replaces all patterns with PatternX::Var
    Decl { pattern: Pattern, mode: Mode, init: Option<Expr> },
}

/// Function parameter
pub type Param = Arc<Spanned<ParamX>>;
pub type Params = Arc<Vec<Param>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub struct ParamX {
    pub name: Ident,
    pub typ: Typ,
    pub mode: Mode,
    /// An &mut parameter
    pub is_mut: bool,
    /// If the parameter uses a Ghost(x) or Tracked(x) pattern to unwrap the value, this is
    /// the mode of the resulting unwrapped x variable (Spec for Ghost(x), Proof for Tracked(x)).
    /// We also save a copy of the original wrapped name for lifetime_generate
    pub unwrapped_info: Option<(Mode, Ident)>,
}

pub type GenericBound = Arc<GenericBoundX>;
pub type GenericBounds = Arc<Vec<GenericBound>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum GenericBoundX {
    /// Implemented trait T(t1, ..., tn) where t1...tn usually contain some type parameters
    // REVIEW: add ImplPaths here?
    Trait(Path, Typs),
}

/// When instantiating type S<A> with A = T in a recursive type definition,
/// is T allowed to include the one of recursively defined types?
/// Example:
///   enum Foo { Rec(S<Box<Foo>>), None }
///   enum Bar { Rec(S<Box<Bar>>) }
///   (instantiates A with recursive type Box<Foo> or Box<Bar>)
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, Copy, PartialEq, Eq)]
pub enum AcceptRecursiveType {
    /// rejects the Foo example above
    /// (because A may occur negatively in S)
    Reject,
    /// accepts the Foo example above because the occurrence is in Rec,
    /// which is not the ground variant for Foo (None is the ground variant for Foo),
    /// but rejects Bar because Rec is the ground variant for Bar (since there is no None variant)
    /// (because A occurs only strictly positively in S, but may occur in S's ground variant)
    RejectInGround,
    /// accepts both Foo and Bar
    /// (because A occurs only strictly positively in S, and does not occur in S's ground variant)
    Accept,
}
/// Each type parameter is (name: Ident, GenericBound, AcceptRecursiveType)
pub type TypPositives = Arc<Vec<(Ident, AcceptRecursiveType)>>;

pub type FunctionAttrs = Arc<FunctionAttrsX>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Default, Clone)]
pub struct FunctionAttrsX {
    /// Erasure and lifetime checking based on ghost blocks
    pub uses_ghost_blocks: bool,
    /// Inline spec function for SMT
    pub inline: bool,
    /// List of functions that this function wants to view as opaque
    pub hidden: Arc<Vec<Fun>>,
    /// Create a global axiom saying forall params, require ==> ensure
    pub broadcast_forall: bool,
    /// In triggers_auto, don't use this function as a trigger
    pub no_auto_trigger: bool,
    /// Custom error message to display when a pre-condition fails
    pub custom_req_err: Option<String>,
    /// When used in a ghost context, redirect to a specified spec function
    pub autospec: Option<Fun>,
    /// Verify using bitvector theory
    pub bit_vector: bool,
    /// Is atomic (i.e., can be inside an invariant block)
    pub atomic: bool,
    /// Verify non_linear arithmetic using Singular
    pub integer_ring: bool,
    /// This is a proof of termination for another spec function
    pub is_decrease_by: bool,
    /// In a spec function, check the body for violations of recommends
    pub check_recommends: bool,
    /// set option smt.arith.nl=true
    pub nonlinear: bool,
    /// Use a dedicated Z3 process for this single query
    pub spinoff_prover: bool,
    /// Memoize function call results during interpretation
    pub memoize: bool,
    /// override default rlimit
    pub rlimit: Option<f32>,
}

/// Function specification of its invariant mask
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum MaskSpec {
    InvariantOpens(Exprs),
    InvariantOpensExcept(Exprs),
    NoSpec,
}

#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub enum FunctionKind {
    Static,
    /// Method declaration inside a trait
    TraitMethodDecl {
        trait_path: Path,
    },
    /// Method implementation inside an impl, implementing a trait method for a trait for a type
    TraitMethodImpl {
        method: Fun,
        /// Path of the impl (e.g. "impl2") that contains the method implementation
        impl_path: Path,
        trait_path: Path,
        trait_typ_args: Typs,
    },
    /// These should get demoted into Static functions in `demote_foreign_traits`.
    /// This really only exists so that we can check the trait really is foreign.
    ForeignTraitMethodImpl(Path),
}

/// Function, including signature and body
pub type Function = Arc<Spanned<FunctionX>>;
#[derive(Debug, Serialize, Deserialize, Clone)]
#[to_node_impl]
pub struct FunctionX {
    /// Name of function
    pub name: Fun,
    /// Proxy used to declare the spec of this function
    /// (e.g., some function marked `external_fn_specification`)
    pub proxy: Option<Spanned<Path>>,
    /// Kind (translation to AIR is different for each different kind)
    pub kind: FunctionKind,
    /// Access control (public/private)
    pub visibility: Visibility,
    /// Owning module
    pub owning_module: Option<Path>,
    /// exec functions are compiled, proof/spec are erased
    /// exec/proof functions can have requires/ensures, spec cannot
    /// spec functions can be used in requires/ensures, proof/exec cannot
    pub mode: Mode,
    /// Default amount of fuel: 0 means opaque, >= 1 means visible
    /// For recursive functions, fuel determines the number of unfoldings that the SMT solver sees
    pub fuel: u32,
    /// Type parameters to generic functions
    pub typ_params: Idents,
    /// Type bounds of generic functions
    pub typ_bounds: GenericBounds,
    /// Function parameters
    pub params: Params,
    /// Return value (unit return type is treated specially; see FunctionX::has_return in ast_util)
    pub ret: Param,
    /// Preconditions (requires for proof/exec functions, recommends for spec functions)
    pub require: Exprs,
    /// Postconditions (proof/exec functions only)
    pub ensure: Exprs,
    /// Decreases clause to ensure recursive function termination
    /// decrease.len() == 0 means no decreases clause
    /// decrease.len() >= 1 means list of expressions, interpreted in lexicographic order
    pub decrease: Exprs,
    /// If Expr is true for the arguments to the function,
    /// the function is defined according to the function body and the decreases clauses must hold.
    /// If Expr is false, the function is uninterpreted, the body and decreases clauses are ignored.
    pub decrease_when: Option<Expr>,
    /// Prove termination with a separate proof function
    pub decrease_by: Option<Fun>,
    /// For broadcast_forall functions, poly sets this to Some((params, reqs ==> enss))
    /// where params and reqs ==> enss use coerce_typ_to_poly rather than coerce_typ_to_native
    pub broadcast_forall: Option<(Params, Expr)>,
    /// MaskSpec that specifies what invariants the function is allowed to open
    pub mask_spec: MaskSpec,
    /// Allows the item to be a const declaration or static
    pub item_kind: ItemKind,
    /// For public spec functions, publish == None means that the body is private
    /// even though the function is public, the bool indicates false = opaque, true = visible
    /// the body is public
    pub publish: Option<bool>,
    /// Various attributes
    pub attrs: FunctionAttrs,
    /// Body of the function (may be None for foreign functions or for external_body functions)
    pub body: Option<Expr>,
    /// Extra dependencies, only used for for the purposes of recursion-well-foundedness
    /// Useful only for trusted fns.
    pub extra_dependencies: Vec<Fun>,
}

#[derive(Debug, Serialize, Deserialize, Clone, ToDebugSNode, Copy)]
pub enum ItemKind {
    Function,
    /// This function is actually a const declaration;
    /// we treat const declarations as functions with 0 arguments, having mode == Spec.
    /// However, if ret.x.mode != Spec, there are some differences: the const can dually be used as spec,
    /// and the body is restricted to a subset of expressions that are spec-safe.
    Const,
    /// Static is kind of similar to const, in that we treat it as a 0-argument function.
    /// The main difference is what happens when you reference the static or const.
    /// For a const, it's as if you call the function every time you reference it.
    /// For a static, it's as if you call the function once at the beginning of the program.
    /// The difference is most obvious when the item of a type that is not Copy.
    /// For example, if a const/static has type PCell, then:
    ///  - If it's a const, it will get a different id() every time it is referenced from code
    ///  - If it's a static, every use will have the same id()
    /// This initially seems a bit paradoxical; const and static can only call 'const' functions,
    /// so they can only be deterministic, right? But for something like cell, the 'id'
    /// (the nondeterministic part) is purely ghost.
    Static,
}

/// Single field in a variant
pub type Field = Binder<(Typ, Mode, Visibility)>;
/// List of fields in a variant
/// For tuple-style variants, the fields appear in order and are named "0", "1", etc.
/// For struct-style variants, the fields may appear in any order
pub type Fields = Binders<(Typ, Mode, Visibility)>;
pub type Variant = Binder<Fields>;
pub type Variants = Binders<Fields>;

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum DatatypeTransparency {
    Never,
    WhenVisible(Visibility),
}

/// struct or enum
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct DatatypeX {
    pub path: Path,
    /// Similar to FunctionX proxy field.
    /// If this datatype is declared via a proxy (a type labeled external_type_specification)
    /// then this points to the proxy.
    /// e.g., we might have,
    ///   path = core::option::Option
    ///   proxy = vstd::std_specs::core::ExOption
    pub proxy: Option<Spanned<Path>>,
    pub owning_module: Option<Path>,
    pub visibility: Visibility,
    pub transparency: DatatypeTransparency,
    pub typ_params: TypPositives,
    pub typ_bounds: GenericBounds,
    pub variants: Variants,
    pub mode: Mode,
    /// Generate ext_equal lemmas for datatype
    pub ext_equal: bool,
}
pub type Datatype = Arc<Spanned<DatatypeX>>;
pub type Datatypes = Vec<Datatype>;

pub type Trait = Arc<Spanned<TraitX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct TraitX {
    pub name: Path,
    pub visibility: Visibility,
    // REVIEW: typ_params does not yet explicitly include Self (right now, Self is implicit)
    pub typ_params: TypPositives,
    pub typ_bounds: GenericBounds,
    pub assoc_typs: Arc<Vec<Ident>>,
    pub assoc_typs_bounds: GenericBounds,
    pub methods: Arc<Vec<Fun>>,
}

/// impl<typ_params> trait_name<trait_typ_args[1..]> for trait_typ_args[0] { type name = typ; }
pub type AssocTypeImpl = Arc<Spanned<AssocTypeImplX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct AssocTypeImplX {
    pub name: Ident,
    /// Path of the impl (e.g. "impl2") that contains "type name = typ;"
    pub impl_path: Path,
    pub typ_params: Idents,
    pub typ_bounds: GenericBounds,
    pub trait_path: Path,
    pub trait_typ_args: Typs,
    pub typ: Typ,
    /// Paths of the impls that are used to satisfy the bounds on the associated type
    pub impl_paths: ImplPaths,
}

pub type TraitImpl = Arc<Spanned<TraitImplX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct TraitImplX {
    /// Path of the impl (e.g. "impl2")
    pub impl_path: Path,
    // typ_params of impl (unrelated to typ_params of trait)
    pub typ_params: Idents,
    pub typ_bounds: GenericBounds,
    pub trait_path: Path,
    pub trait_typ_args: Typs,
    pub trait_typ_arg_impls: ImplPaths,
}

#[derive(Clone, Debug, Hash, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq)]
pub enum WellKnownItem {
    DropTrait,
}

pub type Module = Arc<Spanned<ModuleX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct ModuleX {
    pub path: Path,
    // add attrs here
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, ToDebugSNode)]
pub enum ArchWordBits {
    Either32Or64,
    Exactly(u32),
}

impl ArchWordBits {
    pub fn min_bits(&self) -> u32 {
        match self {
            ArchWordBits::Either32Or64 => 32,
            ArchWordBits::Exactly(v) => *v,
        }
    }
    pub fn num_bits(&self) -> Option<u32> {
        match self {
            ArchWordBits::Either32Or64 => None,
            ArchWordBits::Exactly(v) => Some(*v),
        }
    }
}

impl Default for ArchWordBits {
    fn default() -> Self {
        ArchWordBits::Either32Or64
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct Arch {
    pub word_bits: ArchWordBits,
}

/// An entire crate
pub type Krate = Arc<KrateX>;
#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct KrateX {
    /// All functions in the crate, plus foreign functions
    pub functions: Vec<Function>,
    /// All datatypes in the crate
    pub datatypes: Vec<Datatype>,
    /// All traits in the crate
    pub traits: Vec<Trait>,
    /// Every impl in the crate of a trait
    pub trait_impls: Vec<TraitImpl>,
    /// All associated type impls in the crate
    pub assoc_type_impls: Vec<AssocTypeImpl>,
    /// List of all modules in the crate
    pub modules: Vec<Module>,
    /// List of all 'external' functions in the crate (only useful for diagnostics)
    pub external_fns: Vec<Fun>,
    /// List of all 'external' types in the crate (only useful for diagnostics)
    pub external_types: Vec<Path>,
    /// Map rustc-based internal paths to friendlier names for error messages
    pub path_as_rust_names: Vec<(Path, String)>,
    /// Arch info
    pub arch: Arch,
}
