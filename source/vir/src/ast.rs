//! The VIR-AST Abstract Syntax Tree
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! VIR-AST follows the structure of Rust-HIR, but omits features that are not needed
//! for verification.

use crate::def::Spanned;
use air::ast::{Quant, Span};
use std::sync::Arc;

pub use air::ast::{Binder, Binders};

/// Result<T, VirErr> is used when an error might need to be reported to the user
pub type VirErr = Arc<Spanned<VirErrX>>;
#[derive(Clone, Debug)]
pub enum VirErrX {
    /// Currently, the only variant is a String, but we may add more cases later
    Str(String),
}

/// A non-qualified name, such as a local variable name or type parameter name
pub type Ident = Arc<String>;
pub type Idents = Arc<Vec<Ident>>;

/// A fully-qualified name, such as a module name, function name, or datatype name
pub type Path = Arc<PathX>;
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PathX {
    pub krate: Option<Ident>, // None for local crate
    pub segments: Idents,
}

/// Describes what access other modules have to a function, datatype, etc.
#[derive(Clone, Debug)]
pub struct Visibility {
    /// Module that owns this item, or None for a foreign module
    pub owning_module: Option<Path>,
    /// true for private, false for pub, pub(crate)
    pub is_private: bool,
}

/// Describes whether a variable, function, etc. is compiled or just used for verification
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Ghost (not compiled), used to represent specifications (requires, ensures, invariant)
    Spec,
    /// Ghost (not compiled), used to represent proofs of that specifications are satisfied
    Proof,
    /// Non-ghost (compiled code)
    Exec,
}

/// Describes integer types
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

/// Rust type, but without Box, Rc, Arc, etc.
pub type Typ = Arc<TypX>;
pub type Typs = Arc<Vec<Typ>>;
// Deliberately not marked Eq -- use explicit match instead, so we know where types are compared
#[derive(Debug)]
pub enum TypX {
    /// Bool, Int, Datatype are translated directly into corresponding SMT types (they are not SMT-boxed)
    Bool,
    Int(IntRange),
    /// Tuple type (t1, ..., tn).  Note: ast_simplify replaces Tuple with Datatype.
    Tuple(Typs),
    /// Spec closure type (t1, ..., tn) -> t0.
    Lambda(Typs, Typ),
    /// Datatype (concrete or abstract) applied to type arguments
    Datatype(Path, Typs),
    /// Boxed for SMT encoding (unrelated to Rust Box type), can be unboxed:
    Boxed(Typ),
    /// Type parameter (inherently SMT-boxed, and cannot be unboxed)
    TypParam(Ident),
    /// Type of type identifiers
    TypeId,
}

/// Primitive unary operations
/// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
#[derive(Copy, Clone, Debug)]
pub enum UnaryOp {
    /// boolean not
    Not,
    /// Mark an expression as a member of an SMT quantifier trigger group.
    /// Each trigger group becomes one SMT trigger containing all the expressions in the trigger group.
    /// Each group is named by either Some integer, or the unnamed group None.
    /// (None is just another name; it is no different from an integer-named group.)
    /// Example: #[trigger] expr is translated into Trigger(None) applied to expr
    /// Example: #[trigger(1, 2, 3)] expr is translated into three Trigger ops wrapped around expr
    ///   (Trigger(Some(1)), Trigger(Some(2)), Trigger(Some(3)))
    Trigger(Option<u64>),
    /// Force integer value into range given by IntRange (e.g. by using mod)
    Clip(IntRange),
}

/// More complex unary operations (requires Clone rather than Copy)
/// (Below, "boxed" refers to boxing types in the SMT encoding, not the Rust Box type)
#[derive(Clone, Debug)]
pub enum UnaryOpr {
    /// coerce Typ --> Boxed(Typ)
    Box(Typ),
    /// coerce Boxed(Typ) --> Typ
    Unbox(Typ),
    /// Test whether expression is a particular variant of a datatype
    IsVariant { datatype: Path, variant: Ident },
    /// Read .0, .1, etc. from tuple (Note: ast_simplify replaces this with Field)
    TupleField { tuple_arity: usize, field: usize },
    /// Read field from variant of datatype
    Field { datatype: Path, variant: Ident, field: Ident },
}

/// Primitive binary operations
/// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
/// Note that all integer operations are on mathematic integers (IntRange::Int),
/// not on finite-width integer types or nat.
/// Finite-width and nat operations are represented with a combination of IntRange::Int operations
/// and UnaryOp::Clip.
#[derive(Copy, Clone, Debug)]
pub enum BinaryOp {
    /// boolean and (short-circuiting: right side is evaluated only if left side is true)
    And,
    /// boolean or (short-circuiting: right side is evaluated only if left side is false)
    Or,
    /// boolean implies (short-circuiting: right side is evaluated only if left side is true)
    Implies,
    /// SMT equality for any type -- two expressions are exactly the same value
    /// Some types support compilable equality (Mode == Exec); others only support spec equality (Mode == Spec)
    Eq(Mode),
    /// not Eq
    Ne,
    /// IntRange::Int <=
    Le,
    /// IntRange::Int >=
    Ge,
    /// IntRange::Int <
    Lt,
    /// IntRange::Int >
    Gt,
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
    // bit vector Ops
    BitXor,
    BitAnd,
    BitOr,
    Shr,
    Shl,
}

/// Ghost annotations on functions and while loops; must appear at the beginning of function body
/// or while loop body
pub type HeaderExpr = Arc<HeaderExprX>;
#[derive(Debug)]
pub enum HeaderExprX {
    /// Preconditions on functions
    Requires(Exprs),
    /// Postconditions on functions, with an optional name and type for the return value
    Ensures(Option<(Ident, Typ)>, Exprs),
    /// Invariants on while loops
    Invariant(Exprs),
    /// Decreases clauses for functions (possibly also for while loops, but this isn't implemented yet)
    Decreases(Expr),
    /// Make a function f opaque (definition hidden) within the current function body.
    /// (The current function body can later reveal f in specific parts of the current function body if desired.)
    Hide(Fun),
}

/// Primitive constant values
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constant {
    /// true or false
    Bool(bool),
    /// non-negative integer of arbitrary size (IntRange::Nat); use subtraction to get negative numbers
    Nat(Arc<String>),
}

#[derive(Debug)]
pub struct SpannedTyped<X> {
    pub span: Span,
    pub typ: Typ,
    pub x: X,
}

/// Patterns for match expressions
pub type Pattern = Arc<SpannedTyped<PatternX>>;
pub type Patterns = Arc<Vec<Pattern>>;
#[derive(Debug)]
pub enum PatternX {
    /// _
    Wildcard,
    /// x or mut x
    Var { name: Ident, mutable: bool },
    /// Note: ast_simplify replaces this with Constructor
    Tuple(Patterns),
    /// Match constructor of datatype Path, variant Ident
    /// For tuple-style variants, the patterns appear in order and are named "0", "1", etc.
    /// For struct-style variants, the patterns may appear in any order.
    Constructor(Path, Ident, Binders<Pattern>),
}

/// Arms of match expressions
pub type Arm = Arc<Spanned<ArmX>>;
pub type Arms = Arc<Vec<Arm>>;
#[derive(Debug)]
pub struct ArmX {
    /// pattern
    pub pattern: Pattern,
    /// "if" condition on a case
    pub guard: Expr,
    /// expression or statement the executes when case matches
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum CallTarget {
    /// Call a statically known function, passing some type arguments
    Static(Fun, Typs),
    /// Call a dynamically computed FnSpec (no type arguments allowed),
    /// where the function type is specified by the GenericBound of typ_param.
    FnSpec(Expr),
}

/// Expression, similar to rustc_hir::Expr
pub type Expr = Arc<SpannedTyped<ExprX>>;
pub type Exprs = Arc<Vec<Expr>>;
#[derive(Debug)]
pub enum ExprX {
    /// Constant
    Const(Constant),
    /// Local variable
    Var(Ident),
    /// Call to a function passing some expression arguments
    Call(CallTarget, Exprs),
    /// Note: ast_simplify replaces this with Ctor
    Tuple(Exprs),
    /// Construct datatype value of type Path and variant Ident,
    /// with field initializers Binders<Expr> and an optional ".." update expression.
    /// For tuple-style variants, the field initializers appear in order and are named "0", "1", etc.
    /// For struct-style variants, the field initializers may appear in any order.
    Ctor(Path, Ident, Binders<Expr>, Option<Expr>),
    /// Primitive unary operation
    Unary(UnaryOp, Expr),
    /// Special unary operator
    UnaryOpr(UnaryOpr, Expr),
    /// Primitive binary operation
    Binary(BinaryOp, Expr, Expr),
    /// Quantifier (forall/exists), binding the variables in Binders, with body Expr
    Quant(Quant, Binders<Typ>, Expr),
    /// Specification closure
    Closure(Binders<Typ>, Expr),
    /// Choose a specification value satisfying a predicate
    Choose(Binder<Typ>, Expr),
    /// Assign to local variable
    Assign(Expr, Expr),
    /// Reveal definition of an opaque function with some integer fuel amount
    Fuel(Fun, u32),
    /// Header, which must appear at the beginning of a function or while loop.
    /// Note: this only appears temporarily during rust_to_vir construction, and should not
    /// appear in the final Expr produced by rust_to_vir (see vir::headers::read_header).
    Header(HeaderExpr),
    /// Assume false
    Admit,
    /// Forall or assert-by statement; proves "forall vars. ensure" via proof.
    Forall { vars: Binders<Typ>, require: Expr, ensure: Expr, proof: Expr },
    /// If-else
    If(Expr, Expr, Option<Expr>),
    /// Match (Note: ast_simplify replaces Match with other expressions)
    Match(Expr, Arms),
    /// While loop, with invariants
    While { cond: Expr, body: Expr, invs: Exprs },
    /// Return from function
    Return(Option<Expr>),
    /// Sequence of statements, optionally including an expression at the end
    Block(Stmts, Option<Expr>),
}

/// Statement, similar to rustc_hir::Stmt
pub type Stmt = Arc<Spanned<StmtX>>;
pub type Stmts = Arc<Vec<Stmt>>;
#[derive(Debug)]
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
#[derive(Debug)]
pub struct ParamX {
    pub name: Ident,
    pub typ: Typ,
    pub mode: Mode,
}

pub type GenericBound = Arc<GenericBoundX>;
#[derive(Debug)]
pub enum GenericBoundX {
    None,
    /// Spec function type (t1, ..., tn) -> t0.
    /// Note: ast_simplify removes FnSpec type parameters, using a Datatype to represent FnSpec.
    FnSpec(Typs, Typ),
}

pub type TypBounds = Arc<Vec<(Ident, GenericBound)>>;

pub type FunctionAttrs = Arc<FunctionAttrsX>;
#[derive(Debug, Default, Clone)]
pub struct FunctionAttrsX {
    /// List of functions that this function wants to view as opaque
    pub hidden: Arc<Vec<Fun>>,
    /// Create a global axiom saying forall params, require ==> ensure
    pub export_as_global_forall: bool,
    /// In triggers_auto, don't use this function as a trigger
    pub no_auto_trigger: bool,
    /// Custom error message to display when a pre-condition fails
    pub custom_req_err: Option<String>,
}

/// Static function identifier
pub type Fun = Arc<FunX>;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunX {
    /// Path of function
    pub path: Path,
    /// Path of the trait that defines the function, if any.
    /// This disambiguates between impls for the same type of multiple traits that define functions
    /// with the same name.
    pub trait_path: Option<Path>,
}

/// Function, including signature and body
pub type Function = Arc<Spanned<FunctionX>>;
#[derive(Debug, Clone)]
pub struct FunctionX {
    /// Name of function
    pub name: Fun,
    /// Access control (public/private)
    pub visibility: Visibility,
    /// exec functions are compiled, proof/spec are erased
    /// exec/proof functions can have requires/ensures, spec cannot
    /// spec functions can be used in requires/ensures, proof/exec cannot
    pub mode: Mode,
    /// Default amount of fuel: 0 means opaque, >= 1 means visible
    /// For recursive functions, fuel determines the number of unfoldings that the SMT solver sees
    pub fuel: u32,
    /// Type parameters to generic functions
    pub typ_bounds: TypBounds,
    /// Function parameters
    pub params: Params,
    /// Return value (unit return type is treated specially; see FunctionX::has_return in ast_util)
    pub ret: Param,
    /// Preconditions
    pub require: Exprs,
    /// Postconditions
    pub ensure: Exprs,
    /// Decreases clause to ensure recursive function termination
    pub decrease: Option<Expr>,
    /// For public spec functions, is_abstract == true means that the body is private
    /// even though the function is public
    pub is_abstract: bool,
    /// Various attributes
    pub attrs: FunctionAttrs,
    /// Body of the function (may be None for foreign functions or for no_verify functions)
    pub body: Option<Expr>,
}

/// Single field in a variant
pub type Field = Binder<(Typ, Mode)>;
/// List of fields in a variant
/// For tuple-style variants, the fields appear in order and are named "0", "1", etc.
/// For struct-style variants, the fields may appear in any order
pub type Fields = Binders<(Typ, Mode)>;
pub type Variant = Binder<Fields>;
pub type Variants = Binders<Fields>;

#[derive(Clone, Debug)]
pub enum DatatypeTransparency {
    Never,
    WithinModule,
    Always,
}

/// struct or enum
#[derive(Clone, Debug)]
pub struct DatatypeX {
    pub path: Path,
    pub visibility: Visibility,
    pub transparency: DatatypeTransparency,
    // Note: currently typ_params doesn't contain GenericBound, which means that datatype fields
    // cannot have FnSpec function types.  If we ever allow datatype fields with function types,
    // we will need to check that recursive types only appear in positive positions for soundness.
    pub typ_params: Idents,
    pub variants: Variants,
    pub mode: Mode,
}
pub type Datatype = Arc<Spanned<DatatypeX>>;
pub type Datatypes = Vec<Datatype>;

/// An entire crate
pub type Krate = Arc<KrateX>;
#[derive(Clone, Debug, Default)]
pub struct KrateX {
    /// All functions in the crate, plus foreign functions
    pub functions: Vec<Function>,
    /// All datatypes in the crate
    pub datatypes: Vec<Datatype>,
    /// List of all modules in the crate
    pub module_ids: Vec<Path>,
}
