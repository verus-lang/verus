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
pub type Path = Arc<Vec<Ident>>;

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
    /// Unit, Bool, Int, Path are translated directly into corresponding SMT types (they are not SMT-boxed)
    Unit,
    Bool,
    Int(IntRange),
    Path(Path),
    /// Boxed for SMT encoding (unrelated to Rust Box type), can be unboxed:
    Boxed(Typ),
    /// Type parameter (inherently SMT-boxed, and cannot be unboxed)
    TypParam(Ident),
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
}

/// Primitive binary operations
/// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
/// Note that all integer operations are on mathematic integers (IntRange::Int),
/// not on finite-width integer types or nat.
/// Finite-width and nat operations are represented with a combination of IntRange::Int operations
/// and UnaryOp::Clip.
#[derive(Copy, Clone, Debug)]
pub enum BinaryOp {
    /// boolean and
    And,
    /// boolean or
    Or,
    /// boolean implies
    Implies,
    /// SMT equality for any type -- two expressions are exactly the same value
    Eq,
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
    Decreases(Expr, Typ),
    /// Make a function f opaque (definition hidden) within the current function body.
    /// (The current function body can later reveal f in specific parts of the current function body if desired.)
    Hide(Path),
}

/// Primitive constant values
#[derive(Clone, Debug)]
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

/// Expression, similar to rustc_hir::Expr
pub type Expr = Arc<SpannedTyped<ExprX>>;
pub type Exprs = Arc<Vec<Expr>>;
#[derive(Debug)]
pub enum ExprX {
    /// Constant
    Const(Constant),
    /// Local variable
    Var(Ident),
    /// Call to function with given name, passing some type arguments and some expression arguments
    /// TODO: should be Path, not Ident
    /// Note: higher-order functions aren't yet supported
    Call(Path, Typs, Exprs),
    /// Construct datatype value of type Path and variant Ident, with field initializers Binders<Expr>
    Ctor(Path, Ident, Binders<Expr>),
    /// Read field from datatype
    Field { lhs: Expr, datatype: Path, field_name: Ident },
    /// Primitive unary operation
    Unary(UnaryOp, Expr),
    /// Special unary operator
    UnaryOpr(UnaryOpr, Expr),
    /// Primitive binary operation
    Binary(BinaryOp, Expr, Expr),
    /// Quantifier (forall/exists), binding the variables in Binders, with body Expr
    Quant(Quant, Binders<Typ>, Expr),
    /// Assign to local variable
    Assign(Expr, Expr),
    /// Reveal definition of an opaque function with some integer fuel amount
    Fuel(Path, u32),
    /// Header, which must appear at the beginning of a function or while loop.
    /// Note: this only appears temporarily during rust_to_vir construction, and should not
    /// appear in the final Expr produced by rust_to_vir (see vir::headers::read_header).
    Header(HeaderExpr),
    /// Assume false
    Admit,
    /// If-else
    If(Expr, Expr, Option<Expr>),
    /// While loop, with invariants
    While { cond: Expr, body: Expr, invs: Exprs },
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
    Decl { param: Param, mutable: bool, init: Option<Expr> },
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

/// Function, including signature and body
pub type Function = Arc<Spanned<FunctionX>>;
#[derive(Debug, Clone)]
pub struct FunctionX {
    pub path: Path,
    pub visibility: Visibility,
    /// exec functions are compiled, proof/spec are erased
    /// exec/proof functions can have requires/ensures, spec cannot
    /// spec functions can be used in requires/ensures, proof/exec cannot
    pub mode: Mode,
    /// Default amount of fuel: 0 means opaque, >= 1 means visible
    /// For recursive functions, fuel determines the number of unfoldings that the SMT solver sees
    pub fuel: u32,
    /// Type parameters to generic functions
    pub typ_params: Idents,
    /// Function parameters
    pub params: Params,
    /// Optional return value
    /// TODO: rather than an Option, it might be cleaner to use the unit type
    pub ret: Option<(Ident, Typ, Mode)>,
    /// Preconditions
    pub require: Exprs,
    /// Postconditions
    pub ensure: Exprs,
    /// Decreases clause to ensure recursive function termination
    pub decrease: Option<(Expr, Typ)>,
    /// Custom error message to display when a pre-condition fails
    pub custom_req_err: Option<String>,
    /// List of functions that this function wants to view as opaque
    pub hidden: Arc<Vec<Path>>,
    /// For public spec functions, is_abstract == true means that the body is private
    /// even though the function is public
    pub is_abstract: bool,
    /// Body of the function (may be None for foreign functions or for no_verify functions)
    pub body: Option<Expr>,
}

pub type Field = Binder<(Typ, Mode)>;
pub type Fields = Binders<(Typ, Mode)>;
pub type Variant = Binder<Fields>;
pub type Variants = Binders<Fields>;

#[derive(Debug)]
pub enum DatatypeTransparency {
    Never,
    WithinModule,
    Always,
}

/// struct or enum
#[derive(Debug)]
pub struct DatatypeX {
    pub path: Path,
    pub visibility: Visibility,
    pub transparency: DatatypeTransparency,
    pub variants: Variants,
}
pub type Datatype = Arc<Spanned<DatatypeX>>;
pub type Datatypes = Vec<Datatype>;

/// An entire crate
pub type Krate = Arc<KrateX>;
#[derive(Debug, Default)]
pub struct KrateX {
    /// All functions in the crate, plus foreign functions
    pub functions: Vec<Function>,
    /// All datatypes in the crate
    pub datatypes: Vec<Datatype>,
    /// List of all modules in the crate
    pub module_ids: Vec<Path>,
}
