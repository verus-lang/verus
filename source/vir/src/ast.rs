//! The VIR-AST Abstract Syntax Tree
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! VIR-AST follows the structure of Rust-HIR, but omits features that are not needed
//! for verification.

use crate::def::Spanned;
use air::ast::Span;
use air::errors::Error;
use std::sync::Arc;

pub use air::ast::{Binder, Binders};

/// Result<T, VirErr> is used when an error might need to be reported to the user
pub type VirErr = Error;

/// A non-qualified name, such as a local variable name or type parameter name
pub type Ident = Arc<String>;
pub type Idents = Arc<Vec<Ident>>;

/// A fully-qualified name, such as a module name, function name, or datatype name
pub type Path = Arc<PathX>;
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

/// Mode that gets filled in by the mode checker.
/// (A unique id marks the place that needs to be filled in.)
pub type InferMode = u64;

/// Describes integer types
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    /// AIR type, used internally during translation
    Air(air::ast::Typ),
}

#[derive(Copy, Clone, Debug)]
pub enum TriggerAnnotation {
    /// Automatically choose triggers for the expression containing this annotation,
    /// with no diagnostics printed
    AutoTrigger,
    /// Each trigger group is named by either Some integer, or the unnamed group None.
    /// (None is just another name; it is no different from an integer-named group.)
    /// Example: #[trigger] expr is translated into Trigger(None) applied to expr
    /// Example: #[trigger(1, 2, 3)] expr is translated into three Trigger ops wrapped around expr
    ///   (Trigger(Some(1)), Trigger(Some(2)), Trigger(Some(3)))
    Trigger(Option<u64>),
}

/// Operations on Ghost and Tracked
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ModeCoercion {
    /// Mutable borrows (Ghost::borrow_mut and Tracked::borrow_mut) are treated specially by
    /// the mode checker when checking assignments.
    BorrowMut,
    /// All other cases are treated uniformly by the mode checker based on their op/from/to-mode.
    /// (This includes Ghost::borrow, Tracked::get, etc.)
    Other,
}

/// Primitive unary operations
/// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
#[derive(Copy, Clone, Debug)]
pub enum UnaryOp {
    /// boolean not
    Not,
    /// bitwise not
    BitNot,
    /// Mark an expression as a member of an SMT quantifier trigger group.
    /// Each trigger group becomes one SMT trigger containing all the expressions in the trigger group.
    Trigger(TriggerAnnotation),
    /// Force integer value into range given by IntRange (e.g. by using mod)
    Clip(IntRange),
    /// Operations that coerce from/to builtin::Ghost or builtin::Tracked
    CoerceMode { op_mode: Mode, from_mode: Mode, to_mode: Mode, kind: ModeCoercion },
    /// Internal consistency check to make sure finalize_exp gets called
    /// (appears only briefly in SST before finalize_exp is called)
    MustBeFinalized,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldOpr {
    pub datatype: Path,
    pub variant: Ident,
    pub field: Ident,
}

/// More complex unary operations (requires Clone rather than Copy)
/// (Below, "boxed" refers to boxing types in the SMT encoding, not the Rust Box type)
#[derive(Clone, Debug)]
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
}

/// Arithmetic operation that might fail (overflow or divide by zero)
#[derive(Copy, Clone, Debug)]
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
#[derive(Copy, Clone, Debug)]
pub enum BitwiseOp {
    BitXor,
    BitAnd,
    BitOr,
    Shr,
    Shl,
}

#[derive(Copy, Clone, Debug)]
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
    /// boolean xor (no short-circuiting)
    Xor,
    /// boolean implies (short-circuiting: right side is evaluated only if left side is true)
    Implies,
    /// SMT equality for any type -- two expressions are exactly the same value
    /// Some types support compilable equality (Mode == Exec); others only support spec equality (Mode == Spec)
    Eq(Mode),
    /// not Eq
    Ne,
    ///
    Inequality(InequalityOp),
    /// IntRange operations that may require overflow or divide-by-zero checks
    /// (None for InferMode means always mode Spec)
    Arith(ArithOp, Option<InferMode>),
    /// Bit Vector Operators
    Bitwise(BitwiseOp),
}

#[derive(Clone, Debug)]
pub enum MultiOp {
    Chained(Arc<Vec<InequalityOp>>),
}

/// Ghost annotations on functions and while loops; must appear at the beginning of function body
/// or while loop body
pub type HeaderExpr = Arc<HeaderExprX>;
#[derive(Debug)]
pub enum HeaderExprX {
    /// Marker that trait declaration method body is omitted and should be erased
    NoMethodBody,
    /// Preconditions on exec/proof functions
    Requires(Exprs),
    /// Postconditions on exec/proof functions, with an optional name and type for the return value
    Ensures(Option<(Ident, Typ)>, Exprs),
    /// Recommended preconditions on spec functions, used to help diagnose mistakes in specifications.
    /// Checking of recommends is disabled by default.
    Recommends(Exprs),
    /// Invariants on while loops
    Invariant(Exprs),
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
#[derive(Debug, Clone)]
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

#[derive(Clone, Debug)]
pub enum CallTarget {
    /// Call a statically known function, passing some type arguments
    Static(Fun, Typs),
    /// Call a dynamically computed FnSpec (no type arguments allowed),
    /// where the function type is specified by the GenericBound of typ_param.
    FnSpec(Expr),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VarAt {
    Pre,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InvAtomicity {
    Atomic,
    NonAtomic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AssertQueryMode {
    NonLinear,
}

#[derive(Clone, Copy, Debug)]
pub struct Quant {
    pub quant: air::ast::Quant,
    pub boxed_params: bool,
}

/// Expression, similar to rustc_hir::Expr
pub type Expr = Arc<SpannedTyped<ExprX>>;
pub type Exprs = Arc<Vec<Expr>>;
#[derive(Debug)]
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
    ConstVar(Fun),
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
    /// Primitive unary operation
    Unary(UnaryOp, Expr),
    /// Special unary operator
    UnaryOpr(UnaryOpr, Expr),
    /// Primitive binary operation
    Binary(BinaryOp, Expr, Expr),
    /// Primitive multi-operand operation
    Multi(MultiOp, Exprs),
    /// Quantifier (forall/exists), binding the variables in Binders, with body Expr
    Quant(Quant, Binders<Typ>, Expr),
    /// Specification closure
    Closure(Binders<Typ>, Expr),
    /// Choose specification values satisfying a condition, compute body
    Choose { params: Binders<Typ>, cond: Expr, body: Expr },
    /// Manually supply triggers for body of quantifier
    WithTriggers { triggers: Arc<Vec<Exprs>>, body: Expr },
    /// Assign to local variable
    /// init_not_mut = true ==> a delayed initialization of a non-mutable variable
    Assign { init_not_mut: bool, lhs: Expr, rhs: Expr },
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
    /// bit vector assertions
    AssertBV(Expr),
    /// If-else
    If(Expr, Expr, Option<Expr>),
    /// Match (Note: ast_simplify replaces Match with other expressions)
    Match(Expr, Arms),
    /// While loop, with invariants
    While { cond: Expr, body: Expr, invs: Exprs },
    /// Open invariant
    OpenInvariant(Expr, Binder<Typ>, Expr, InvAtomicity),
    /// Return from function
    Return(Option<Expr>),
    /// Enter a Rust ghost block, which will be erased during compilation.
    /// In principle, this is not needed, because we can infer which code to erase using modes.
    /// However, we can't easily communicate the inferred modes back to rustc for erasure
    /// and lifetime checking -- rustc needs syntactic annotations for these, and the mode checker
    /// needs to confirm that these annotations agree with what would have been inferred.
    Ghost { alloc_wrapper: Option<Fun>, tracked: bool, expr: Expr },
    /// Sequence of statements, optionally including an expression at the end
    Block(Stmts, Option<Expr>),
    /// assert_by with smt.arith.nl=true
    AssertQuery { requires: Exprs, ensures: Exprs, proof: Expr, mode: AssertQueryMode },
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
#[derive(Debug, Clone)]
pub struct ParamX {
    pub name: Ident,
    pub typ: Typ,
    pub mode: Mode,
    /// An &mut parameter
    pub is_mut: bool,
}

pub type GenericBound = Arc<GenericBoundX>;
#[derive(Debug)]
pub enum GenericBoundX {
    /// List of implemented traits
    Traits(Vec<Path>),
    /// Spec function type (t1, ..., tn) -> t0.
    /// Note: ast_simplify removes FnSpec type parameters, using a Datatype to represent FnSpec.
    FnSpec(Typs, Typ),
}

pub type TypBounds = Arc<Vec<(Ident, GenericBound)>>;
/// Each type parameter is (name: Ident, bound: GenericBound, strictly_positive: bool)
pub type TypPositiveBounds = Arc<Vec<(Ident, GenericBound, bool)>>;

pub type FunctionAttrs = Arc<FunctionAttrsX>;
#[derive(Debug, Default, Clone)]
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
    /// coerce f(e, ...) to f(e.view(), ...)
    pub autoview: bool,
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
}

/// Function specification of its invariant mask
#[derive(Clone, Debug)]
pub enum MaskSpec {
    InvariantOpens(Exprs),
    InvariantOpensExcept(Exprs),
    NoSpec,
}

#[derive(Debug, Clone)]
pub enum FunctionKind {
    Static,
    /// Method declaration inside a trait
    TraitMethodDecl {
        trait_path: Path,
    },
    /// Method implementation inside an impl, implementing a trait method for a trait for a datatype
    TraitMethodImpl {
        method: Fun,
        trait_path: Path,
        trait_typ_args: Typs,
        datatype: Path,
        datatype_typ_args: Typs,
    },
}

/// Function, including signature and body
pub type Function = Arc<Spanned<FunctionX>>;
#[derive(Debug, Clone)]
pub struct FunctionX {
    /// Name of function
    pub name: Fun,
    /// Kind (translation to AIR is different for each different kind)
    pub kind: FunctionKind,
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
    /// is_const == true means that this function is actually a const declaration;
    /// we treat const declarations as functions with 0 arguments, having mode == Spec.
    /// However, if ret.x.mode != Spec, there are some differences: the const can dually be used as spec,
    /// and the body is restricted to a subset of expressions that are spec-safe.
    pub is_const: bool,
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

/// Single field in a variant
pub type Field = Binder<(Typ, Mode, Visibility)>;
/// List of fields in a variant
/// For tuple-style variants, the fields appear in order and are named "0", "1", etc.
/// For struct-style variants, the fields may appear in any order
pub type Fields = Binders<(Typ, Mode, Visibility)>;
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
    pub typ_params: TypPositiveBounds,
    pub variants: Variants,
    pub mode: Mode,
    // For token types that need to be 'unforgeable'. Only makes sense for 'Proof' types.
    pub unforgeable: bool,
}
pub type Datatype = Arc<Spanned<DatatypeX>>;
pub type Datatypes = Vec<Datatype>;

pub type Trait = Arc<Spanned<TraitX>>;
#[derive(Clone, Debug)]
pub struct TraitX {
    pub name: Path,
    pub typ_params: TypPositiveBounds,
    pub methods: Arc<Vec<Fun>>,
}

/// An entire crate
pub type Krate = Arc<KrateX>;
#[derive(Clone, Debug, Default)]
pub struct KrateX {
    /// All functions in the crate, plus foreign functions
    pub functions: Vec<Function>,
    /// All datatypes in the crate
    pub datatypes: Vec<Datatype>,
    /// All traits in the crate
    pub traits: Vec<Trait>,
    /// List of all modules in the crate
    pub module_ids: Vec<Path>,
}
