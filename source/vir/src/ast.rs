//! The VIR-AST Abstract Syntax Tree
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! VIR-AST follows the structure of Rust-HIR, but omits features that are not needed
//! for verification.

use crate::def::Spanned;
use crate::messages::{Message, MessageAs, Span};
pub use air::ast::{Binder, Binders};
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use vir_macros::{ToDebugSNode, to_node_impl};

/// Result<T, VirErr> is used when an error might need to be reported to the user
pub type VirErr = Message;
pub type VirErrAs = MessageAs;

/// A non-qualified name, such as a local variable name or type parameter name
pub type Ident = Arc<String>;
pub type Idents = Arc<Vec<Ident>>;

/// A fully-qualified name, such as a module name, function name, or datatype name
pub type Path = Arc<PathX>;
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PathX {
    pub krate: Option<Ident>, // None for local crate
    pub segments: Idents,
}

#[derive(
    Copy,
    Clone,
    Debug,
    Serialize,
    Deserialize,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    ToDebugSNode
)]
pub enum VarIdentDisambiguate {
    // AIR names that don't derive from rustc's names:
    AirLocal,
    // rustc's parameter unique id comes from the function body; no body means no id:
    NoBodyParam,
    // TypParams are normally Idents, but sometimes we mix TypParams into lists of VarIdents:
    TypParamBare,
    TypParamSuffixed,
    TypParamDecorated,
    // Fields are normally Idents, but sometimes we mix field names into lists of VarIdents:
    Field,
    RustcId(usize),
    // We track whether the variable is SST/AIR statement-bound or expression-bound,
    // to help drop unnecessary ids from expression-bound variables
    VirRenumbered { is_stmt: bool, does_shadow: bool, id: u64 },
    // Some expression-bound variables don't need an id
    VirExprNoNumber,
    // We rename parameters to VirParam if the parameters don't conflict with each other
    VirParam,
    // Recursive definitions have an extra copy of the parameters
    VirParamRecursion(usize),
    // Capture-avoiding substitution creates new names:
    VirSubst(u64),
    VirTemp(u64),
    ExpandErrorsDecl(u64),
    BitVectorToAirDecl(u64),
    UserDefinedTypeInvariantPass(u64),
    ResInfTemp(u64),
}

/// A local variable name, possibly renamed for disambiguation
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash, ToDebugSNode)]
pub struct VarIdent(pub Ident, pub VarIdentDisambiguate);

pub type VarBinder<A> = Arc<VarBinderX<A>>;
pub type VarBinders<A> = Arc<Vec<VarBinder<A>>>;
#[derive(Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct VarBinderX<A: Clone> {
    pub name: VarIdent,
    pub a: A,
}

/// Static function identifier
pub type Fun = Arc<FunX>;
#[derive(Serialize, Deserialize, ToDebugSNode, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq)]
pub enum BodyVisibility {
    Uninterpreted,
    /// None for pub
    /// Some(path) means visible to path and path's descendents
    Visibility(Visibility),
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
    /// Rust's 'char' type, representing a Unicode Scalar Value:
    /// The range 0 to 0x10FFFF, inclusive, MINUS the range 0xD800 to 0xDFFF.
    /// Or another way: [0, 0xD800) union [0xE000, 0x10FFFF]. See unicode.rs.
    Char,
}

/// Type information relevant to Rust but generally not relevant to the SMT encoding.
/// This information is relevant for resolving traits.
///
/// A `TypDecoration` can be applied to a type (via `TypX::Decorate`) to represent
/// a different type that has the same encoding at the SMT level.
/// For example, `u64` is represented in VIR as `Int(IntRange::U(64))`
/// while `Box<u64>` is represented in VIR as `Decorate(Box, Int(IntRange::U(64)))`.
/// Since the VIR types differ only in the "decoration", we know they are represented
/// by the same SMT sort (air's Int type, in this case).
/// Many functions (e.g., HasType) that depend on a type can be written
/// to only depend on the "base type" (i.e., the type minus the decoration).
///
/// Furthermore, many functions can be elided entirely because they are simply the identity
/// operation, e.g., `Box::new` takes a `T` to a `Box<T>`; but since these types are
/// equivalent up to decoration, they are represented the same in SMT, and it happens the
/// function is the identity function.
///
/// However, decorations are not totally irrelevant. They are still significant for resolving
/// traits (e.g., `u64` and `Box<u64>` might implement the same trait in different ways).
///
/// In some places, the decoration of a Typ cannot be considered meaningful due to these
/// implicit 'identity' coercions:
///   - `expr.typ`
///   - `place.typ`
///   - `pattern.typ`
///   - `exp.typ` (SST nodes)
/// But in other places, types must be exactly correct, *including* decoration:
///   - type arguments for a Call
///   - `pattern_binding.typ` (type of a local variable declaration)
///   - Most places where `Typ` is given as an explicit field of a node
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
    /// For new-mut-ref, don't use this; use TypX::MutRef instead
    MutRef,
    /// Box<T>
    /// This is complicated due to the Allocator type argument; see `TypDecorationArg`.
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
    /// This is applied to `*mut T` to turn it into `*const T`
    /// (This is _not_ applied to `T` on its own.)
    /// This is done because `*mut T` is represented identically `*const T`,
    /// but neither are represented identically to T.
    ConstPtr,
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
    /// StrSlice type. Currently the vstd StrSlice struct is "seen" as this type
    /// despite the fact that it is in fact a datatype
    StrSlice,
    Ptr, // Mut ptr, unless Const decoration is applied
    Global,
}

#[derive(Debug, Serialize, Deserialize, Hash, ToDebugSNode, Clone)]
pub struct TypDecorationArg {
    pub allocator_typ: Typ,
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
    /// Integer type: int, nat, i8, ..., i128, u8, ..., u128, isize, usize, char
    Int(IntRange),
    /// SMT solver's real number (ghost code only)
    Real,
    /// Floating point type (e.g. f32, f64), with specified number of bits (e.g. 32, 64)
    Float(u32),
    /// `spec_fn` type (t1, ..., tn) -> t0.
    SpecFn(Typs, Typ),
    /// Executable function types (with a requires and ensures)
    AnonymousClosure(Typs, Typ, usize),
    /// Corresponds to Rust's FnDef type
    /// Typs are generic type args
    /// If Fun is a trait function, then the Option<Fun> has the statically resolved
    /// function if it exists. Similar to ImplPaths, this is technically redundant
    /// (because it follows from the types), but it is not easy to compute without
    /// storing it here. We need it because it is useful for determining which
    /// FnDef axioms to introduce.
    /// If it resolves to a default function, it can be None.
    FnDef(Fun, Typs, Option<Fun>),
    /// Datatype (concrete or abstract) applied to type arguments
    Datatype(Dt, Typs, ImplPaths),
    /// dyn T<...args...> for some trait T (given by the Path) applied to trait type arguments
    Dyn(Path, Typs, ImplPaths),
    /// When an opaque type is defined (e.g., by a function return), Rustc creates
    /// an unique opaque type constructor for it.
    /// This opaque type is just an instantiation of the opaque type constructor with args
    Opaque {
        // path of the opaque type constructor.
        def_path: Path,
        // args of the instantiation. e.g., let x = foo<args>(); if foo returns an opaque type.
        args: Typs,
    },
    /// Other primitive type (applied to type arguments)
    Primitive(Primitive, Typs),
    /// Wrap type with extra information relevant to Rust but usually irrelevant to SMT encoding
    /// (though needed sometimes to encode trait resolution)
    Decorate(TypDecoration, Option<TypDecorationArg>, Typ),
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
    /// <T as Pointee>::Metadata (see https://doc.rust-lang.org/beta/core/ptr/trait.Pointee.html)
    /// For the msot part, this should be treated identically to a Projection, but the AIR
    /// encoding is special.
    PointeeMetadata(Typ),
    /// Type of type identifiers
    TypeId,
    /// Const integer type argument (e.g. for array sizes)
    ConstInt(BigInt),
    /// Const bool type argument
    ConstBool(bool),
    /// AIR type, used internally during translation
    Air(air::ast::Typ),
    MutRef(Typ),
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
    TraitBound(TraitId, Typs),
    /// predicate representing a type equality bound T<t1, ..., tn, X = typ> for trait T
    TypEqualityBound(Path, Typs, Ident, Typ),
    /// predicate representing const type bound, e.g., `const X: usize`
    ConstTypBound(Typ, Typ),
    /// A failed InferSpecForLoopIter subexpression
    NoInferSpecForLoopIter,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum ArrayKind {
    Array,
    Slice,
}

/// Primitive unary operations
/// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum UnaryOp {
    /// boolean not
    Not,
    /// bitwise not
    /// Semantics:
    ///   Flip every bit in the infinite binary representation of
    ///   (equivalently, compute -x-1)
    ///   Then, if the bitwidth argument is non-None, clip to the given bitwidth
    /// Note that:
    ///  1. A bitwise 'not' on a SIGNED integer can be encoded as BitNot(None)
    ///  2. A bitwise 'not' on an UNSIGNED integer of width w can be encoded as BitNot(Some(w))
    BitNot(Option<IntegerTypeBitwidth>),
    /// Mark an expression as a member of an SMT quantifier trigger group.
    /// Each trigger group becomes one SMT trigger containing all the expressions in the trigger group.
    Trigger(TriggerAnnotation),
    /// Force integer value into range given by IntRange (e.g. by using mod)
    Clip {
        range: IntRange,
        truncate: bool,
    },
    /// Convert integer type to real type (SMT to_real operation)
    IntToReal,
    /// Return raw bits of a float as an int
    FloatToBits,
    /// Operations that coerce from/to verus_builtin::Ghost or verus_builtin::Tracked
    CoerceMode {
        op_mode: Mode,
        from_mode: Mode,
        to_mode: Mode,
        kind: ModeCoercion,
    },
    /// Coerce from concrete type to dyn T
    ToDyn,
    /// Internal consistency check to make sure finalize_exp gets called
    /// (appears only briefly in SST before finalize_exp is called)
    MustBeFinalized,
    /// Internal consistency check to make sure sst_elaborate gets called
    /// (appears only briefly in SST before sst_elaborate is called)
    MustBeElaborated,
    /// We don't give users direct access to the "height" function and Height types.
    /// However, it's useful to be able to trigger on the "height" function
    /// when using HeightCompare.  We manage this by having triggers.rs convert
    /// HeightCompare triggers into HeightTrigger, which is eventually translated
    /// into direct calls to the "height" function in the triggers.
    HeightTrigger,
    /// Used only for handling verus_builtin::strslice_len
    StrLen,
    /// Used only for handling verus_builtin::strslice_is_ascii
    StrIsAscii,
    /// Given an exec/proof expression used to construct a loop iterator,
    /// try to infer a pure specification for the loop iterator.
    /// Evaluate to Some(spec) if successful, None otherwise.
    /// (Note: this is just used as a hint for loop invariants;
    /// regardless of whether it is Some(spec) or None, it should not affect soundness.)
    /// For an exec/proof expression e, the spec s should be chosen so that the value v
    /// that e evaluates to is immutable and v == s, where v may contain local variables.
    /// For example, if v == (n..m), then n and m must be immutable local variables.
    InferSpecForLoopIter {
        print_hint: bool,
    },
    /// May need coercion after casting a type argument
    CastToInteger,
    MutRefCurrent,
    MutRefFuture(MutRefFutureSourceName),
    /// The `final` keyword. `*final(e)` should be replaced with `mut_ref_future(e)`
    /// and `final` on its own is unsupported.
    MutRefFinal,

    /// Length of an array or slice
    Length(ArrayKind),
}

/// Which builtin source name does this come from
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum MutRefFutureSourceName {
    /// This comes from a direct use of the `mut_ref_future` built-in
    MutRefFuture,
    /// Simplified from `*final(e)`
    Final,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord, ToDebugSNode)]
pub enum VariantCheck {
    /// No check necessary
    None,
    /// Check is required because the given field is from a union
    Union,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord, ToDebugSNode)]
pub struct FieldOpr {
    pub datatype: Dt,
    pub variant: Ident,
    pub field: Ident,
    /// Does this come from a get_variant_field / get_union_field verus_builtin?
    /// (This is relevant for mode-checking.)
    pub get_variant: bool,
    pub check: VariantCheck,
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
    IsVariant { datatype: Dt, variant: Ident },
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
    /// Predicate over any type that indicates its mutable references has resolved.
    /// For &mut T this says the prophetic value == the current value.
    /// For primitive types this is trivially true.
    /// For datatypes this is recursive in the natural way.
    HasResolved(Typ),
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum BoundsCheck {
    /// No bounds check necessary. This is the only value allowed in SST.
    Allow,
    /// Perform a bounds check.
    Error,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum OverflowBehavior {
    /// Return an int. This is the only value allowed in SST.
    Allow,
    /// Truncate to the given range
    Truncate(IntRange),
    /// Error if the result is outside the given range
    Error(IntRange),
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum Div0Behavior {
    /// Return the (unspecified) result of divide- or mod-by-0.
    /// This is the only value allowed in SST.
    Allow,
    /// Error if the dividend is 0.
    Error,
}

/// Behavior for the bounds check of the RHS applied to either Shl (<<) or Shr (>>).
/// (This doesn't mean anything for the other BitwiseOp kinds)
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum BitshiftBehavior {
    /// Allow any int value for the RHS. Bitshift for negative ints is undefined.
    Allow,
    /// Error if the right-hand side of the bit-shift is outside the allowed range
    Error,
}

/// Arithmetic operation that might fail (overflow or divide by zero)
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum ArithOp {
    /// IntRange::Int +
    Add(OverflowBehavior),
    /// IntRange::Int -
    Sub(OverflowBehavior),
    /// IntRange::Int *
    Mul(OverflowBehavior),
    /// IntRange::Int / defined as Euclidean (round towards -infinity, not round-towards zero)
    EuclideanDiv(Div0Behavior),
    /// IntRange::Int % defined as Euclidean (returns non-negative result even for negative divisor)
    EuclideanMod(Div0Behavior),
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum RealArithOp {
    /// Real number add (spec mode only)
    Add,
    /// Real number subtract (spec mode only)
    Sub,
    /// Real number multiply (spec mode only)
    Mul,
    /// Real number divide (spec mode only)
    Div,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum IntegerTypeBitwidth {
    /// Exact number of bits (e.g. 8 for u8/i8)
    Width(u32),
    /// usize/isize
    ArchWordSize,
}

/// Bitwise operation
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, ToDebugSNode)]
pub enum BitwiseOp {
    BitXor,
    BitAnd,
    BitOr,
    /// Shift right. The bitwidth argument is only needed to do a bounds-check
    /// (see `BitshiftBehavior`). The actual result, when computed on unbounded integers,
    /// is independent of the bitwidth.
    /// TODO move the IntegerTypeBitwidth field to BitshiftBehavior enum
    Shr(IntegerTypeBitwidth),
    /// Shift left up to w bits, ignoring everything to the left of w.
    /// To interpret the result as an unbounded int,
    /// either zero-extend or sign-extend, depending on the bool argument.
    /// (True = sign-extend, False = zero-extend)
    Shl(IntegerTypeBitwidth, bool),
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
    /// the is_smaller_than verus_builtin, used for decreases (true for <, false for ==)
    HeightCompare { strictly_lt: bool, recursive_function_field: bool },
    /// SMT equality for any type -- two expressions are exactly the same value
    /// Some types support compilable equality (Mode == Exec); others only support spec equality (Mode == Spec)
    Eq(Mode),
    /// not Eq
    Ne,
    /// arithmetic inequality
    Inequality(InequalityOp),
    /// IntRange operations that may require overflow or divide-by-zero checks
    Arith(ArithOp),
    /// Spec-mode real number operations
    RealArith(RealArithOp),
    /// Bit Vector Operators
    Bitwise(BitwiseOp, BitshiftBehavior),
    /// Used only for handling verus_builtin::strslice_get_char
    StrGetChar,
    /// Index into an array or slice, no bounds-checking.
    /// `verus_builtin::array_index` lowers to this.
    /// In SST, this can also be used as a Loc.
    Index(ArrayKind, BoundsCheck),
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
    pub outer_name: VarIdent,
    // rename the parameter to a different name using a "let" binding
    pub inner_name: VarIdent,
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
    /// (regular ensures, default ensures)
    Ensures(Option<(VarIdent, Option<Typ>)>, (Exprs, Exprs)),
    /// Returns clause
    Returns(Expr),
    /// Recommended preconditions on spec functions, used to help diagnose mistakes in specifications.
    /// Checking of recommends is disabled by default.
    Recommends(Exprs),
    /// Invariants (except breaks) on loops
    InvariantExceptBreak(Exprs),
    /// Invariants on loops
    Invariant(Exprs),
    /// Decreases clauses for functions (possibly also for while loops, but this isn't implemented yet)
    Decreases(Exprs),
    /// Recursive function is uninterpreted when Expr is false
    DecreasesWhen(Expr),
    /// Proof function to prove termination for recursive functions
    DecreasesBy(Fun),
    /// The function might open the following invariants
    InvariantOpens(Span, Exprs),
    /// The function might open any BUT the following invariants
    InvariantOpensExcept(Span, Exprs),
    /// The function might open the following invariants, specified as a set
    InvariantOpensSet(Expr),
    /// Make a function f opaque (definition hidden) within the current function body.
    /// (The current function body can later reveal f in specific parts of the current function body if desired.)
    Hide(Fun),
    /// `extra_dependency(f)` means that recursion-checking should act as if the current
    /// function calls `f`
    ExtraDependency(Fun),
    /// This function will not unwind
    NoUnwind,
    /// This function will not unwind if the given condition holds (function of arguments)
    NoUnwindWhen(Expr),
    /// The visibility used in, e.g., `open(crate)`
    OpenVisibilityQualifier(Visibility),
}

/// Primitive constant values
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq, Hash)]
pub enum Constant {
    /// true or false
    Bool(bool),
    /// integer of arbitrary size
    Int(BigInt),
    /// String is >= 1 decimal digits, then one decimal point, then >= 1 decimal digits
    Real(String),
    /// Hold generated string slices in here
    StrSlice(Arc<String>),
    // Hold unicode values here
    Char(char),
    /// Rust representation of f32 constant as u32 bits
    Float32(u32),
    /// Rust representation of f64 constant as u64 bits
    Float64(u64),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SpannedTyped<X> {
    pub span: Span,
    pub typ: Typ,
    pub x: X,
}

#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, Copy, PartialEq, Eq)]
pub enum ByRef {
    No,
    ImmutRef,
    MutRef,
}

#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub struct PatternBinding {
    pub name: VarIdent,
    pub by_ref: ByRef,
    pub typ: Typ,
    pub mutable: bool,
    /// True if the type of this variable is copy.
    /// This is used by resolution analysis; it is meaningless post-simplification.
    pub copy: bool,
}

/// Patterns for match expressions
pub type Pattern = Arc<SpannedTyped<PatternX>>;
pub type Patterns = Arc<Vec<Pattern>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub enum PatternX {
    /// _
    /// True if this is implicitly added from a ..
    Wildcard(bool),
    /// Be careful: when binding a variable, the *type of the variable* is found in the
    /// PatternBinding struct. This can be different than the &pattern.typ which is the
    /// *type of the value being matched against*.
    ///
    /// The specific relation depends on the ByRef:
    ///
    /// | ByRef    | pattern.typ | binding.typ |
    /// |----------|-------------|-------------|
    /// | No       | T           | T           |
    /// | ImmutRef | T           | &T          |
    /// | MutRef   | T           | &mut T      |
    Var(PatternBinding),
    /// `x @ subpat`
    Binding {
        binding: PatternBinding,
        sub_pat: Pattern,
    },
    /// Match constructor of datatype Path, variant Ident
    /// For tuple-style variants, the fields are named "0", "1", etc.
    /// (See [`crate::def::positional_field_ident`])
    /// Fields can appear **in any order** even for tuple variants.
    Constructor(Dt, Ident, Binders<Pattern>),
    Or(Pattern, Pattern),
    /// Matches something equal to the value of this expr
    /// This only supports literals and consts, so we don't need to worry
    /// about side-effects, binding order, etc.
    Expr(Expr),
    /// `e1 <= x <= e2` or `e1 <= x < e2`
    /// The start of the range is always inclusive (<=)
    /// The end of the range may be inclusive (<=) or exclusive (<),
    /// as given by the InequalityOp argument.
    Range(Option<Expr>, Option<(Expr, InequalityOp)>),
    /// References, which are often automatically inserted due to "match ergonomics".
    /// A typical case is like, you have `y: &mut Option<T>` and bind it against the pattern
    /// `Some(x)`. In this case it gets elaborated to the VIR pattern:
    /// `MutRef(Constructor("Some", Var("x")))`.
    /// The variable "x" will have binding mode ByRef::Mut,
    /// and ultimately x will have type `&mut T`.
    MutRef(Pattern),
    ImmutRef(Pattern),
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
    /// holds at beginning of loop
    InvariantExceptBreak,
    /// holds at beginning of loop and after loop exit (including breaks)
    InvariantAndEnsures,
    /// holds at loop exit (including breaks)
    Ensures,
}

pub type LoopInvariants = Arc<Vec<LoopInvariant>>;
#[derive(Debug, Serialize, Deserialize, Clone, ToDebugSNode)]
pub struct LoopInvariant {
    pub kind: LoopInvariantKind,
    pub inv: Expr,
}

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum BuiltinSpecFun {
    // Note that this now applies to any supported function type, e.g., FnDef types,
    // not just "closure" types. TODO rename?
    ClosureReq,
    ClosureEns,
    /// default_ensures clauses, for use by call_ensures on impls that inherit the default
    DefaultEns,
}

#[derive(Clone, Debug, Serialize, Deserialize, Hash, ToDebugSNode, PartialEq, Eq)]
pub enum ImplPath {
    /// the usual `impl X for Trait`. The 'Path' is to the 'impl' block
    TraitImplPath(Path),
    /// Declaration of a function `f` which conceptually implements a trait bound
    /// `FnDef(f) : FnOnce`
    FnDefImplPath(Fun),
}

/// Path of each impl that is used to satisfy a trait bound when instantiating the type parameter
/// This is used to name the "dictionary" that is (conceptually) passed along with the
/// type argument (see recursive_types.rs)
// REVIEW: should trait_typ_args also have ImplPaths?
pub type ImplPaths = Arc<Vec<ImplPath>>;

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum CallTargetKind {
    /// Statically known function
    Static,
    /// Call to a proof function with argument modes and return mode
    ProofFn(Arc<Vec<Mode>>, Mode),
    /// Dynamically dispatched function
    Dynamic,
    /// Dynamically dispatched function with known resolved target
    DynamicResolved { resolved: Fun, typs: Typs, impl_paths: ImplPaths, is_trait_default: bool },
    /// Same as DynamicResolved with is_trait_default = true, but resolves to external default fun
    ExternalTraitDefault,
}

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum CallTarget {
    /// Regular function, passing some type arguments
    Fun(CallTargetKind, Fun, Typs, ImplPaths, AutospecUsage),
    /// Call a dynamically computed FnSpec (no type arguments allowed),
    /// where the function type is specified by the GenericBound of typ_param.
    FnSpec(Expr),
    BuiltinSpecFun(BuiltinSpecFun, Typs, ImplPaths),
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

/// Represents the expression after the '..' in a "ctor update"
/// like the `foo` in `{ a: e1, b: e2, .. foo }`.
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct CtorUpdateTail {
    pub place: Place,
    /// This list needs to contain all the fields that are NOT explicitly listed.
    /// i.e., this is all the fields that are moved or copied out of the input struct.
    /// This information is needed by resolution analysis.
    pub taken_fields: Arc<Vec<(Ident, UnfinalizedReadKind)>>,
}

/// Expression, similar to rustc_hir::Expr
pub type Expr = Arc<SpannedTyped<ExprX>>;
pub type Exprs = Arc<Vec<Expr>>;
#[derive(Clone, Debug, Serialize, Deserialize)]
#[to_node_impl(name = ">")]
pub enum ExprX {
    /// Constant
    Const(Constant),
    /// Local variable as a right-hand side
    Var(VarIdent),
    /// Local variable as a left-hand side
    VarLoc(VarIdent),
    /// Local variable, at a different stage (e.g. a mutable reference in the post-state)
    VarAt(VarIdent, VarAt),
    /// Use of a const variable.  Note: ast_simplify replaces this with Call.
    ConstVar(Fun, AutospecUsage),
    /// Use of a static variable.
    StaticVar(Fun),
    /// Location ("l-value") used for mutable references and assignments.
    /// Not used when new-mut-refs is enabled.
    Loc(Expr),
    /// Call to a function passing some expression arguments
    /// The optional expression is to be executed *after* the arguments but *before* the call.
    /// This is used for two-phase borrows.
    Call(CallTarget, Exprs, Option<Expr>),
    /// Construct datatype value of type Path and variant Ident,
    /// with field initializers Binders<Expr> and an optional ".." update expression.
    /// For tuple-style variants, the fields are named "0", "1", etc.
    /// (See [`crate::def::positional_field_ident`])
    /// Fields can appear **in any order** even for tuple variants.
    Ctor(Dt, Ident, Binders<Expr>, Option<CtorUpdateTail>),
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
    Quant(Quant, VarBinders<Typ>, Expr),
    /// Specification closure
    Closure(VarBinders<Typ>, Expr),
    /// Executable closure
    NonSpecClosure {
        params: VarBinders<Typ>,
        /// If this is a proof_fn, record the args/ret modes; otherwise, None
        proof_fn_modes: Option<(Arc<Vec<Mode>>, Mode)>,
        body: Expr,
        requires: Exprs,
        ensures: Exprs,
        ret: VarBinder<Typ>,
        /// The 'external spec' is an Option because it gets filled in during
        /// ast_simplify. It contains the assumptions that surrounding context
        /// can assume about a closure object after it is created.
        external_spec: Option<(VarIdent, Expr)>,
    },
    /// Array literal (can also be used for sequence literals in the future)
    ArrayLiteral(Exprs),
    /// Executable function (declared with 'fn' and referred to by name)
    ExecFnByName(Fun),
    /// Choose specification values satisfying a condition, compute body
    Choose { params: VarBinders<Typ>, cond: Expr, body: Expr },
    /// Manually supply triggers for body of quantifier
    WithTriggers { triggers: Arc<Vec<Exprs>>, body: Expr },
    /// Assign to local variable
    /// init_not_mut = true ==> a delayed initialization of a non-mutable variable
    /// the lhs is assumed to be a memory location, thus it's not wrapped in Loc
    ///
    /// Not used when new-mut-refs is enabled.
    Assign { init_not_mut: bool, lhs: Expr, rhs: Expr, op: Option<BinaryOp> },
    /// Assign to the given place.
    ///
    /// If `resolve` is set, then we also emit
    /// `assume(has_resolved(place))` immediately before the mutation.
    /// This flag may be set by resolution analysis.
    ///
    /// Used only when new-mut-refs is enabled.
    AssignToPlace { place: Place, rhs: Expr, op: Option<BinaryOp>, resolve: Option<Typ> },
    /// Reveal definition of an opaque function with some integer fuel amount
    Fuel(Fun, u32, bool),
    /// Reveal a string
    RevealString(Arc<String>),
    /// Header, which must appear at the beginning of a function or while loop.
    /// Note: this only appears temporarily during rust_to_vir construction, and should not
    /// appear in the final Expr produced by rust_to_vir (see vir::headers::read_header).
    Header(HeaderExpr),
    /// Assert or assume
    AssertAssume { is_assume: bool, expr: Expr, msg: Option<Message> },
    /// Assert or assume user-defined type invariant for `expr` and return `expr`
    /// These are added in user_defined_type_invariants.rs
    AssertAssumeUserDefinedTypeInvariant { is_assume: bool, expr: Expr, fun: Fun },
    /// Assert-forall or assert-by statement
    AssertBy { vars: VarBinders<Typ>, require: Expr, ensure: Expr, proof: Expr },
    /// `assert_by` with a dedicated prover option (nonlinear_arith, bit_vector)
    AssertQuery { requires: Exprs, ensures: Exprs, proof: Expr, mode: AssertQueryMode },
    /// Assertion discharged via computation
    AssertCompute(Expr, ComputeMode),
    /// If-else
    If(Expr, Expr, Option<Expr>),
    /// Match (Note: ast_simplify replaces Match with other expressions)
    Match(Place, Arms),
    /// Loop (either "while", cond = Some(...), or "loop", cond = None), with invariants
    Loop {
        loop_isolation: bool,
        is_for_loop: bool,
        label: Option<String>,
        cond: Option<Expr>,
        body: Expr,
        invs: LoopInvariants,
        decrease: Exprs,
    },
    /// Open invariant
    OpenInvariant(Expr, VarBinder<Typ>, Expr, InvAtomicity),
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
    /// Enter a proof block from inside spec-mode code
    ProofInSpec(Expr),
    /// Sequence of statements, optionally including an expression at the end
    Block(Stmts, Option<Expr>),
    /// Inline AIR statement
    AirStmt(Arc<String>),
    /// never-to-any conversion
    NeverToAny(Expr),
    /// nondeterministic choice
    Nondeterministic,
    /// Creates a mutable borrow from the given place
    /// Used only when new-mut-refs is enabled.
    BorrowMut(Place),
    /// A "two-phase" mutable borrow. These are often created when Rust inserts implicit
    /// borrows. See [https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html].
    ///
    /// This node can only appear as an argument to a Call or to a Ctor;
    /// the semantics of a TwoPhaseBorrowMut node are contextual.
    /// It is the structure of the parent node that determines where the "second phase"
    /// of the borrow is.
    ///
    /// Used only when new-mut-refs is enabled.
    TwoPhaseBorrowMut(Place),
    /// Indicates a move or a copy from the given place.
    /// These over-approximate the actual set of copies/moves.
    /// (That is, many reads marked Move or Copy should really be marked Spec).
    /// We don't know for sure if something is a "real" move or copy until mode-checking.
    ReadPlace(Place, UnfinalizedReadKind),
    /// Evaluate both in sequence and return the left value.
    /// The right side MUST NOT have any assigns it, this lets us avoid creating temporary
    /// vars that would clutter everything up.
    UseLeftWhereRightCanHaveNoAssignments(Expr, Expr),
}

#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, Copy)]
pub struct UnfinalizedReadKind {
    pub preliminary_kind: ReadKind,
    pub id: u64,
}

/// What kind of read (i.e., nonmutating access to a place) is this?
///
/// For the most part, we only care if something is a "move" or not, information
/// which is used by resolution analysis.
/// Further subdivision of kinds is only for additional clarity.
/// However, the `Spec` kind is somewhat special because we don't know if something is
/// Spec until mode-checking, whereas the other kinds are distinguished in rust_to_vir.
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, Copy)]
pub enum ReadKind {
    /// A move.
    Move,
    /// A copy. (Not a move.)
    Copy,
    /// Take a shared borrow (&). (Not a move.)
    ImmutBor,
    /// For an expression that goes unused, e.g., in the statement `foo(x, y);` the return
    /// value of `foo` goes unused. Even though this is technically a move, we can ignore
    /// it for the purposes of resolution analysis.
    Unused,
    /// Spec snapshot. (Not a move.)
    Spec,
    /// Prophetic spec snapshot. (Not a move.)
    SpecAfterBorrow,
}

#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, Copy)]
pub enum ModeWrapperMode {
    /// For Ghost wrapper
    Spec,
    /// For Tracked wrapper
    Proof,
}

/// `Place` is the replacement for `Loc` used for new-mut-refs.
/// (Actually, `Place` is already used sometimes even when
/// new-mut-refs is disabled, but only for reading.)
///
/// A `Place` represents (the computation of) a place that can be read from,
/// moved from, or mutated. Like ordinary Exprs, the evaluation of a Place expression
/// can have arbitrary side-effects.
///
/// A `Place` tree is always a sequence of modifiers that terminates in either a Local
/// or a Temporary. Note that there are no modifier nodes for dereferencing a box or dereferencing
/// a shared reference. These are implicit.
pub type Place = Arc<SpannedTyped<PlaceX>>;
pub type Places = Arc<Vec<Place>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub enum PlaceX {
    /// Place of the given field. May have a precondition if VariantCheck is set to Union
    Field(FieldOpr, Place),
    /// Conceptually, this is like a Field, accessing the 'current' field of a mut_ref.
    DerefMut(Place),
    /// Unwrap a Ghost or a Tracked
    ModeUnwrap(Place, ModeWrapperMode),
    /// Index into an array or slice (`place[expr]`)
    /// The bool = needs bounds check
    Index(Place, Expr, ArrayKind, BoundsCheck),
    /// Named local variable.
    Local(VarIdent),
    /// Evaluate the given expression and assign it to a fresh, unnamed temporary,
    /// and return the place of the temporary.
    /// The resolution_inference pass replaces many of these with named locals.
    Temporary(Expr),
    /// Evaluate expr then return the place
    /// This is useful when expanding temporaries, e.g., `Temporary(expr)` expands to
    /// `WithExpr({ tmp = expr; }, Local(tmp))`.
    /// Without this node, such a transformation would be significantly more complicated.
    WithExpr(Expr, Place),
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
    /// (The mode is only allowed to be None for one special case; see modes.rs)
    Decl { pattern: Pattern, mode: Option<Mode>, init: Option<Place>, els: Option<Expr> },
}

/// Function parameter
pub type Param = Arc<Spanned<ParamX>>;
pub type Params = Arc<Vec<Param>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub struct ParamX {
    pub name: VarIdent,
    pub typ: Typ,
    pub mode: Mode,
    /// An &mut parameter
    pub is_mut: bool,
    /// If the parameter uses a Ghost(x) or Tracked(x) pattern to unwrap the value, this is
    /// the mode of the resulting unwrapped x variable (Spec for Ghost(x), Proof for Tracked(x)).
    /// We also save a copy of the original wrapped name for lifetime_generate
    pub unwrapped_info: Option<(Mode, VarIdent)>,
}

/// Represents different levels of sizedness introduced by
/// https://github.com/rust-lang/rfcs/pull/3729.  For now we treat MetaSized and
/// PointeeSized identically (like ?Sized previously), but we distinguish them
/// here since we may need to make this handling more precise going forward.
#[derive(Copy, Debug, Serialize, Deserialize, ToDebugSNode, Clone, PartialEq, Eq, Hash)]
pub enum Sizedness {
    Sized,
    MetaSized,
    PointeeSized,
}

#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, PartialEq, Eq, Hash)]
pub enum TraitId {
    Path(Path),
    Sizedness(Sizedness),
}

pub type GenericBound = Arc<GenericBoundX>;
pub type GenericBounds = Arc<Vec<GenericBound>>;
#[derive(Debug, Serialize, Deserialize, Hash, ToDebugSNode)]
pub enum GenericBoundX {
    /// Implemented trait T(t1, ..., tn) where t1...tn usually contain some type parameters
    // REVIEW: add ImplPaths here?
    Trait(TraitId, Typs),
    /// An equality bound for associated type X of trait T(t1, ..., tn),
    /// written in Rust as T<t1, ..., tn, X = typ>
    TypEquality(Path, Typs, Ident, Typ),
    /// Const param has type (e.g., const X: usize)
    ConstTyp(Typ, Typ),
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

/// When verifying a function, specify where we auto-promote == to =~=.
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, PartialEq)]
pub struct AutoExtEqual {
    pub assert: bool,
    pub assert_by: bool,
    pub ensures: bool,
    pub invariant: bool,
}

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
    /// Only create global axioms; don't declare req/ens functions (set by prune.rs)
    pub broadcast_forall_only: bool,
    /// In triggers_auto, don't use this function as a trigger
    pub no_auto_trigger: bool,
    /// Specify which places we auto-promote == to =~= when verifying this function
    pub auto_ext_equal: AutoExtEqual,
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
    /// does this function take zero args (this is useful to keep track
    /// of because we add a dummy arg to zero functions)
    pub print_zero_args: bool,
    /// is this a method, i.e., written with x.f() syntax? useful for printing
    pub print_as_method: bool,
    pub prophecy_dependent: bool,
    /// broadcast proof from size_of global
    pub size_of_broadcast_proof: bool,
    /// is type invariant
    pub is_type_invariant_fn: bool,
    /// Marked with external_body or external_fn_specification
    /// TODO: might be duplicate with https://github.com/verus-lang/verus/pull/1473
    pub is_external_body: bool,
    /// Is the function marked unsafe (i.e., with the Rust keyword 'unsafe')
    pub is_unsafe: bool,
    /// Whether to assume that this function terminates
    pub exec_assume_termination: bool,
    /// Whether to allow this function to not terminate
    pub exec_allows_no_decreases_clause: bool,
    /// Is this only for the new_mut_ref experiment
    pub ignore_outside_new_mut_ref: bool,
}

/// Function specification of its invariant mask
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum MaskSpec {
    InvariantOpens(Span, Exprs),
    InvariantOpensExcept(Span, Exprs),
    InvariantOpensSet(Expr),
}

/// Function specification of its invariant mask
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum UnwindSpec {
    NoUnwind,
    NoUnwindWhen(Expr),
    MayUnwind,
}

#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone)]
pub enum FunctionKind {
    Static,
    /// Method declaration inside a trait
    TraitMethodDecl {
        trait_path: Path,
        has_default: bool,
    },
    /// Method implementation inside an impl, implementing a trait method for a trait for a type
    TraitMethodImpl {
        /// Fun declared by trait for this method
        method: Fun,
        /// Path of the impl (e.g. "impl2") that contains the method implementation
        impl_path: Path,
        trait_path: Path,
        trait_typ_args: Typs,
        /// If Some, inherit default method body from function in the trait:
        inherit_body_from: Option<Fun>,
    },
    /// These should get demoted into Static functions in `demote_foreign_traits`.
    /// This really only exists so that we can check the trait really is foreign.
    ForeignTraitMethodImpl {
        method: Fun,
        impl_path: Path,
        trait_path: Path,
        trait_typ_args: Typs,
    },
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

#[derive(Debug, Serialize, Deserialize, Clone, ToDebugSNode)]
pub enum Opaqueness {
    /// Opaque everywhere
    Opaque,
    /// Revealed insided the range given by 'visibility', opaque elsewhere.
    Revealed { visibility: Visibility },
}

/// Function, including signature and body
pub type Function = Arc<Spanned<FunctionX>>;
#[derive(Debug, Serialize, Deserialize, Clone)]
#[to_node_impl]
pub struct FunctionX {
    /// Name of function
    pub name: Fun,
    /// Proxy used to declare the spec of this function
    /// (e.g., some function marked `external_fn_specification`/`assume_specification`)
    pub proxy: Option<Spanned<Path>>,
    /// Kind (translation to AIR is different for each different kind)
    pub kind: FunctionKind,
    /// Access control (public/private)
    pub visibility: Visibility,
    /// Controlled by 'open'. (Only applicable to spec functions.)
    pub body_visibility: BodyVisibility,
    /// Controlled by 'opaque/opaque_outside_module'. (Only applicable to spec functions.)
    pub opaqueness: Opaqueness,
    /// Owning module
    pub owning_module: Option<Path>,
    /// exec functions are compiled, proof/spec are erased
    /// exec/proof functions can have requires/ensures, spec cannot
    /// spec functions can be used in requires/ensures, proof/exec cannot
    pub mode: Mode,
    /// Type parameters to generic functions
    /// (for trait methods, the trait parameters come first, then the method parameters)
    pub typ_params: Idents,
    /// Type bounds of generic functions
    pub typ_bounds: GenericBounds,
    /// Function parameters
    pub params: Params,
    /// Return value
    pub ret: Param,
    /// Can the ensures clause reference the 'ret' param (must be true for non-unit types)
    pub ens_has_return: bool,
    /// Preconditions (requires for proof/exec functions, recommends for spec functions)
    pub require: Exprs,
    /// Postconditions (proof/exec functions only)
    /// (regular ensures, trait-default ensures)
    pub ensure: (Exprs, Exprs),
    /// Expression in the 'returns' clause
    pub returns: Option<Expr>,
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
    /// Axioms (similar to broadcast axioms) for the FnDef type corresponding to
    /// this function, if one is generated for this particular function.
    /// Similar to 'external_spec' in the ExecClosure node, this is filled
    /// in during ast_simplify.
    pub fndef_axioms: Option<Exprs>,
    /// MaskSpec that specifies what invariants the function is allowed to open
    pub mask_spec: Option<MaskSpec>,
    /// UnwindSpec that specifies if the function is allowed to unwind
    pub unwind_spec: Option<UnwindSpec>,
    /// Allows the item to be a const declaration or static
    pub item_kind: ItemKind,
    /// Various attributes
    pub attrs: FunctionAttrs,
    /// Body of the function (may be None for foreign functions or for external_body functions)
    pub body: Option<Expr>,
    /// Extra dependencies, only used for for the purposes of recursion-well-foundedness
    /// Useful only for trusted fns.
    pub extra_dependencies: Vec<Fun>,
}

pub type RevealGroup = Arc<Spanned<RevealGroupX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct RevealGroupX {
    /// Name of the function that is used internally to represent the group.
    /// This is used, for example, to create a Node::Fun(name) for the group.
    /// Note that there is no FunctionX for the group, though.
    pub name: Fun,
    /// Access control (public/private)
    pub visibility: Visibility,
    /// Owning module
    pub owning_module: Option<Path>,
    /// If Some(crate_name), this group is revealed by default for crates that import crate_name.
    /// No more than one such group is allowed in each crate.
    pub broadcast_use_by_default_when_this_crate_is_imported: Option<Ident>,
    /// All the subgroups or functions included in this group
    pub members: Arc<Vec<Fun>>,
}

/// Single field in a variant
pub type Field = Binder<(Typ, Mode, Visibility)>;
/// List of fields in a variant
/// For tuple-style variants, the fields appear in order and are named "0", "1", etc.
/// For struct-style variants, the fields may appear in any order
pub type Fields = Binders<(Typ, Mode, Visibility)>;

#[derive(Clone, Copy, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum CtorPrintStyle {
    Tuple,  // actual tuple (a, b)
    Parens, // tuple style: Ctor(a, b)
    Braces, // struct: Ctor { a: ... }
    Const,  // just Ctor
}

pub type Variants = Arc<Vec<Variant>>;

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct Variant {
    pub name: Ident,
    pub fields: Fields,
    pub ctor_style: CtorPrintStyle,
}

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum DatatypeTransparency {
    Never,
    WhenVisible(Visibility),
}

/// After ast_simplify, all the tuples are added to the Krate, so we can uniformly
/// use Dt as a key. Prior to ast_simplify you need to use Paths as keys and handle
/// tuples separately.
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Dt {
    Path(Path),
    Tuple(usize),
}

/// struct or enum
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct DatatypeX {
    pub name: Dt,
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
    pub user_defined_invariant_fn: Option<Fun>,
    /// This is an optional value -- None means "always sized"
    /// whereas Some(T) means "The given type is Sized iff T is Sized".
    /// For structs, this is usually the last field of the struct, or is derived from it.
    /// For enums, this is always None.
    pub sized_constraint: Option<Typ>,
    /// Does this type have a Drop impl?
    pub destructor: bool,
}
pub type Datatype = Arc<Spanned<DatatypeX>>;
pub type Datatypes = Vec<Datatype>;

/// Opaque type constructors
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct OpaqueTypeX {
    pub def_fun: Fun,
    pub name: Path,
    pub typ_params: Typs,
    pub typ_bounds: GenericBounds,
}

pub type OpaqueType = Arc<Spanned<OpaqueTypeX>>;
pub type OpaqueTypes = Vec<OpaqueType>;

/// Does the trait satisfy Verus's additional dyn-compatibility requirements,
/// on top of Rust's dyn-compatibility requirements?
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum DynCompatible {
    /// If Rust accepts trait as dyn compatible, Verus also accepts trait as dyn compatible
    Accept,
    /// The trait fails one of Verus's requirements for dyn compatibility
    Reject { reason: String },
    /// The trait satisfies Verus's requirements, but has a ?Sized blanket impl,
    /// for which there is currently a known Rust unsoundness with dyn
    /// (see https://github.com/rust-lang/rust/issues/57893 );
    /// we can remove this case when the Rust issue is fixed.
    RejectUnsizedBlanketImpl { trait_path: Path },
}

pub type Trait = Arc<Spanned<TraitX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct TraitX {
    pub name: Path,
    pub proxy: Option<Spanned<Path>>,
    pub visibility: Visibility,
    // REVIEW: typ_params does not yet explicitly include Self (right now, Self is implicit)
    pub typ_params: TypPositives,
    pub typ_bounds: GenericBounds,
    pub assoc_typs: Arc<Vec<Ident>>,
    pub assoc_typs_bounds: GenericBounds,
    pub methods: Arc<Vec<Fun>>,
    pub is_unsafe: bool,
    // Initially set to None during translation to VIR,
    // then set to Some after all the Function declarations have been processed.
    pub dyn_compatible: Option<Arc<DynCompatible>>,
    // If this trait has a verifier::external_trait_extension(TSpec via TSpecImpl),
    // Some((TSpec, TSpecImpl))
    pub external_trait_extension: Option<(Path, Path)>,
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
    pub trait_typ_arg_impls: Arc<Spanned<ImplPaths>>,
    pub owning_module: Option<Path>,
    // Not declared directly to Verus, but imported based on related traits and types:
    pub auto_imported: bool,
    // Is a blanket implementation declared by external_trait_extension:
    pub external_trait_blanket: bool,
}

#[derive(Clone, Debug, Hash, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq)]
pub enum WellKnownItem {
    DropTrait,
}

pub type ModuleReveals = Arc<Spanned<Vec<Fun>>>;

pub type Module = Arc<Spanned<ModuleX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct ModuleX {
    pub path: Path,
    // add attrs here
    pub reveals: Option<ModuleReveals>,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, ToDebugSNode)]
pub enum ArchWordBits {
    Either32Or64,
    Exactly(u32),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Arch {
    pub word_bits: ArchWordBits,
}

/// An entire crate
pub type Krate = Arc<KrateX>;
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct KrateX {
    /// All functions in the crate, plus foreign functions
    pub functions: Vec<Function>,
    /// All reveal_groups in the crate
    pub reveal_groups: Vec<RevealGroup>,
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
    /// All opaque type constructors
    pub opaque_types: OpaqueTypes,
}
