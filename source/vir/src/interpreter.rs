//! A Symbolic Interpreter for VIR
//!
//! Operates on VIR's SST representation
//!
//! Current target is supporting proof by computation
//! https://github.com/secure-foundations/verus/discussions/120

use crate::ast::{
    ArchWordBits, ArithOp, BinaryOp, BitwiseOp, ComputeMode, Constant, Fun, FunX, Idents,
    InequalityOp, IntRange, IntegerTypeBitwidth, IntegerTypeBoundKind, PathX, SpannedTyped, Typ,
    TypX, UnaryOp, VarBinders, VarIdent, VarIdentDisambiguate, VirErr,
};
use crate::ast_to_sst_func::SstMap;
use crate::ast_util::{path_as_vstd_name, undecorate_typ};
use crate::context::GlobalCtx;
use crate::messages::{error, warning, Message, Span, ToAny};
use crate::sst::{Bnd, BndX, CallFun, Exp, ExpX, Exps, FunctionSst, Trigs, UniqueIdent};
use crate::unicode::valid_unicode_scalar_bigint;
use air::ast::{Binder, BinderX, Binders};
use air::scope_map::ScopeMap;
use im::Vector;
use num_bigint::BigInt;
use num_traits::identities::Zero;
use num_traits::{Euclid, FromPrimitive, One, ToPrimitive};
use std::collections::HashMap;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::ops::ControlFlow;
use std::sync::Arc;
use std::thread;

// An approximation of how many interpreter invocations we can do in 1 second (in release mode)
const RLIMIT_MULTIPLIER: u64 = 400_000;

type Env = ScopeMap<UniqueIdent, Exp>;

/// `Exps` that support `Hash` and `Eq`. Intended to never leave this module.
struct ExpsKey {
    e: Exps,
}

impl Hash for ExpsKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_exps(state, &self.e);
    }
}

impl PartialEq for ExpsKey {
    fn eq(&self, other: &Self) -> bool {
        self.e.definitely_eq(&other.e)
    }
}

impl Eq for ExpsKey {}

impl From<Exps> for ExpsKey {
    fn from(e: Exps) -> Self {
        Self { e }
    }
}
impl From<&Exps> for ExpsKey {
    fn from(e: &Exps) -> Self {
        Self { e: e.clone() }
    }
}

/// A set that allows membership queries to `Arc`'d values, such that pointer equality is necessary
/// to be called a member.
///
/// This container is intended as a safer replacement to `HashSet<*const T>`, which (while
/// memory-safe) can lead to surprising logic bugs, since the `*const` does not imply ownership,
/// leading to accidental clashes as objects appear and disappear from existence. `PtrSet` ensures
/// that such clashes cannot occur, by ensuring that every object in the set is kept alive until the
/// set itself is free'd.
#[derive(Default)]
struct PtrSet<T> {
    // Invariant: each pointer key in this set always points at its corresponding value, which
    // ensures that the strong count can never go below 0.
    store: HashMap<*const T, Arc<T>>,
}

impl<T> PtrSet<T> {
    fn new() -> Self {
        Self { store: HashMap::new() }
    }
    fn insert(&mut self, v: &Arc<T>) {
        self.store.insert(Arc::as_ptr(&v), v.clone());
    }
    fn contains(&mut self, v: &Arc<T>) -> bool {
        self.store.contains_key(&Arc::as_ptr(&v))
    }
}

/// Mutable interpreter state
struct State {
    /// Depth of our current recursion; used for formatting log output
    depth: usize,
    /// Symbol table mapping bound variables to their values
    env: Env,
    /// Number of iterations computed thus far
    iterations: u64,
    /// Log to write out extra info
    log: Option<File>,
    /// Collect messages to be displayed after the computation
    msgs: Vec<Message>,
    /// Collect and display performance data
    perf: bool,
    /// Cache function invocations, based on their arguments, so we can directly return the
    /// previously computed result.  Necessary for examples like Fibonacci.
    cache: HashMap<Fun, HashMap<ExpsKey, Exp>>,
    enable_cache: bool,
    /// Cache of expressions we have already simplified
    simplified: PtrSet<SpannedTyped<ExpX>>,
    enable_simplified_cache: bool,

    /// Performance profiling data
    cache_hits: u64,
    cache_misses: u64,
    ptr_hits: u64,
    ptr_misses: u64,
    /// Number of calls for each function
    fun_calls: HashMap<Fun, u64>,
}

// Define the function-call cache's API
impl State {
    fn insert_call(&mut self, f: &Fun, args: &Exps, result: &Exp, memoize: bool) {
        if self.enable_cache && memoize {
            self.cache.entry(f.clone()).or_default().insert(args.into(), result.clone());
        }
    }

    fn lookup_call(&mut self, f: &Fun, args: &Exps, memoize: bool) -> Option<Exp> {
        if self.enable_cache && memoize {
            if self.perf {
                let count = self.fun_calls.entry(f.clone()).or_default();
                *count += 1;
            }
            self.cache.get(f)?.get(&args.into()).cloned()
        } else {
            None
        }
    }

    fn log(&self, s: String) {
        if self.log.is_some() {
            let mut log = self.log.as_ref().unwrap();
            writeln!(log, "{}", s).expect("I/O error writing to the interpreter's log");
        }
    }
}

/// Static context for the interpreter
struct Ctx<'a> {
    /// Maps each function to the SST expression representing its body
    fun_ssts: &'a HashMap<Fun, FunctionSst>,
    /// We avoid infinite loops by running for a fixed number of intervals
    max_iterations: u64,
    arch: ArchWordBits,
    global: &'a GlobalCtx,
}

/// Interpreter-internal expressions
#[derive(Debug, Clone)]
pub enum InterpExp {
    /// Track free variables (those not introduced inside an assert_by_compute),
    /// so they don't get confused with bound variables.
    FreeVar(UniqueIdent),
    /// Optimized representation of intermediate sequence results
    Seq(Vector<Exp>),
    /// A lambda expression that carries with it the original context
    Closure(Exp, HashMap<UniqueIdent, Exp>),
    /// Optimized representation of intermediate array values
    Array(Vector<Exp>),
}

/*****************************************************************
 * Functionality needed to compute equality between expressions  *
 *****************************************************************/

/// Trait to compute syntactic equality of two objects.
trait SyntacticEquality {
    /// Compute syntactic equality. Returns `Some(b)` if syntactically, equality can be guaranteed,
    /// where `b` iff `self == other`. Otherwise, returns `None`.
    fn syntactic_eq(&self, other: &Self) -> Option<bool>;
    fn definitely_eq(&self, other: &Self) -> bool {
        matches!(self.syntactic_eq(other), Some(true))
    }
    fn definitely_ne(&self, other: &Self) -> bool {
        matches!(self.syntactic_eq(other), Some(false))
    }
    /// If we cannot definitively establish equality, we conservatively return `None`
    fn conservative_eq(&self, other: &Self) -> Option<bool> {
        self.definitely_eq(other).then(|| true)
    }
}

// Automatically get syntactic equality over typs, exps, ... once we know syntactic equality over typ, exp, ...
impl<T: SyntacticEquality> SyntacticEquality for Arc<Vec<T>> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        if self.len() != other.len() {
            Some(false)
        } else {
            let check = self.iter().zip(other.iter()).try_fold(true, |def_true, (l, r)| {
                match l.syntactic_eq(r) {
                    None => ControlFlow::Continue(false), // We still continue, since we might see a definitely false result
                    Some(false) => ControlFlow::Break(()), // Short circuit
                    Some(true) => ControlFlow::Continue(def_true),
                }
            });
            match check {
                ControlFlow::Break(_) => Some(false),
                ControlFlow::Continue(def_true) => {
                    if def_true {
                        Some(true)
                    } else {
                        None
                    }
                }
            }
        }
    }
}

impl<T: Clone + SyntacticEquality> SyntacticEquality for Vector<T> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        if self.len() != other.len() {
            Some(false)
        } else {
            let check = self.iter().zip(other.iter()).try_fold(true, |def_true, (l, r)| {
                match l.syntactic_eq(r) {
                    None => ControlFlow::Continue(false), // We still continue, since we might see a definitely false result
                    Some(false) => ControlFlow::Break(()), // Short circuit
                    Some(true) => ControlFlow::Continue(def_true),
                }
            });
            match check {
                ControlFlow::Break(_) => Some(false),
                ControlFlow::Continue(def_true) => {
                    if def_true {
                        Some(true)
                    } else {
                        None
                    }
                }
            }
        }
    }
}

impl SyntacticEquality for Typ {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        use TypX::*;
        match (undecorate_typ(self).as_ref(), undecorate_typ(other).as_ref()) {
            (Bool, Bool) => Some(true),
            (Int(l), Int(r)) => Some(l == r),
            (Tuple(typs_l), Tuple(typs_r)) => typs_l.syntactic_eq(typs_r),
            (SpecFn(formals_l, res_l), SpecFn(formals_r, res_r)) => {
                Some(formals_l.syntactic_eq(formals_r)? && res_l.syntactic_eq(res_r)?)
            }
            (Datatype(path_l, typs_l, _), Datatype(path_r, typs_r, _)) => {
                Some(path_l == path_r && typs_l.syntactic_eq(typs_r)?)
            }
            (Boxed(l), Boxed(r)) => l.syntactic_eq(r),
            (TypParam(l), TypParam(r)) => {
                if l == r {
                    Some(true)
                } else {
                    None
                }
            }
            (TypeId, TypeId) => Some(true),
            (Air(l), Air(r)) => Some(l == r),
            _ => None,
        }
    }
}

impl SyntacticEquality for Bnd {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        use BndX::*;
        match (&self.x, &other.x) {
            (Let(bnds_l), Let(bnds_r)) => {
                if bnds_l.syntactic_eq(bnds_r)? {
                    Some(true)
                } else {
                    None
                }
            }
            (Quant(q_l, bnds_l, _trigs_l), Quant(q_r, bnds_r, _trigs_r)) => {
                Some(q_l == q_r && bnds_l.conservative_eq(bnds_r)?)
            }
            (Lambda(bnds_l, _trigs_l), Lambda(bnds_r, _trigs_r)) => bnds_l.conservative_eq(bnds_r),
            (Choose(bnds_l, _trigs_l, e_l), Choose(bnds_r, _trigs_r, e_r)) => {
                Some(bnds_l.conservative_eq(bnds_r)? && e_l.syntactic_eq(e_r)?)
            }
            _ => None,
        }
    }
}

// XXX: Generalize over `Binders<T>`?
impl SyntacticEquality for Binders<Typ> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        self.iter().zip(other.iter()).try_fold(true, |acc, (bnd_l, bnd_r)| {
            Some(acc && bnd_l.name == bnd_r.name && bnd_l.a.syntactic_eq(&bnd_r.a)?)
        })
    }
}
impl SyntacticEquality for Binders<Exp> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        self.iter().zip(other.iter()).try_fold(true, |acc, (bnd_l, bnd_r)| {
            Some(acc && bnd_l.name == bnd_r.name && bnd_l.a.syntactic_eq(&bnd_r.a)?)
        })
    }
}

impl SyntacticEquality for VarBinders<Typ> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        self.iter().zip(other.iter()).try_fold(true, |acc, (bnd_l, bnd_r)| {
            Some(acc && bnd_l.name == bnd_r.name && bnd_l.a.syntactic_eq(&bnd_r.a)?)
        })
    }
}
impl SyntacticEquality for VarBinders<Exp> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        self.iter().zip(other.iter()).try_fold(true, |acc, (bnd_l, bnd_r)| {
            Some(acc && bnd_l.name == bnd_r.name && bnd_l.a.syntactic_eq(&bnd_r.a)?)
        })
    }
}

impl SyntacticEquality for Exp {
    // We expect to only call this after eval_expr has been called on both expressions
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        // Easy case where the pointers match
        if Arc::ptr_eq(self, other) {
            return Some(true);
        }
        // If we can't definitively establish equality, we conservatively return None
        let def_eq = |b| if b { Some(true) } else { None };
        use ExpX::*;
        match (&self.x, &other.x) {
            (Const(l), Const(r)) => {
                // Explicitly enumerate cases here, in case we someday introduce
                // a constant type that doesn't have a unique representation
                use Constant::*;
                match (l, r) {
                    (Bool(l), Bool(r)) => Some(l == r),
                    (Int(l), Int(r)) => Some(l == r),
                    (StrSlice(l), StrSlice(r)) => Some(l == r),
                    (Char(l), Char(r)) => Some(l == r),
                    _ => None,
                }
            }
            (Var(l), Var(r)) => def_eq(l == r),
            (VarLoc(l), VarLoc(r)) => def_eq(l == r),
            (VarAt(l, at_l), VarAt(r, at_r)) => def_eq(l == r && at_l == at_r),
            (Loc(l), Loc(r)) => l.syntactic_eq(r),
            (Old(id_l, unique_id_l), Old(id_r, unique_id_r)) => {
                def_eq(id_l == id_r && unique_id_l == unique_id_r)
            }
            (Call(CallFun::Fun(f_l, _), _, exps_l), Call(CallFun::Fun(f_r, _), _, exps_r)) => {
                if f_l == f_r && exps_l.len() == exps_r.len() {
                    def_eq(exps_l.syntactic_eq(exps_r)?)
                } else {
                    // We don't know if a function call on symbolic values
                    // will return the same or different values
                    None
                }
            }
            (CallLambda(exp_l, exps_l), CallLambda(exp_r, exps_r)) => {
                Some(exp_l.syntactic_eq(exp_r)? && exps_l.syntactic_eq(exps_r)?)
            }

            (Ctor(path_l, id_l, bnds_l), Ctor(path_r, id_r, bnds_r)) => {
                if path_l != path_r || id_l != id_r {
                    // These are definitely different datatypes or different
                    // constructors of the same datatype
                    Some(false)
                } else {
                    bnds_l.syntactic_eq(bnds_r)
                }
            }
            (Unary(op_l, e_l), Unary(op_r, e_r)) => def_eq(op_l == op_r && e_l.syntactic_eq(e_r)?),
            (UnaryOpr(op_l, e_l), UnaryOpr(op_r, e_r)) => {
                use crate::ast::UnaryOpr::*;
                let op_eq = match (op_l, op_r) {
                    // Short circuit, since in this case x != y ==> box(x) != box(y)
                    (Box(l), Box(r)) => return Some(l.syntactic_eq(r)? && e_l.syntactic_eq(e_r)?),
                    (Unbox(l), Unbox(r)) => def_eq(l.syntactic_eq(r)?),
                    (HasType(l), HasType(r)) => def_eq(l.syntactic_eq(r)?),
                    (
                        IsVariant { datatype: dt_l, variant: var_l },
                        IsVariant { datatype: dt_r, variant: var_r },
                    ) => def_eq(dt_l == dt_r && var_l == var_r),
                    (TupleField { .. }, TupleField { .. }) => {
                        panic!("TupleField should have been removed by ast_simplify!")
                    }
                    (Field(l), Field(r)) => def_eq(l == r),
                    _ => None,
                };
                def_eq(op_eq? && e_l.syntactic_eq(e_r)?)
            }
            (Binary(op_l, e1_l, e2_l), Binary(op_r, e1_r, e2_r)) => {
                def_eq(op_l == op_r && e1_l.syntactic_eq(e1_r)? && e2_l.syntactic_eq(e2_r)?)
            }
            (If(e1_l, e2_l, e3_l), If(e1_r, e2_r, e3_r)) => Some(
                e1_l.syntactic_eq(e1_r)? && e2_l.syntactic_eq(e2_r)? && e3_l.syntactic_eq(e3_r)?,
            ),
            (WithTriggers(_trigs_l, e_l), WithTriggers(_trigs_r, e_r)) => e_l.syntactic_eq(e_r),
            (Bind(bnd_l, e_l), Bind(bnd_r, e_r)) => {
                Some(bnd_l.syntactic_eq(bnd_r)? && e_l.syntactic_eq(e_r)?)
            }
            (Interp(l), Interp(r)) => match (l, r) {
                (InterpExp::FreeVar(l), InterpExp::FreeVar(r)) => def_eq(l == r),
                (InterpExp::Seq(l), InterpExp::Seq(r)) => l.syntactic_eq(r),
                _ => None,
            },
            _ => None,
        }
    }
}

/*********************************************
 * Functionality needed to hash expressions  *
 *********************************************/

// Convenience function to simplify repetitive hashing behavior over an iterator.
fn hash_iter<H: Hasher, K: Hash, V>(
    state: &mut H,
    it: impl Iterator<Item = (K, V)>,
    f: impl Fn(&mut H, V),
) {
    it.for_each(|(k, v)| {
        k.hash(state);
        f(state, v);
    })
}

fn hash_exps<H: Hasher>(state: &mut H, exps: &Exps) {
    hash_iter(state, exps.iter().enumerate(), hash_exp)
}

fn hash_exps_vector<H: Hasher>(state: &mut H, exps: &Vector<Exp>) {
    hash_iter(state, exps.iter().enumerate(), hash_exp)
}

fn hash_trigs<H: Hasher>(state: &mut H, trigs: &Trigs) {
    hash_iter(state, trigs.iter().enumerate(), hash_exps)
}

fn hash_var_binders_typ<H: Hasher>(state: &mut H, bnds: &VarBinders<Typ>) {
    hash_iter(state, bnds.iter().map(|b| (&b.name, &b.a)), |st, v| v.hash(st))
}

fn hash_binders_exp<H: Hasher>(state: &mut H, bnds: &Binders<Exp>) {
    hash_iter(state, bnds.iter().map(|b| (&b.name, &b.a)), hash_exp)
}

fn hash_var_binders_exp<H: Hasher>(state: &mut H, bnds: &VarBinders<Exp>) {
    hash_iter(state, bnds.iter().map(|b| (&b.name, &b.a)), hash_exp)
}

fn hash_bnd<H: Hasher>(state: &mut H, bnd: &Bnd) {
    use BndX::*;
    macro_rules! dohash {
        // See exact same macro in `hash_exp`
        ($($x:expr),* $(; $($f:ident($y:ident)),*)?) => {{
            $($x.hash(state);)*
            $($($f(state, $y);)*)?
        }}
    }
    match &bnd.x {
        Let(bnds) => dohash!(0; hash_var_binders_exp(bnds)),
        Quant(quant, bnds, trigs) => {
            dohash!(1, quant; hash_var_binders_typ(bnds), hash_trigs(trigs))
        }
        Lambda(bnds, trigs) => dohash!(2; hash_var_binders_typ(bnds), hash_trigs(trigs)),
        Choose(bnds, trigs, e) => dohash!(3;
                    hash_var_binders_typ(bnds), hash_trigs(trigs), hash_exp(e)),
    }
}

fn hash_exp<H: Hasher>(state: &mut H, exp: &Exp) {
    use ExpX::*;
    macro_rules! dohash {
        // A simple macro to reduce the highly repetitive code. Use `dohash!(a, b; c(d), e(f))` to
        // hash components `a`, `b`, ... that implement `Hash`; The `c(d)`, `e(f)` components after
        // the semi-colon can be used for components that do not implement `Hash` but have an
        // equivalent function for them.
        //
        // TODO: Remove all the "equivalent functions" replacing them with wrapper structs
        // instead. It is not computationally different, but would allow cleaner code overall (eg:
        // auto-derive `hash_exps` from `hash_exp`)
        ($($x:expr),* $(; $($f:ident($y:ident)),*)?) => {{
            $($x.hash(state);)*
            $($($f(state, $y);)*)?
        }}
    }
    match &exp.x {
        Const(c) => dohash!(0, c),
        Var(id) => dohash!(1, id),
        VarLoc(id) => dohash!(2, id),
        VarAt(id, va) => dohash!(3, id, va),
        Loc(e) => dohash!(4; hash_exp(e)),
        Old(id, uid) => dohash!(5, id, uid),
        Call(fun, typs, exps) => dohash!(6, fun, typs; hash_exps(exps)),
        CallLambda(lambda, args) => {
            dohash!(7; hash_exp(lambda));
            hash_iter(state, args.iter().enumerate(), hash_exp);
        }
        Ctor(path, id, bnds) => dohash!(8, path, id; hash_binders_exp(bnds)),
        NullaryOpr(op) => dohash!(-1, op),
        Unary(op, e) => dohash!(9, op; hash_exp(e)),
        UnaryOpr(op, e) => dohash!(10, op; hash_exp(e)),
        Binary(op, e1, e2) => dohash!(11, op; hash_exp(e1), hash_exp(e2)),
        BinaryOpr(op, e1, e2) => dohash!(111, op; hash_exp(e1), hash_exp(e2)),
        If(e1, e2, e3) => dohash!(12; hash_exp(e1), hash_exp(e2), hash_exp(e3)),
        WithTriggers(trigs, e) => dohash!(13; hash_trigs(trigs), hash_exp(e)),
        Bind(bnd, e) => dohash!(14; hash_bnd(bnd), hash_exp(e)),
        Interp(e) => {
            dohash!(15);
            match e {
                InterpExp::FreeVar(id) => dohash!(0, id),
                InterpExp::Seq(exps) => dohash!(1; hash_exps_vector(exps)),
                InterpExp::Closure(e, _ctx) => dohash!(2; hash_exp(e)),
                InterpExp::Array(exps) => dohash!(3; hash_exps_vector(exps)),
            }
        }
        StaticVar(f) => dohash!(16, f),
        ExecFnByName(fun) => {
            dohash!(17, fun);
        }
        ArrayLiteral(es) => dohash!(18; hash_exps(es)),
        FuelConst(i) => {
            dohash!(19, i);
        }
    }
}

/**********************
 * Utility functions  *
 **********************/

/// Truncate a u128 to a fixed width BigInt
fn u128_to_fixed_width(u: u128, width: u32) -> BigInt {
    match width {
        8 => BigInt::from_u8(u as u8),
        16 => BigInt::from_u16(u as u16),
        32 => BigInt::from_u32(u as u32),
        64 => BigInt::from_u64(u as u64),
        128 => BigInt::from_u128(u as u128),
        _ => panic!("Unexpected fixed-width integer type U({})", width),
    }
    .unwrap()
}

/// Truncate an i128 to a fixed width BigInt
fn i128_to_fixed_width(i: i128, width: u32) -> BigInt {
    match width {
        8 => BigInt::from_i8(i as i8),
        16 => BigInt::from_i16(i as i16),
        32 => BigInt::from_i32(i as i32),
        64 => BigInt::from_i64(i as i64),
        128 => BigInt::from_i128(i as i128),
        _ => panic!("Unexpected fixed-width integer type U({})", width),
    }
    .unwrap()
}

/// Truncate a u128 to an arch-specific BigInt, if possible
fn u128_to_arch_width(u: u128, arch: ArchWordBits) -> Option<BigInt> {
    match arch {
        ArchWordBits::Either32Or64 => {
            let v32 = u128_to_fixed_width(u, 32);
            let v64 = u128_to_fixed_width(u, 64);
            if v32 == v64 { Some(v32) } else { None }
        }
        ArchWordBits::Exactly(v) => Some(u128_to_fixed_width(u, v)),
    }
}

/// Truncate an i128 to an arch-specific BigInt, if possible
fn i128_to_arch_width(i: i128, arch: ArchWordBits) -> Option<BigInt> {
    match arch {
        ArchWordBits::Either32Or64 => {
            let v32 = i128_to_fixed_width(i, 32);
            let v64 = i128_to_fixed_width(i, 64);
            if v32 == v64 { Some(v32) } else { None }
        }
        ArchWordBits::Exactly(v) => Some(i128_to_fixed_width(i, v)),
    }
}

fn u128_to_width(u: u128, width: IntegerTypeBitwidth, arch: ArchWordBits) -> Option<BigInt> {
    match width {
        IntegerTypeBitwidth::Width(w) => Some(u128_to_fixed_width(u, w)),
        IntegerTypeBitwidth::ArchWordSize => u128_to_arch_width(u, arch),
    }
}

fn i128_to_width(i: i128, width: IntegerTypeBitwidth, arch: ArchWordBits) -> Option<BigInt> {
    match width {
        IntegerTypeBitwidth::Width(w) => Some(i128_to_fixed_width(i, w)),
        IntegerTypeBitwidth::ArchWordSize => i128_to_arch_width(i, arch),
    }
}

/// Displays data for profiling/debugging the interpreter
fn display_perf_stats(state: &State) {
    if state.perf {
        state.log(format!("\n{}\nPerformance Stats\n{}\n", "*".repeat(80), "*".repeat(80)));
        state.log(format!("Performed {} interpreter iterations", state.iterations));
        if state.enable_simplified_cache {
            let sum = state.ptr_hits + state.ptr_misses;
            let hit_perc = 100.0 * (state.ptr_hits as f64 / sum as f64);
            state.log(format!(
                "Simplified cache had {} hits out of {} ({:.1}%)",
                state.ptr_hits, sum, hit_perc
            ));
        } else {
            state.log("Simplified cache was disabled".to_string());
        }
        if state.enable_cache {
            let sum = state.cache_hits + state.cache_misses;
            let hit_perc = 100.0 * (state.cache_hits as f64 / sum as f64);
            state.log(format!(
                "Call result cache had {} hits out of {} ({:.1}%)",
                state.cache_hits, sum, hit_perc
            ));

            let mut cache_stats: Vec<(&Fun, usize)> =
                state.cache.iter().map(|(fun, vec)| (fun, vec.len())).collect();
            cache_stats.sort_by(|a, b| b.1.cmp(&a.1));
            for (fun, calls) in &cache_stats {
                state.log(format!("{:?} cached {} distinct invocations", fun.path, calls));
            }
        } else {
            state.log("Function-call cache was disabled".to_string());
        }
        state.log(format!("\nRaw call numbers:"));
        let mut fun_call_stats: Vec<(&Fun, _)> = state.fun_calls.iter().collect();
        fun_call_stats.sort_by(|a, b| b.1.cmp(&a.1));
        for (fun, count) in fun_call_stats {
            state.log(format!("{:?} called {} times", fun.path, count));
        }
    }
}

/***********************************************
 * Special handling for interpreting sequences *
 ***********************************************/

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub enum SeqFn {
    Empty,
    New,
    Push,
    Update,
    Subrange,
    Add,
    Len,
    Index,
    ExtEqual,
    Last,
}

// TODO: Make the matching here more robust to changes in vstd
/// Identify sequence functions for which we provide custom interpretation
pub(crate) fn is_sequence_fn(fun: &Fun) -> Option<SeqFn> {
    use SeqFn::*;
    match path_as_vstd_name(&fun.path).as_ref().map(|x| x.as_str()) {
        Some("seq::Seq::empty") => Some(Empty),
        Some("seq::Seq::new") => Some(New),
        Some("seq::Seq::push") => Some(Push),
        Some("seq::Seq::update") => Some(Update),
        Some("seq::Seq::subrange") => Some(Subrange),
        Some("seq::Seq::add") => Some(Add),
        Some("seq::Seq::len") => Some(Len),
        Some("seq::Seq::index") => Some(Index),
        Some("seq::Seq::ext_equal") => Some(ExtEqual),
        Some("seq::Seq::last") => Some(Last),
        _ => None,
    }
}

fn strs_to_idents(s: Vec<&str>) -> Idents {
    let idents = s.iter().map(|s| Arc::new(s.to_string())).collect();
    Arc::new(idents)
}

pub(crate) fn is_seq_to_sst_fun(fun: &Fun) -> bool {
    match is_sequence_fn(fun) {
        Some(SeqFn::Empty | SeqFn::Push) => true,
        _ => false,
    }
}

/// Convert an interpreter-internal sequence representation back into a
/// representation we can pass to AIR
// TODO: More robust way of pointing to vstd's sequence functions
fn seq_to_sst(span: &Span, typ: Typ, s: &Vector<Exp>) -> Exp {
    let exp_new = |e: ExpX| SpannedTyped::new(span, &typ, e);
    let typs = Arc::new(vec![typ.clone()]);
    let path_empty = Arc::new(PathX {
        krate: Some(Arc::new("vstd".to_string())),
        segments: strs_to_idents(vec!["seq", "Seq", "empty"]),
    });
    let path_push = Arc::new(PathX {
        krate: Some(Arc::new("vstd".to_string())),
        segments: strs_to_idents(vec!["seq", "Seq", "push"]),
    });
    let fun_empty = Arc::new(FunX { path: path_empty });
    let fun_push = Arc::new(FunX { path: path_push });
    let empty = exp_new(ExpX::Call(CallFun::Fun(fun_empty, None), typs.clone(), Arc::new(vec![])));
    let seq = s.iter().fold(empty, |acc, e| {
        let args = Arc::new(vec![acc, e.clone()]);
        exp_new(ExpX::Call(CallFun::Fun(fun_push.clone(), None), typs.clone(), args))
    });
    seq
}

/// Convert an interpreter-internal array representation back into a
/// representation we can pass to AIR
fn array_to_sst(span: &Span, typ: Typ, arr: &Vector<Exp>) -> Exp {
    let exp_new = |e: ExpX| SpannedTyped::new(span, &typ, e);
    let exps = Arc::new(arr.iter().cloned().collect());
    exp_new(ExpX::ArrayLiteral(exps))
}

/// Custom interpretation for sequence functions.
/// Expects to be called after is_sequence_fn has already identified
/// the relevant sequence function.  We still pass in the original Call Exp,
/// so that we can return it as a default if we encounter symbolic values
fn eval_seq(
    ctx: &Ctx,
    state: &mut State,
    seq_fn: SeqFn,
    exp: &Exp,
    args: &Exps,
) -> Result<Exp, VirErr> {
    use ExpX::*;
    use InterpExp::*;
    match &exp.x {
        Call(fun, typs, _old_args) => {
            let exp_new = |e: ExpX| SpannedTyped::new(&exp.span, &exp.typ, e);
            let bool_new = |b: bool| Ok(exp_new(Const(Constant::Bool(b))));
            let int_new = |i: BigInt| Ok(exp_new(Const(Constant::Int(i))));
            let seq_new = |v| Ok(exp_new(Interp(Seq(v))));
            // If we can't make any progress at all, we return the partially simplified call
            let ok = Ok(exp_new(Call(fun.clone(), typs.clone(), args.clone())));
            // We made partial progress, so convert the internal sequence back to SST
            // and reassemble a call from the rest of the args
            let ok_seq = |seq_exp: &Exp, seq: &Vector<Exp>, args: &[Exp]| {
                let mut new_args = vec![seq_to_sst(&seq_exp.span, typs[0].clone(), &seq)];
                new_args.extend(args.iter().map(|arg| arg.clone()));
                let new_args = Arc::new(new_args);
                Ok(exp_new(Call(fun.clone(), typs.clone(), new_args)))
            };
            let get_int = |e: &Exp| match &e.x {
                UnaryOpr(crate::ast::UnaryOpr::Box(_), e) => match &e.x {
                    Const(Constant::Int(index)) => Some(BigInt::to_usize(index).unwrap()),
                    _ => None,
                },
                _ => None,
            };
            use SeqFn::*;
            match seq_fn {
                Empty => seq_new(Vector::new()),
                New => {
                    match get_int(&args[0]) {
                        Some(len) => {
                            // Extract the boxed lambda argument passed to Seq::new
                            let lambda = match &args[1].x {
                                UnaryOpr(crate::ast::UnaryOpr::Box(_), e) => e,
                                _ => panic!(
                                    "Expected Seq::new's second argument to be boxed.  Got {:?} instead",
                                    args[1]
                                ),
                            };
                            // Apply the lambda to each index of the new sequence
                            let vec: Result<Vec<Exp>, VirErr> = (0..len)
                                .map(|i| {
                                    let int_typ = Arc::new(TypX::Int(IntRange::Int));
                                    let int_i = exp_new(Const(Constant::Int(BigInt::from(i))));
                                    let boxed_i = exp_new(UnaryOpr(
                                        crate::ast::UnaryOpr::Box(int_typ),
                                        int_i,
                                    ));
                                    let args = Arc::new(vec![boxed_i]);
                                    let call = exp_new(CallLambda(lambda.clone(), args));
                                    eval_expr_internal(ctx, state, &call)
                                })
                                .collect();
                            let im_vec: Vector<Exp> = vec?.into_iter().collect();
                            seq_new(im_vec)
                        }
                        _ => ok,
                    }
                }
                Push => match &args[0].x {
                    Interp(Seq(s)) => {
                        let mut s = s.clone();
                        s.push_back(args[1].clone());
                        seq_new(s)
                    }
                    _ => ok,
                },
                Update => match &args[0].x {
                    Interp(Seq(s)) => match get_int(&args[1]) {
                        Some(index) if index < s.len() => {
                            let s = s.update(index, args[2].clone());
                            seq_new(s)
                        }
                        _ => ok_seq(&args[0], &s, &args[1..]),
                    },
                    _ => ok,
                },
                Subrange => match &args[0].x {
                    Interp(Seq(s)) => {
                        let start = get_int(&args[1]);
                        let end = get_int(&args[2]);
                        match (start, end) {
                            (Some(start), Some(end)) if start <= end && end <= s.len() => {
                                seq_new(s.clone().slice(start..end))
                            }
                            _ => ok_seq(&args[0], &s, &args[1..]),
                        }
                    }
                    _ => ok,
                },
                Add => match (&args[0].x, &args[1].x) {
                    (Interp(Seq(s1)), Interp(Seq(s2))) => {
                        let mut s = s1.clone();
                        s.append(s2.clone());
                        seq_new(s)
                    }
                    (_, Interp(Seq(s2))) => ok_seq(&args[1], &s2, &args[0..1]),
                    (Interp(Seq(s1)), _) => ok_seq(&args[0], &s1, &args[1..]),
                    _ => ok,
                },
                Len => match &args[0].x {
                    Interp(Seq(s)) => int_new(BigInt::from_usize(s.len()).unwrap()),
                    _ => ok,
                },
                Index => match &args[0].x {
                    Interp(Seq(s)) => match &args[1].x {
                        UnaryOpr(crate::ast::UnaryOpr::Box(_), e) => match &e.x {
                            Const(Constant::Int(index)) => match BigInt::to_usize(index) {
                                None => {
                                    let msg = "Computation tried to index into a sequence using a value that does not fit into usize";
                                    state.msgs.push(warning(&exp.span, msg));
                                    ok_seq(&args[0], &s, &args[1..])
                                }
                                Some(index) => {
                                    if index < s.len() {
                                        Ok(s[index].clone())
                                    } else {
                                        let msg = "Computation tried to index past the length of a sequence";
                                        state.msgs.push(warning(&exp.span, msg));
                                        ok_seq(&args[0], &s, &args[1..])
                                    }
                                }
                            },
                            _ => ok_seq(&args[0], &s, &args[1..]),
                        },
                        _ => ok_seq(&args[0], &s, &args[1..]),
                    },
                    _ => ok,
                },
                ExtEqual => match (&args[0].x, &args[1].x) {
                    (Interp(Seq(l)), Interp(Seq(r))) => match l.syntactic_eq(r) {
                        None => {
                            let new_args = vec![
                                seq_to_sst(&args[0].span, args[0].typ.clone(), &l),
                                seq_to_sst(&args[1].span, args[1].typ.clone(), &r),
                            ];
                            let new_args = Arc::new(new_args);
                            Ok(exp_new(Call(fun.clone(), typs.clone(), new_args)))
                        }
                        Some(b) => bool_new(b),
                    },
                    (_, Interp(Seq(r))) => ok_seq(&args[1], &r, &args[0..1]),
                    (Interp(Seq(l)), _) => ok_seq(&args[0], &l, &args[1..]),
                    _ => ok,
                },
                Last => match &args[0].x {
                    Interp(Seq(s)) => {
                        if s.len() > 0 {
                            Ok(s.last().unwrap().clone())
                        } else {
                            ok_seq(&args[0], &s, &args[1..])
                        }
                    }
                    _ => ok,
                },
            }
        }
        _ => panic!(
            "Expected sequence expression to be a Call.  Got {:} instead.",
            exp.x.to_user_string(&ctx.global)
        ),
    }
}

fn unbox(e: &Exp) -> Exp {
    if let ExpX::UnaryOpr(crate::ast::UnaryOpr::Box(_), e) = &e.x { e.clone() } else { e.clone() }
}

/// Custom interpretation for array_index
fn eval_array_index(
    state: &mut State,
    exp: &Exp,
    arr: &Exp,
    index_exp: &Exp,
) -> Result<Exp, VirErr> {
    use ExpX::*;
    use InterpExp::*;
    let exp_new = |e: ExpX| SpannedTyped::new(&exp.span, &exp.typ, e);
    // If we can't make any progress at all, we return the partially simplified call
    let ok = Ok(exp_new(Binary(crate::ast::BinaryOp::ArrayIndex, arr.clone(), index_exp.clone())));
    // For now, the only possible function is array_index
    match &arr.x {
        Interp(Array(s)) => match &unbox(index_exp).x {
            Const(Constant::Int(i)) => match BigInt::to_usize(i) {
                None => {
                    let msg = "Computation tried to index into an array using a value that does not fit into usize";
                    state.msgs.push(warning(&exp.span, msg));
                    ok
                }
                Some(index) => {
                    if index < s.len() {
                        Ok(s[index].clone())
                    } else {
                        let msg = "Computation tried to index past the length of an array";
                        state.msgs.push(warning(&exp.span, msg));
                        ok
                    }
                }
            },
            _ => ok,
        },
        _ => ok,
    }
}

/********************
 * Core interpreter *
 ********************/

/// Symbolically execute the expression as far as we can,
/// stopping when we hit a symbolic control-flow decision
fn eval_expr_internal(ctx: &Ctx, state: &mut State, exp: &Exp) -> Result<Exp, VirErr> {
    state.iterations += 1;
    if state.iterations > ctx.max_iterations {
        return Err(error(&exp.span, "assert_by_compute timed out"));
    }
    state.log(format!(
        "{}Evaluating {:}",
        "\t".repeat(state.depth),
        exp.x.to_user_string(&ctx.global)
    ));
    let ok = Ok(exp.clone());
    if state.enable_simplified_cache && state.simplified.contains(exp) {
        state.ptr_hits += 1;
        state
            .log(format!("{}=> already simplified as far as it will go", "\t".repeat(state.depth)));
        return Ok(exp.clone());
    }
    state.ptr_misses += 1;
    state.depth += 1;
    let exp_new = |e: ExpX| Ok(SpannedTyped::new(&exp.span, &exp.typ, e));
    let bool_new = |b: bool| exp_new(Const(Constant::Bool(b)));
    let int_new = |i: BigInt| exp_new(Const(Constant::Int(i)));
    let zero = int_new(BigInt::zero());
    use ExpX::*;
    let r = match &exp.x {
        Const(_) => ok,
        Var(id) => match state.env.get(id) {
            None => {
                state.log(format!("Failed to find a match for variable {:?}", id));
                // "Hide" the variable, so that we don't accidentally
                // mix free and bound variables while interpreting
                exp_new(Interp(InterpExp::FreeVar(id.clone())))
            }
            Some(e) => Ok(e.clone()),
        },
        NullaryOpr(op) => {
            match op {
                crate::ast::NullaryOpr::ConstGeneric(typ) => {
                    match &**typ {
                        TypX::TypParam(id) => {
                            let var_id = VarIdent(id.clone(), VarIdentDisambiguate::TypParamBare);
                            match state.env.get(&var_id) {
                                None => {
                                    state.log(format!(
                                        "Failed to find a match for const generic {:?}",
                                        var_id
                                    ));
                                    // "Hide" the variable, so that we don't accidentally
                                    // mix free and bound variables while interpreting
                                    exp_new(Interp(InterpExp::FreeVar(var_id.clone())))
                                }
                                Some(e) => Ok(e.clone()),
                            }
                        }
                        _ => ok,
                    }
                }
                _ => ok,
            }
        }
        Unary(op, e) => {
            use Constant::*;
            use UnaryOp::*;
            let e = eval_expr_internal(ctx, state, e)?;
            let ok = exp_new(Unary(*op, e.clone()));
            match &e.x {
                Const(Bool(b)) => {
                    // Explicitly enumerate UnaryOps, in case more are added
                    match op {
                        Not => bool_new(!b),
                        BitNot(..)
                        | Clip { .. }
                        | HeightTrigger
                        | Trigger(_)
                        | CoerceMode { .. }
                        | StrLen
                        | StrIsAscii
                        | InferSpecForLoopIter { .. } => ok,
                        MustBeFinalized | UnaryOp::MustBeElaborated => {
                            panic!("Found MustBeFinalized op {:?} after calling finalize_exp", exp)
                        }
                        CastToInteger => {
                            panic!("CastToInteger should have been removed by poly!")
                        }
                    }
                }
                Const(Int(i)) => {
                    // Explicitly enumerate UnaryOps, in case more are added
                    match op {
                        BitNot(None) => match i.to_i128() {
                            Some(i) => int_new(BigInt::from_i128(!i).unwrap()),
                            None => ok,
                        },
                        BitNot(Some(w)) => match i.to_u128() {
                            Some(i) => match u128_to_width(!i, *w, ctx.arch) {
                                Some(i) => int_new(i),
                                None => ok,
                            },
                            None => ok,
                        },
                        Clip { range, truncate: _ } => {
                            let in_range =
                                |lower: BigInt, upper: BigInt| !(i < &lower || i > &upper);
                            let mut apply_range = |lower: BigInt, upper: BigInt| {
                                if !in_range(lower, upper) {
                                    let msg =
                                        "Computation clipped an integer that was out of range";
                                    state.msgs.push(warning(&exp.span, msg));
                                    ok.clone()
                                } else {
                                    // Use the type of clip, not the inner expression,
                                    // to reflect the type change imposed by clip
                                    Ok(SpannedTyped::new(&e.span, &exp.typ, e.x.clone()))
                                }
                            };
                            let apply_unicode_scalar_range = |state: &mut State| {
                                if !valid_unicode_scalar_bigint(i) {
                                    let msg =
                                        "Computation clipped an integer that was out of range";
                                    state.msgs.push(warning(&exp.span, msg));
                                    ok.clone()
                                } else {
                                    // Use the type of clip, not the inner expression,
                                    // to reflect the type change imposed by clip
                                    Ok(SpannedTyped::new(&e.span, &exp.typ, e.x.clone()))
                                }
                            };
                            match range {
                                IntRange::Int => ok,
                                IntRange::Nat => apply_range(BigInt::zero(), i.clone()),
                                IntRange::Char => apply_unicode_scalar_range(state),
                                IntRange::U(n) => {
                                    let u = apply_range(
                                        BigInt::zero(),
                                        (BigInt::one() << n) - BigInt::one(),
                                    );
                                    u
                                }
                                IntRange::I(n) => apply_range(
                                    -1 * (BigInt::one() << (n - 1)),
                                    (BigInt::one() << (n - 1)) - BigInt::one(),
                                ),
                                IntRange::USize => {
                                    let lower = BigInt::zero();
                                    let upper = |n| (BigInt::one() << n) - BigInt::one();
                                    match ctx.arch {
                                        ArchWordBits::Either32Or64 => {
                                            if in_range(lower.clone(), upper(32)) {
                                                // then must be in range of 64 too
                                                apply_range(lower, upper(32))
                                            } else {
                                                // may or may not be in range of 64, we must conservatively give up.
                                                state.msgs.push(warning(&exp.span, "Computation clipped an arch-dependent integer that was out of range"));
                                                ok.clone()
                                            }
                                        }
                                        ArchWordBits::Exactly(n) => apply_range(lower, upper(n)),
                                    }
                                }
                                IntRange::ISize => {
                                    let lower = |n| -1 * (BigInt::one() << (n - 1));
                                    let upper = |n| (BigInt::one() << (n - 1)) - BigInt::one();
                                    match ctx.arch {
                                        ArchWordBits::Either32Or64 => {
                                            if in_range(lower(32), upper(32)) {
                                                // then must be in range of 64 too
                                                apply_range(lower(32), upper(32))
                                            } else {
                                                // may or may not be in range of 64, we must conservatively give up.
                                                state.msgs.push(warning(&exp.span, "Computation clipped an arch-dependent integer that was out of range"));
                                                ok.clone()
                                            }
                                        }
                                        ArchWordBits::Exactly(n) => apply_range(lower(n), upper(n)),
                                    }
                                }
                            }
                        }
                        MustBeFinalized | UnaryOp::MustBeElaborated => {
                            panic!("Found MustBeFinalized op {:?} after calling finalize_exp", exp)
                        }
                        CastToInteger => {
                            panic!("CastToInteger should have been removed by poly!")
                        }
                        Not
                        | HeightTrigger
                        | Trigger(_)
                        | CoerceMode { .. }
                        | StrLen
                        | StrIsAscii
                        | InferSpecForLoopIter { .. } => ok,
                    }
                }
                // !(!(e_inner)) == e_inner
                Unary(Not, e_inner) if matches!(op, Not) => Ok(e_inner.clone()),
                _ => ok,
            }
        }
        UnaryOpr(op, e) => {
            let e = eval_expr_internal(ctx, state, e)?;
            let ok = exp_new(UnaryOpr(op.clone(), e.clone()));
            use crate::ast::UnaryOpr::*;
            match op {
                Box(_) => match &e.x {
                    // Sequences move through box
                    Interp(InterpExp::Seq(s)) => exp_new(Interp(InterpExp::Seq(s.clone()))),
                    // Arrays move through box
                    Interp(InterpExp::Array(s)) => exp_new(Interp(InterpExp::Array(s.clone()))),
                    _ => ok,
                },
                Unbox(_) => match &e.x {
                    UnaryOpr(Box(_), inner_e) => Ok(inner_e.clone()),
                    // Sequences move through unbox
                    Interp(InterpExp::Seq(s)) => exp_new(Interp(InterpExp::Seq(s.clone()))),
                    // Arrays move through unbox
                    Interp(InterpExp::Array(s)) => exp_new(Interp(InterpExp::Array(s.clone()))),
                    _ => ok,
                },
                HasType(_) => ok,
                IsVariant { datatype, variant } => match &e.x {
                    Ctor(dt, var, _) => bool_new(dt == datatype && var == variant),
                    _ => ok,
                },
                TupleField { .. } => panic!("TupleField should have been removed by ast_simplify!"),
                Field(f) => match &e.x {
                    Ctor(_dt, _var, binders) => {
                        match binders.iter().position(|b| b.name == f.field) {
                            None => ok,
                            Some(i) => Ok(binders.get(i).unwrap().a.clone()),
                        }
                    }
                    _ => ok,
                },
                IntegerTypeBound(kind, _) => {
                    // We're about to take an exponent, so bound this
                    // by something reasonable.
                    match &e.x {
                        Const(Constant::Int(i)) => match i.to_u32() {
                            Some(i) if i <= 1024 => match kind {
                                IntegerTypeBoundKind::ArchWordBits => match ctx.arch {
                                    ArchWordBits::Exactly(b) => {
                                        int_new(BigInt::from_u32(b).unwrap())
                                    }
                                    _ => ok,
                                },
                                _ if i == 0 => int_new(BigInt::from_usize(0).unwrap()),
                                IntegerTypeBoundKind::UnsignedMax => {
                                    int_new(BigInt::from_usize(2).unwrap().pow(i) - 1)
                                }
                                IntegerTypeBoundKind::SignedMax => {
                                    int_new(BigInt::from_usize(2).unwrap().pow(i - 1) - 1)
                                }
                                IntegerTypeBoundKind::SignedMin => {
                                    int_new(-BigInt::from_usize(2).unwrap().pow(i - 1))
                                }
                            },
                            _ => ok,
                        },
                        _ => ok,
                    }
                }
                CustomErr(_) => Ok(e),
            }
        }
        Binary(op, e1, e2) => {
            use BinaryOp::*;
            use Constant::*;
            // We initially evaluate only e1, since op may short circuit
            // e.g., x != 0 && y == 5 / x
            let e1 = eval_expr_internal(ctx, state, e1)?;
            // Create the default value with a possibly updated value for e2
            let ok_e2 = |e2: Exp| exp_new(Binary(*op, e1.clone(), e2.clone()));
            match op {
                And => match &e1.x {
                    Const(Bool(true)) => eval_expr_internal(ctx, state, e2),
                    Const(Bool(false)) => bool_new(false),
                    _ => {
                        let e2 = eval_expr_internal(ctx, state, e2)?;
                        match &e2.x {
                            Const(Bool(true)) => Ok(e1.clone()),
                            Const(Bool(false)) => bool_new(false),
                            _ => ok_e2(e2),
                        }
                    }
                },
                Or => match &e1.x {
                    Const(Bool(true)) => bool_new(true),
                    Const(Bool(false)) => eval_expr_internal(ctx, state, e2),
                    _ => {
                        let e2 = eval_expr_internal(ctx, state, e2)?;
                        match &e2.x {
                            Const(Bool(true)) => bool_new(true),
                            Const(Bool(false)) => Ok(e1.clone()),
                            _ => ok_e2(e2),
                        }
                    }
                },
                Xor => {
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    match (&e1.x, &e2.x) {
                        (Const(Bool(b1)), Const(Bool(b2))) => {
                            let r = (*b1 && !b2) || (!b1 && *b2);
                            bool_new(r)
                        }
                        (Const(Bool(true)), _) => exp_new(Unary(UnaryOp::Not, e2.clone())),
                        (Const(Bool(false)), _) => Ok(e2.clone()),
                        (_, Const(Bool(true))) => exp_new(Unary(UnaryOp::Not, e1.clone())),
                        (_, Const(Bool(false))) => Ok(e1.clone()),
                        _ => ok_e2(e2),
                    }
                }
                Implies => {
                    match &e1.x {
                        Const(Bool(true)) => eval_expr_internal(ctx, state, e2),
                        Const(Bool(false)) => bool_new(true),
                        _ => {
                            let e2 = eval_expr_internal(ctx, state, e2)?;
                            match &e2.x {
                                Const(Bool(true)) => bool_new(false),
                                Const(Bool(false)) =>
                                // Recurse in case we can simplify the new negation
                                {
                                    eval_expr_internal(
                                        ctx,
                                        state,
                                        &exp_new(Unary(UnaryOp::Not, e1.clone()))?,
                                    )
                                }
                                _ => ok_e2(e2),
                            }
                        }
                    }
                }
                Eq(_mode) => {
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    match e1.syntactic_eq(&e2) {
                        None => ok_e2(e2),
                        Some(b) => bool_new(b),
                    }
                }
                Ne => {
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    match e1.syntactic_eq(&e2) {
                        None => ok_e2(e2),
                        Some(b) => bool_new(!b),
                    }
                }
                Inequality(op) => {
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    match (&e1.x, &e2.x) {
                        (Const(Int(i1)), Const(Int(i2))) => {
                            use InequalityOp::*;
                            let b = match op {
                                Le => i1 <= i2,
                                Ge => i1 >= i2,
                                Lt => i1 < i2,
                                Gt => i1 > i2,
                            };
                            bool_new(b)
                        }
                        _ => ok_e2(e2),
                    }
                }
                Arith(op, _mode) => {
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    use ArithOp::*;
                    match (&e1.x, &e2.x) {
                        // Ideal case where both sides are concrete
                        (Const(Int(i1)), Const(Int(i2))) => {
                            use ArithOp::*;
                            match op {
                                Add => int_new(i1 + i2),
                                Sub => int_new(i1 - i2),
                                Mul => int_new(i1 * i2),
                                EuclideanDiv => {
                                    if i2.is_zero() {
                                        ok_e2(e2) // Treat as symbolic instead of erroring
                                    } else {
                                        int_new(i1.div_euclid(i2))
                                    }
                                }
                                EuclideanMod => {
                                    if i2.is_zero() {
                                        ok_e2(e2) // Treat as symbolic instead of erroring
                                    } else {
                                        int_new(i1.rem_euclid(i2))
                                    }
                                }
                            }
                        }
                        // Special cases for certain concrete values
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, Add) => Ok(e2.clone()),
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, Mul) => zero,
                        (Const(Int(i1)), _) if i1.is_one() && matches!(op, Mul) => Ok(e2.clone()),
                        (_, Const(Int(i2))) if i2.is_zero() => {
                            use ArithOp::*;
                            match op {
                                Add | Sub => Ok(e1.clone()),
                                Mul => zero,
                                EuclideanDiv => {
                                    ok_e2(e2) // Treat as symbolic instead of erroring
                                }
                                EuclideanMod => {
                                    ok_e2(e2) // Treat as symbolic instead of erroring
                                }
                            }
                        }
                        (_, Const(Int(i2))) if i2.is_one() && matches!(op, EuclideanMod) => {
                            int_new(BigInt::zero())
                        }
                        (_, Const(Int(i2))) if i2.is_one() && matches!(op, Mul | EuclideanDiv) => {
                            Ok(e1.clone())
                        }
                        _ => {
                            match op {
                                // X - X => 0
                                ArithOp::Sub if e1.definitely_eq(&e2) => zero,
                                _ => ok_e2(e2),
                            }
                        }
                    }
                }
                Bitwise(op, _) => {
                    use BitwiseOp::*;
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    match (&e1.x, &e2.x) {
                        // Ideal case where both sides are concrete
                        (Const(Int(i1)), Const(Int(i2))) => match op {
                            BitXor => int_new(i1 ^ i2),
                            BitAnd => int_new(i1 & i2),
                            BitOr => int_new(i1 | i2),
                            Shr(_) => match i2.to_u128() {
                                None => ok,
                                Some(i2) => int_new(i1 >> i2),
                            },
                            Shl(w, signed) => {
                                if *signed {
                                    match (i1.to_i128(), i2.to_u128()) {
                                        (Some(i1), Some(i2)) => {
                                            let i1_shifted =
                                                if i2 >= 128 { 0i128 } else { i1 << i2 };
                                            match i128_to_width(i1_shifted, *w, ctx.arch) {
                                                Some(i) => int_new(i),
                                                None => ok,
                                            }
                                        }
                                        _ => ok,
                                    }
                                } else {
                                    match (i1.to_u128(), i2.to_u128()) {
                                        (Some(i1), Some(i2)) => {
                                            let i1_shifted =
                                                if i2 >= 128 { 0u128 } else { i1 << i2 };
                                            match u128_to_width(i1_shifted, *w, ctx.arch) {
                                                Some(i) => int_new(i),
                                                None => ok,
                                            }
                                        }
                                        _ => ok,
                                    }
                                }
                            }
                        },
                        // Special cases for certain concrete values
                        (Const(Int(i)), _) | (_, Const(Int(i)))
                            if i.is_zero() && matches!(op, BitAnd) =>
                        {
                            zero
                        }
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, BitOr) => {
                            Ok(e2.clone())
                        }
                        (_, Const(Int(i2))) if i2.is_zero() && matches!(op, BitOr) => {
                            Ok(e1.clone())
                        }
                        _ => {
                            match op {
                                // X ^ X => 0
                                BitXor if e1.definitely_eq(&e2) => zero,
                                // X & X = X, X | X = X
                                BitAnd | BitOr if e1.definitely_eq(&e2) => Ok(e1.clone()),
                                _ => ok_e2(e2),
                            }
                        }
                    }
                }
                ArrayIndex => {
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    eval_array_index(state, exp, &e1, &e2)
                }
                HeightCompare { .. } | StrGetChar => ok_e2(e2.clone()),
            }
        }
        BinaryOpr(op, e1, e2) => {
            let e1 = eval_expr_internal(ctx, state, e1)?;
            let e2 = eval_expr_internal(ctx, state, e2)?;
            match op {
                crate::ast::BinaryOpr::ExtEq(..) => match e1.syntactic_eq(&e2) {
                    None => exp_new(BinaryOpr(op.clone(), e1.clone(), e2.clone())),
                    Some(b) => bool_new(b),
                },
            }
        }
        If(e1, e2, e3) => {
            let e1 = eval_expr_internal(ctx, state, e1)?;
            match &e1.x {
                Const(Constant::Bool(b)) => {
                    if *b {
                        eval_expr_internal(ctx, state, e2)
                    } else {
                        eval_expr_internal(ctx, state, e3)
                    }
                }
                _ => {
                    // We still try to simplify both branches, if we can
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    let e3 = eval_expr_internal(ctx, state, e3)?;
                    exp_new(If(e1, e2, e3))
                }
            }
        }
        Call(CallFun::Fun(fun, resolved_method), typs, args) => {
            let (fun, typs) = match resolved_method {
                None => (fun, typs),
                Some((f, ts)) => (f, ts),
            };
            if state.perf {
                // Record the call for later performance analysis
                match state.fun_calls.get_mut(fun) {
                    None => {
                        state.fun_calls.insert(fun.clone(), 1);
                    }
                    Some(count) => {
                        *count += 1;
                    }
                }
            }
            // Simplify arguments
            let new_args: Result<Vec<Exp>, VirErr> =
                args.iter().map(|e| eval_expr_internal(ctx, state, e)).collect();
            let new_args = Arc::new(new_args?);

            match is_sequence_fn(&fun) {
                Some(seq_fn) => eval_seq(ctx, state, seq_fn, exp, &new_args),
                None => {
                    // Try to find the function's body
                    match ctx.fun_ssts.get(fun) {
                        Some(func) if func.x.axioms.spec_axioms.is_some() => {
                            let memoize = func.x.attrs.memoize;
                            match state.lookup_call(&fun, &new_args, memoize) {
                                Some(prev_result) => {
                                    state.cache_hits += 1;
                                    Ok(prev_result)
                                }
                                None => {
                                    let typ_params = &func.x.typ_params;
                                    let pars = &func.x.pars;
                                    let body =
                                        &func.x.axioms.spec_axioms.as_ref().unwrap().body_exp;
                                    state.cache_misses += 1;
                                    state.env.push_scope(true);
                                    for (formal, actual) in pars.iter().zip(new_args.iter()) {
                                        let formal_id = formal.x.name.clone();
                                        state.env.insert(formal_id, actual.clone()).unwrap();
                                    }
                                    // Account for const generics by adding, e.g., { N => 7 } to the environment
                                    for (formal, actual) in typ_params.iter().zip(typs.iter()) {
                                        if let TypX::ConstInt(c) = &**actual {
                                            let formal_id = VarIdent(
                                                formal.clone(),
                                                VarIdentDisambiguate::TypParamBare,
                                            );
                                            let value = SpannedTyped::new(
                                                &exp.span,
                                                &exp.typ,
                                                Const(Constant::Int(c.clone())),
                                            );
                                            state.env.insert(formal_id, value).unwrap();
                                        }
                                    }
                                    let result = eval_expr_internal(ctx, state, &body);
                                    state.env.pop_scope();
                                    state.insert_call(fun, &new_args, &result.clone()?, memoize);
                                    result
                                }
                            }
                        }
                        _ => {
                            // We don't have the body for this function, so we can't simplify further
                            exp_new(Call(
                                CallFun::Fun(fun.clone(), resolved_method.clone()),
                                typs.clone(),
                                new_args.clone(),
                            ))
                        }
                    }
                }
            }
        }
        Call(CallFun::Recursive(_), _, _) => ok,
        Call(fun @ CallFun::InternalFun(_), typs, args) => {
            let new_args: Result<Vec<Exp>, VirErr> =
                args.iter().map(|e| eval_expr_internal(ctx, state, e)).collect();
            let new_args = Arc::new(new_args?);
            exp_new(Call(fun.clone(), typs.clone(), new_args.clone()))
        }
        CallLambda(lambda, args) => {
            let lambda = eval_expr_internal(ctx, state, lambda)?;
            match &lambda.x {
                Interp(InterpExp::Closure(lambda, context)) => match &lambda.x {
                    Bind(bnd, body) => match &bnd.x {
                        BndX::Lambda(bnds, _trigs) => {
                            let new_args: Result<Vec<Exp>, VirErr> =
                                args.iter().map(|e| eval_expr_internal(ctx, state, e)).collect();
                            let new_args = Arc::new(new_args?);
                            state.env.push_scope(true);
                            // Process the original context first, so formal args take precedence
                            context.iter().for_each(|(k, v)| {
                                state.env.insert(k.clone(), v.clone()).unwrap();
                            });
                            state.env.push_scope(true);
                            for (formal, actual) in bnds.iter().zip(new_args.iter()) {
                                let formal_id = formal.name.clone();
                                state.env.insert(formal_id, actual.clone()).unwrap();
                            }
                            let e = eval_expr_internal(ctx, state, body);
                            state.env.pop_scope();
                            state.env.pop_scope();
                            e
                        }
                        _ => panic!(
                            "Expected CallLambda's binder to contain a lambda.  Instead found {:?}",
                            bnd
                        ),
                    },
                    _ => ok,
                },
                _ => ok,
            }
        }
        Bind(bnd, e) => match &bnd.x {
            BndX::Let(bnds) => {
                state.env.push_scope(true);
                for b in bnds.iter() {
                    let id = b.name.clone();
                    let val = eval_expr_internal(ctx, state, &b.a)?;
                    state.env.insert(id, val).unwrap();
                }
                let e = eval_expr_internal(ctx, state, e);
                state.env.pop_scope();
                e
            }
            BndX::Lambda(_, _) => {
                let mut env = HashMap::new();
                env.extend(state.env.map().iter().map(|(k, v)| (k.clone(), v.clone())));
                exp_new(Interp(InterpExp::Closure(exp.clone(), env)))
            }
            _ => ok,
        },
        Ctor(path, id, bnds) => {
            let new_bnds: Result<Vec<Binder<Exp>>, VirErr> = bnds
                .iter()
                .map(|b| {
                    let name = b.name.clone();
                    let a = eval_expr_internal(ctx, state, &b.a)?;
                    Ok(Arc::new(BinderX { name, a }))
                })
                .collect();
            let new_bnds = new_bnds?;
            exp_new(Ctor(path.clone(), id.clone(), Arc::new(new_bnds)))
        }
        ArrayLiteral(exprs) => {
            let new_exprs: Result<Vec<Exp>, VirErr> =
                exprs.iter().map(|e| eval_expr_internal(ctx, state, e)).collect();
            let im_vec: Vector<Exp> = new_exprs?.into_iter().collect();
            exp_new(Interp(InterpExp::Array(im_vec)))
        }
        Interp(e) => match e {
            InterpExp::FreeVar(_) => ok,
            InterpExp::Seq(_) => ok,
            InterpExp::Closure(_, _) => ok,
            InterpExp::Array(_) => ok,
        },
        // Ignored by the interpreter at present (i.e., treated as symbolic)
        VarAt(..) | VarLoc(..) | Loc(..) | Old(..) | WithTriggers(..) | StaticVar(..) => ok,
        ExecFnByName(_) => ok,
        FuelConst(_) => ok,
    };
    let res = r?;
    state.depth -= 1;
    state.log(format!("{}=> {:}", "\t".repeat(state.depth), res.x.to_user_string(&ctx.global)));
    if state.enable_simplified_cache {
        state.simplified.insert(&res);
    }
    Ok(res)
}

fn cleanup_seq(span: &Span, typ: Typ, v: &Vector<Exp>) -> Result<Exp, VirErr> {
    match &*typ {
        TypX::Datatype(_, typs, _) => {
            // Grab the type the sequence holds
            let inner_type = typs[0].clone();
            // Convert back to a standard SST representation
            let s = seq_to_sst(span, inner_type.clone(), v);
            // Wrap the seq construction in unbox to account for the Poly type of the sequence functions
            let unbox_opr = crate::ast::UnaryOpr::Unbox(typ.clone());
            let unboxed_expx = crate::sst::ExpX::UnaryOpr(unbox_opr, s);
            let unboxed_e = SpannedTyped::new(span, &typ.clone(), unboxed_expx);
            Ok(unboxed_e)
        }
        TypX::Boxed(t) => {
            match &**t {
                TypX::Datatype(_, typs, _) => {
                    // Grab the type the sequence holds
                    let inner_type = typs[0].clone();
                    // Convert back to a standard SST sequence representation
                    let s = seq_to_sst(span, inner_type.clone(), v);
                    Ok(s)
                }
                _ => Err(error(
                    &span,
                    format!(
                        "Internal error: Inside box, expected to find a sequence type but found: {:?}",
                        typ,
                    ),
                )),
            }
        }
        _ => Err(error(
            &span,
            format!("Internal error: Expected to find a sequence type but found: {:?}", typ),
        )),
    }
}

fn cleanup_array(span: &Span, typ: Typ, v: &Vector<Exp>) -> Result<Exp, VirErr> {
    let arr = array_to_sst(span, typ.clone(), v);
    // Wrap the construction in box to account for the Poly type of the sequence/array functions
    let box_opr = crate::ast::UnaryOpr::Box(typ.clone());
    let boxed_expx = crate::sst::ExpX::UnaryOpr(box_opr, arr);
    let boxed_e = SpannedTyped::new(span, &typ.clone(), boxed_expx);
    Ok(boxed_e)
}

/// Restore the free variables we hid during interpretation
/// and any sequence expressions we partially simplified during interpretation
fn cleanup_exp(exp: &Exp) -> Result<Exp, VirErr> {
    crate::sst_visitor::map_exp_visitor_result(exp, &mut |e| match &e.x {
        ExpX::Interp(InterpExp::FreeVar(v)) => {
            Ok(SpannedTyped::new(&e.span, &e.typ, ExpX::Var(v.clone())))
        }
        ExpX::Interp(InterpExp::Array(v)) => cleanup_array(&e.span, e.typ.clone(), v),
        ExpX::Interp(InterpExp::Seq(v)) => cleanup_seq(&e.span, e.typ.clone(), v),
        ExpX::Interp(InterpExp::Closure(..)) => Err(error(
            &e.span,
            "Proof by computation included a closure literal that wasn't applied.  This is not yet supported.",
        )),
        _ => Ok(e.clone()),
    })
}

enum SimplificationResult {
    /// Expression evaluated to true.
    True,
    /// Expression evaluated to false.
    /// If the optional argument is given, then it is equivalent
    /// to the original and also simplifies to 'false'.
    False(Option<Exp>),
    /// Expression evaluates to something that we can't simplify
    /// further via the interpreter.
    Complex(Exp),
}

/// Evaluate the result
///
/// Includes a special case when the top-level operation is a binary op.
/// For example, if the user tries to prove `a == b`, and it evaluates
/// to `7 == 5` which evaluates to false, we return
///     SimplificationResult::False(Some(`7 == 5`))
/// This lets the caller report a nicer error message
fn eval_expr_top(ctx: &Ctx, state: &mut State, exp: &Exp) -> Result<SimplificationResult, VirErr> {
    use BinaryOp::*;
    use ExpX::*;
    match &exp.x {
        Binary(op @ (Eq(_) | Ne | Inequality(_)), e1, e2) => {
            let e1 = eval_expr_internal(ctx, state, e1)?;
            let e2 = eval_expr_internal(ctx, state, e2)?;

            let simpl_exp = exp.new_x(Binary(*op, e1, e2));

            // This should only take one step to simplify the binary expression
            let final_exp = eval_expr_internal(ctx, state, &simpl_exp)?;

            if let ExpX::Const(Constant::Bool(b)) = final_exp.x {
                if b {
                    Ok(SimplificationResult::True)
                } else {
                    Ok(SimplificationResult::False(Some(simpl_exp)))
                }
            } else {
                Ok(SimplificationResult::Complex(final_exp))
            }
        }
        _ => {
            let final_exp = eval_expr_internal(ctx, state, exp)?;
            if let ExpX::Const(Constant::Bool(b)) = final_exp.x {
                if b {
                    Ok(SimplificationResult::True)
                } else {
                    Ok(SimplificationResult::False(None))
                }
            } else {
                Ok(SimplificationResult::Complex(final_exp))
            }
        }
    }
}

/// We run the interpreter on a separate thread, so that we can give it a larger-than-default stack
fn eval_expr_launch(
    global: &GlobalCtx,
    exp: Exp,
    fun_ssts: &HashMap<Fun, FunctionSst>,
    rlimit: f32,
    arch: ArchWordBits,
    mode: ComputeMode,
    log: &mut Option<File>,
) -> Result<(Exp, Vec<Message>), VirErr> {
    let env = ScopeMap::new();
    let cache = HashMap::new();
    let logging = log.is_some();
    let msgs = Vec::new();
    let mut state = State {
        depth: 0,
        env,
        iterations: 1,
        msgs,
        log: log.take(),
        perf: logging,
        cache,
        enable_cache: true,
        cache_hits: 0,
        cache_misses: 0,
        simplified: PtrSet::new(),
        enable_simplified_cache: false,
        ptr_hits: 0,
        ptr_misses: 0,
        fun_calls: HashMap::new(),
    };
    // Don't run for too long
    let max_iterations = (rlimit as f64 * RLIMIT_MULTIPLIER as f64) as u64;
    let ctx = Ctx { fun_ssts: &fun_ssts, max_iterations, arch, global };
    let result = eval_expr_top(&ctx, &mut state, &exp)?;
    display_perf_stats(&state);
    if state.log.is_some() {
        log.replace(state.log.unwrap());
    }

    match result {
        SimplificationResult::True => {
            return Ok((crate::sst_util::sst_bool(&exp.span, true), state.msgs));
        }
        SimplificationResult::False(None) => {
            return Err(error(&exp.span, "expression simplifies to false"));
        }
        SimplificationResult::False(Some(small_exp)) => {
            let small_exp = cleanup_exp(&small_exp)?;
            return Err(error(
                &exp.span,
                format!(
                    "expression simplifies to `{}`, which evaluates to false",
                    small_exp.x.to_user_string(&ctx.global)
                ),
            ));
        }
        SimplificationResult::Complex(res) => match mode {
            ComputeMode::Z3 => {
                let res = cleanup_exp(&res)?;
                // Send partial result to Z3
                if exp.definitely_eq(&res) {
                    let msg = format!(
                        "Failed to simplify expression <<{}>> before sending to Z3",
                        exp.x.to_user_string(&ctx.global)
                    );
                    state.msgs.push(warning(&exp.span, msg));
                }
                Ok((res, state.msgs))
            }
            ComputeMode::ComputeOnly => {
                // Proof must succeed purely through computation
                let res = cleanup_exp(&res)?;
                Err(error(
                    &exp.span,
                    &format!(
                        "assert_by_compute_only failed to simplify down to true.  Instead got: {}.",
                        res.x.to_user_string(&ctx.global)
                    )
                    .to_string(),
                ))
            }
        },
    }
}

/// Symbolically evaluate an expression, simplifying it as much as possible
pub fn eval_expr(
    global: &GlobalCtx,
    exp: &Exp,
    diagnostics: &(impl air::messages::Diagnostics + ?Sized),
    fun_ssts: SstMap,
    rlimit: f32,
    arch: ArchWordBits,
    mode: ComputeMode,
    log: &mut Option<File>,
) -> Result<Exp, VirErr> {
    // Make a new global so we can move it into the new thread
    let global = global.from_self_with_log(global.interpreter_log.clone());

    let builder =
        thread::Builder::new().name("interpreter".to_string()).stack_size(1024 * 1024 * 1024); // 1 GB
    let mut taken_log = log.take();
    let (taken_log, res) = {
        let handler = {
            // Create local versions that we own and hence can pass to the closure
            let exp = exp.clone();
            builder
                .spawn(move || {
                    let res = eval_expr_launch(
                        &global,
                        exp,
                        &*fun_ssts,
                        rlimit,
                        arch,
                        mode,
                        &mut taken_log,
                    );
                    (taken_log, res)
                })
                .unwrap()
        };
        handler.join().unwrap()
    };
    *log = taken_log;
    let (e, msgs) = res?;
    msgs.iter().for_each(|m| diagnostics.report(&m.clone().to_any()));
    Ok(e)
}
