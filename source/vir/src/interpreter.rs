//! A Symbolic Interpreter for VIR
//!
//! Operates on VIR's SST representation
//!
//! Current target is supporting proof by computation
//! https://github.com/secure-foundations/verus/discussions/120

use crate::ast::{
    ArithOp, BinaryOp, BitwiseOp, ComputeMode, Constant, Fun, FunX, Idents, InequalityOp, IntRange,
    PathX, SpannedTyped, Typ, TypX, UnaryOp, VirErr,
};
use crate::ast_util::{err_str, path_as_rust_name};
use crate::func_to_air::{SstInfo, SstMap};
use crate::sst::{Bnd, BndX, Exp, ExpX, Exps, Trigs, UniqueIdent};
use air::ast::{Binder, BinderX, Binders, Span};
use air::messages::{warning, Diagnostics, Message};
use air::scope_map::ScopeMap;
use im::Vector;
use num_bigint::{BigInt, Sign};
use num_traits::identities::Zero;
use num_traits::{FromPrimitive, One, Signed, ToPrimitive};
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
    fun_ssts: &'a HashMap<Fun, SstInfo>,
    /// We avoid infinite loops by running for a fixed number of intervals
    max_iterations: u64,
    /// Number of bits we assume the underlying architecture supports
    arch_size_min_bits: u32,
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
        match (self.as_ref(), other.as_ref()) {
            (Bool, Bool) => Some(true),
            (Int(l), Int(r)) => Some(l == r),
            (Tuple(typs_l), Tuple(typs_r)) => typs_l.syntactic_eq(typs_r),
            (Lambda(formals_l, res_l), Lambda(formals_r, res_r)) => {
                Some(formals_l.syntactic_eq(formals_r)? && res_l.syntactic_eq(res_r)?)
            }
            (Datatype(path_l, typs_l), Datatype(path_r, typs_r)) => {
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
            (Call(f_l, _, exps_l), Call(f_r, _, exps_r)) => {
                if f_l == f_r && exps_l.len() == exps_r.len() {
                    def_eq(exps_l.syntactic_eq(exps_r)?)
                } else {
                    // We don't know if a function call on symbolic values
                    // will return the same or different values
                    None
                }
            }
            (CallLambda(typ_l, exp_l, exps_l), CallLambda(typ_r, exp_r, exps_r)) => Some(
                typ_l.syntactic_eq(typ_r)?
                    && exp_l.syntactic_eq(exp_r)?
                    && exps_l.syntactic_eq(exps_r)?,
            ),

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

fn hash_binders_typ<H: Hasher>(state: &mut H, bnds: &Binders<Typ>) {
    hash_iter(state, bnds.iter().map(|b| (&b.name, &b.a)), |st, v| v.hash(st))
}

fn hash_binders_exp<H: Hasher>(state: &mut H, bnds: &Binders<Exp>) {
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
        Let(bnds) => dohash!(0; hash_binders_exp(bnds)),
        Quant(quant, bnds, trigs) => dohash!(1, quant; hash_binders_typ(bnds), hash_trigs(trigs)),
        Lambda(bnds, trigs) => dohash!(2; hash_binders_typ(bnds), hash_trigs(trigs)),
        Choose(bnds, trigs, e) => dohash!(3;
                    hash_binders_typ(bnds), hash_trigs(trigs), hash_exp(e)),
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
        CallLambda(typ, lambda, args) => {
            dohash!(7, typ; hash_exp(lambda));
            hash_iter(state, args.iter().enumerate(), hash_exp);
        }
        Ctor(path, id, bnds) => dohash!(8, path, id; hash_binders_exp(bnds)),
        Unary(op, e) => dohash!(9, op; hash_exp(e)),
        UnaryOpr(op, e) => dohash!(10, op; hash_exp(e)),
        Binary(op, e1, e2) => dohash!(11, op; hash_exp(e1), hash_exp(e2)),
        If(e1, e2, e3) => dohash!(12; hash_exp(e1), hash_exp(e2), hash_exp(e3)),
        WithTriggers(trigs, e) => dohash!(13; hash_trigs(trigs), hash_exp(e)),
        Bind(bnd, e) => dohash!(14; hash_bnd(bnd), hash_exp(e)),
        Interp(e) => {
            dohash!(15);
            match e {
                InterpExp::FreeVar(id) => dohash!(0, id),
                InterpExp::Seq(exps) => dohash!(1; hash_exps_vector(exps)),
                InterpExp::Closure(e, _ctx) => dohash!(2; hash_exp(e)),
            }
        }
    }
}

/**********************
 * Utility functions  *
 **********************/

// Based on Dafny's C# implementation:
// https://github.com/dafny-lang/dafny/blob/08744a797296897f4efd486083579e484f57b9dc/Source/DafnyRuntime/DafnyRuntime.cs#L1383
/// Proper Euclidean division on BigInt
fn euclidean_div(i1: &BigInt, i2: &BigInt) -> BigInt {
    // Note: Can be replaced with an inbuilt method on BigInts once
    // https://github.com/rust-num/num-bigint/pull/245 is merged.
    use Sign::*;
    match (i1.sign(), i2.sign()) {
        (Plus | NoSign, Plus | NoSign) => i1 / i2,
        (Plus | NoSign, Minus) => -(i1 / (-i2)),
        (Minus, Plus | NoSign) => -(((-i1) - BigInt::one()) / i2) - BigInt::one(),
        (Minus, Minus) => (((-i1) - BigInt::one()) / (-i2)) + 1,
    }
}

// Based on Dafny's C# implementation:
// https://github.com/dafny-lang/dafny/blob/08744a797296897f4efd486083579e484f57b9dc/Source/DafnyRuntime/DafnyRuntime.cs#L1436
/// Proper Euclidean mod on BigInt
fn euclidean_mod(i1: &BigInt, i2: &BigInt) -> BigInt {
    // Note: Can be replaced with an inbuilt method on BigInts once
    // https://github.com/rust-num/num-bigint/pull/245 is merged.
    use Sign::*;
    match i1.sign() {
        Plus | NoSign => i1 % i2.abs(),
        Minus => {
            let c = (-i1) % i2.abs();
            if c.is_zero() { BigInt::zero() } else { i2.abs() - c }
        }
    }
}

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

enum SeqFn {
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

// TODO: Make the matching here more robust to changes in pervasive
/// Identify sequence functions for which we provide custom interpretation
fn is_sequence_fn(fun: &Fun) -> Option<SeqFn> {
    use SeqFn::*;
    match path_as_rust_name(&fun.path).as_str() {
        "crate::pervasive::seq::Seq::empty" => Some(Empty),
        "crate::pervasive::seq::Seq::new" => Some(New),
        "crate::pervasive::seq::Seq::push" => Some(Push),
        "crate::pervasive::seq::Seq::update" => Some(Update),
        "crate::pervasive::seq::Seq::subrange" => Some(Subrange),
        "crate::pervasive::seq::Seq::add" => Some(Add),
        "crate::pervasive::seq::Seq::len" => Some(Len),
        "crate::pervasive::seq::Seq::index" => Some(Index),
        "crate::pervasive::seq::Seq::ext_equal" => Some(ExtEqual),
        "crate::pervasive::seq::Seq::last" => Some(Last),
        _ => None,
    }
}

fn strs_to_idents(s: Vec<&str>) -> Idents {
    let idents = s.iter().map(|s| Arc::new(s.to_string())).collect();
    Arc::new(idents)
}

/// Convert an interpreter-internal sequence representation back into a
/// representation we can pass to AIR
// TODO: More robust way of pointing to pervasive's sequence functions
fn seq_to_sst(span: &Span, typ: Typ, s: &Vector<Exp>) -> Exp {
    let exp_new = |e: ExpX| SpannedTyped::new(span, &typ, e);
    let typs = Arc::new(vec![typ.clone()]);
    let path_empty = Arc::new(PathX {
        krate: None,
        segments: strs_to_idents(vec!["pervasive", "seq", "Seq", "empty"]),
    });
    let path_push = Arc::new(PathX {
        krate: None,
        segments: strs_to_idents(vec!["pervasive", "seq", "Seq", "push"]),
    });
    let fun_empty = Arc::new(FunX { path: path_empty, trait_path: None });
    let fun_push = Arc::new(FunX { path: path_push, trait_path: None });
    let empty = exp_new(ExpX::Call(fun_empty, typs.clone(), Arc::new(vec![])));
    let seq = s.iter().fold(empty, |acc, e| {
        let args = Arc::new(vec![acc, e.clone()]);
        exp_new(ExpX::Call(fun_push.clone(), typs.clone(), args))
    });
    seq
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
                                    let call = exp_new(CallLambda(
                                        lambda.typ.clone(),
                                        lambda.clone(),
                                        args,
                                    ));
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
                                    state.msgs.push(warning(msg, &exp.span));
                                    ok_seq(&args[0], &s, &args[1..])
                                }
                                Some(index) => {
                                    if index < s.len() {
                                        Ok(s[index].clone())
                                    } else {
                                        let msg = "Computation tried to index past the length of a sequence";
                                        state.msgs.push(warning(msg, &exp.span));
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
        _ => panic!("Expected sequence expression to be a Call.  Got {:} instead.", exp),
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
        return err_str(&exp.span, "assert_by_compute timed out");
    }
    state.log(format!("{}Evaluating {:}", "\t".repeat(state.depth), exp));
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
                        BitNot
                        | Clip { .. }
                        | Trigger(_)
                        | CoerceMode { .. }
                        | StrLen
                        | StrIsAscii
                        | CharToInt => ok,
                        MustBeFinalized => {
                            panic!("Found MustBeFinalized op {:?} after calling finalize_exp", exp)
                        }
                    }
                }
                Const(Int(i)) => {
                    // Explicitly enumerate UnaryOps, in case more are added
                    match op {
                        BitNot => {
                            use IntRange::*;
                            let r = match *e.typ {
                                TypX::Int(U(n)) => {
                                    let i = i.to_u128().unwrap();
                                    u128_to_fixed_width(!i, n)
                                }
                                TypX::Int(I(n)) => {
                                    let i = i.to_i128().unwrap();
                                    i128_to_fixed_width(!i, n)
                                }
                                TypX::Int(USize) => {
                                    let i = i.to_u128().unwrap();
                                    u128_to_fixed_width(!i, ctx.arch_size_min_bits)
                                }
                                TypX::Int(ISize) => {
                                    let i = i.to_i128().unwrap();
                                    i128_to_fixed_width(!i, ctx.arch_size_min_bits)
                                }

                                _ => panic!(
                                    "Type checker should not allow bitwise ops on non-fixed-width types"
                                ),
                            };
                            int_new(r)
                        }
                        Clip { range, truncate: _ } => {
                            let mut apply_range = |lower: BigInt, upper: BigInt| {
                                if i < &lower || i > &upper {
                                    let msg =
                                        "Computation clipped an integer that was out of range";
                                    state.msgs.push(warning(msg, &exp.span));
                                    ok.clone()
                                } else {
                                    Ok(e.clone())
                                }
                            };
                            match range {
                                IntRange::Int => ok,
                                IntRange::Nat => apply_range(BigInt::zero(), i.clone()),
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
                                    let u = apply_range(
                                        BigInt::zero(),
                                        (BigInt::one() << ctx.arch_size_min_bits) - BigInt::one(),
                                    );
                                    u
                                }
                                IntRange::ISize => apply_range(
                                    -1 * (BigInt::one() << (ctx.arch_size_min_bits - 1)),
                                    (BigInt::one() << (ctx.arch_size_min_bits - 1)) - BigInt::one(),
                                ),
                            }
                        }
                        MustBeFinalized => {
                            panic!("Found MustBeFinalized op {:?} after calling finalize_exp", exp)
                        }
                        Not | Trigger(_) | CoerceMode { .. } | StrLen | StrIsAscii | CharToInt => {
                            ok
                        }
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
                    _ => ok,
                },
                Unbox(_) => match &e.x {
                    UnaryOpr(Box(_), inner_e) => Ok(inner_e.clone()),
                    // Sequences move through unbox
                    Interp(InterpExp::Seq(s)) => exp_new(Interp(InterpExp::Seq(s.clone()))),
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
                                        int_new(euclidean_div(i1, i2))
                                    }
                                }
                                EuclideanMod => {
                                    if i2.is_zero() {
                                        ok_e2(e2) // Treat as symbolic instead of erroring
                                    } else {
                                        int_new(euclidean_mod(i1, i2))
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
                Bitwise(op) => {
                    use BitwiseOp::*;
                    let e2 = eval_expr_internal(ctx, state, e2)?;
                    match (&e1.x, &e2.x) {
                        // Ideal case where both sides are concrete
                        (Const(Int(i1)), Const(Int(i2))) => match op {
                            BitXor => int_new(i1 ^ i2),
                            BitAnd => int_new(i1 & i2),
                            BitOr => int_new(i1 | i2),
                            Shr | Shl => match i2.to_u128() {
                                None => ok_e2(e2),
                                Some(shift) => {
                                    use IntRange::*;
                                    let r = match *exp.typ {
                                        TypX::Int(U(n)) => {
                                            let i1 = i1.to_u128().unwrap();
                                            let res = if matches!(op, Shr) {
                                                i1 >> shift
                                            } else {
                                                i1 << shift
                                            };
                                            u128_to_fixed_width(res, n)
                                        }
                                        TypX::Int(I(n)) => {
                                            let i1 = i1.to_i128().unwrap();
                                            let res = if matches!(op, Shr) {
                                                i1 >> shift
                                            } else {
                                                i1 << shift
                                            };
                                            i128_to_fixed_width(res, n)
                                        }
                                        TypX::Int(USize) => {
                                            let i1 = i1.to_u128().unwrap();
                                            let res = if matches!(op, Shr) {
                                                i1 >> shift
                                            } else {
                                                i1 << shift
                                            };
                                            u128_to_fixed_width(res, ctx.arch_size_min_bits)
                                        }
                                        TypX::Int(ISize) => {
                                            let i1 = i1.to_i128().unwrap();
                                            let res = if matches!(op, Shr) {
                                                i1 >> shift
                                            } else {
                                                i1 << shift
                                            };
                                            i128_to_fixed_width(res, ctx.arch_size_min_bits)
                                        }
                                        _ => panic!(
                                            "Type checker should not allow bitwise ops on non-fixed-width types"
                                        ),
                                    };
                                    int_new(r)
                                }
                            },
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
                StrGetChar => ok_e2(e2.clone()),
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
                _ => exp_new(If(e1, e2.clone(), e3.clone())),
            }
        }
        Call(fun, typs, args) => {
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
                        None => {
                            // We don't have the body for this function, so we can't simplify further
                            exp_new(Call(fun.clone(), typs.clone(), new_args.clone()))
                        }
                        Some(SstInfo { params, body, memoize, .. }) => {
                            match state.lookup_call(&fun, &new_args, *memoize) {
                                Some(prev_result) => {
                                    state.cache_hits += 1;
                                    Ok(prev_result)
                                }
                                None => {
                                    state.cache_misses += 1;
                                    state.env.push_scope(true);
                                    for (formal, actual) in params.iter().zip(new_args.iter()) {
                                        let formal_id = UniqueIdent {
                                            name: formal.x.name.clone(),
                                            local: Some(0),
                                        };
                                        state.env.insert(formal_id, actual.clone()).unwrap();
                                    }
                                    let result = eval_expr_internal(ctx, state, &body);
                                    state.env.pop_scope();
                                    state.insert_call(fun, &new_args, &result.clone()?, *memoize);
                                    result
                                }
                            }
                        }
                    }
                }
            }
        }
        CallLambda(_typ, lambda, args) => {
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
                                let formal_id =
                                    UniqueIdent { name: formal.name.clone(), local: None };
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
                    let id = UniqueIdent { name: b.name.clone(), local: None };
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
        Interp(e) => match e {
            InterpExp::FreeVar(_) => ok,
            InterpExp::Seq(_) => ok,
            InterpExp::Closure(_, _) => ok,
        },
        // Ignored by the interpreter at present (i.e., treated as symbolic)
        VarAt(..) | VarLoc(..) | Loc(..) | Old(..) | WithTriggers(..) => ok,
    };
    let res = r?;
    state.depth -= 1;
    state.log(format!("{}=> {:}", "\t".repeat(state.depth), &res));
    if state.enable_simplified_cache {
        state.simplified.insert(&res);
    }
    Ok(res)
}

/// We run the interpreter on a separate thread, so that we can give it a larger-than-default stack
fn eval_expr_launch(
    exp: Exp,
    fun_ssts: &HashMap<Fun, SstInfo>,
    rlimit: u32,
    arch_size_min_bits: u32,
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
    let max_iterations =
        if rlimit == 0 { std::u64::MAX } else { rlimit as u64 * RLIMIT_MULTIPLIER };
    let ctx = Ctx { fun_ssts: &fun_ssts, max_iterations, arch_size_min_bits };
    let res = eval_expr_internal(&ctx, &mut state, &exp)?;
    display_perf_stats(&state);
    if state.log.is_some() {
        log.replace(state.log.unwrap());
    }
    if let ExpX::Const(Constant::Bool(false)) = res.x {
        err_str(&exp.span, "assert simplifies to false")
    } else {
        match mode {
            // Send partial result to Z3
            ComputeMode::Z3 => {
                // Restore the free variables we hid during interpretation
                let res = crate::sst_visitor::map_exp_visitor_result(&res, &mut |e| match &e.x {
                    ExpX::Interp(InterpExp::FreeVar(v)) => {
                        Ok(SpannedTyped::new(&e.span, &e.typ, ExpX::Var(v.clone())))
                    }
                    ExpX::Interp(InterpExp::Closure(..)) => err_str(
                        &e.span,
                        "Proof by computation included a closure literal that wasn't applied.  This is not yet supported.",
                    ),
                    _ => Ok(e.clone()),
                })?;
                if exp.definitely_eq(&res) {
                    let msg =
                        format!("Failed to simplify expression <<{}>> before sending to Z3", exp);
                    state.msgs.push(warning(msg, &exp.span));
                }
                Ok((res, state.msgs))
            }
            // Proof must succeed purely through computation
            ComputeMode::ComputeOnly => match res.x {
                ExpX::Const(Constant::Bool(true)) => Ok((res, state.msgs)),
                _ => err_str(
                    &exp.span,
                    &format!(
                        "assert_by_compute_only failed to simplify down to true.  Instead got: {}.",
                        res
                    )
                    .to_string(),
                ),
            },
        }
    }
}

/// Symbolically evaluate an expression, simplifying it as much as possible
pub fn eval_expr(
    exp: &Exp,
    diagnostics: &(impl Diagnostics + ?Sized),
    fun_ssts: &mut SstMap,
    rlimit: u32,
    arch_size_min_bits: u32,
    mode: ComputeMode,
    log: &mut Option<File>,
) -> Result<Exp, VirErr> {
    let builder =
        thread::Builder::new().name("interpreter".to_string()).stack_size(1024 * 1024 * 1024); // 1 GB
    let mut taken_log = log.take();
    let (taken_log, res) = fun_ssts.update(|fun_ssts| {
        let handler = {
            // Create local versions that we own and hence can pass to the closure
            let exp = exp.clone();
            builder
                .spawn(move || {
                    let res = eval_expr_launch(
                        exp,
                        &fun_ssts,
                        rlimit,
                        arch_size_min_bits,
                        mode,
                        &mut taken_log,
                    );
                    (fun_ssts, (taken_log, res))
                })
                .unwrap()
        };
        handler.join().unwrap()
    });
    *log = taken_log;
    let (e, msgs) = res?;
    msgs.iter().for_each(|m| diagnostics.report(m));
    Ok(e)
}
