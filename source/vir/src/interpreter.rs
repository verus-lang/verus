//! A Symbolic Interpreter for VIR
//!
//! Operates on VIR's SST representation
//!
//! Current target is supporting proof by computation
//! https://github.com/secure-foundations/verus/discussions/120

use crate::ast::{
    ArithOp, BinaryOp, BitwiseOp, ComputeMode, Constant, Fun, InequalityOp, IntRange, SpannedTyped,
    Typ, TypX, UnaryOp, VirErr,
};
use crate::ast_util::{err_str, path_as_rust_name};
use crate::def::{SstMap, ARCH_SIZE_MIN_BITS};
use crate::sst::{Bnd, BndX, Exp, ExpX, Exps, Trigs, UniqueIdent};
use air::ast::{Binder, BinderX, Binders};
use air::scope_map::ScopeMap;
use im::Vector;
use num_bigint::{BigInt, Sign};
use num_traits::identities::Zero;
use num_traits::{FromPrimitive, One, Signed, ToPrimitive};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::time::{Duration, Instant};

// TODO: Potential optimizations:
//  - Swap to CPS with enforced tail-call optimization to avoid exhausting the stack
//    - See crates musttail and with_locals

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

struct State {
    depth: usize,
    env: Env,
    debug: bool,
    cache: HashMap<Fun, HashMap<ExpsKey, Exp>>,
    cache_hits: u64,
    cache_misses: u64,
    fun_calls: HashMap<Fun, u64>,
    simplified: PtrSet<SpannedTyped<ExpX>>,
}

// Define the function-call cache's API
impl State {
    fn insert_call(&mut self, f: &Fun, args: &Exps, result: &Exp) {
        self.cache.entry(f.clone()).or_default().insert(args.into(), result.clone());
    }

    fn lookup_call(&self, f: &Fun, args: &Exps) -> Option<Exp> {
        self.cache.get(f)?.get(&args.into()).cloned()
    }
}

struct Ctx<'a> {
    fun_ssts: &'a SstMap,
    time_start: Instant,
    time_limit: Duration,
}

/// Interpreter-internal expressions
#[derive(Debug)]
pub enum InterpExp {
    FreeVar(UniqueIdent),
    Seq(Vector<Exp>),
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
        self.iter().zip(other.iter()).try_fold(true, |acc, (l, r)| Some(acc && l.syntactic_eq(r)?))
    }
}

impl<T: Clone + SyntacticEquality> SyntacticEquality for Vector<T> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        self.iter().zip(other.iter()).try_fold(true, |acc, (l, r)| Some(acc && l.syntactic_eq(r)?))
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
            (Lambda(bnds_l), Lambda(bnds_r)) => bnds_l.conservative_eq(bnds_r),
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
            (Const(l), Const(r)) => Some(l == r),
            (Var(l), Var(r)) => def_eq(l == r),
            (VarLoc(l), VarLoc(r)) => def_eq(l == r),
            (VarAt(l, at_l), VarAt(r, at_r)) => def_eq(l == r && at_l == at_r),
            (Loc(l), Loc(r)) => l.syntactic_eq(r),
            (Old(id_l, unique_id_l), Old(id_r, unique_id_r)) => {
                def_eq(id_l == id_r && unique_id_l == unique_id_r)
            }
            (Call(f_l, _, exps_l), Call(f_r, _, exps_r)) => {
                if f_l == f_r && exps_l.len() == exps_r.len() {
                    exps_l.syntactic_eq(exps_r)
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
                    (Box(l), Box(r)) => def_eq(l.syntactic_eq(r)?),
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
        Lambda(bnds) => dohash!(2; hash_binders_typ(bnds)),
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
        (Minus, Plus | NoSign) => -(-i1 - BigInt::one() / i2) - BigInt::one(),
        (Minus, Minus) => ((-i1 - BigInt::one()) / (-i2)) + 1,
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
    let sum = state.cache_hits + state.cache_misses;
    let hit_perc = 100.0 * (state.cache_hits as f64 / sum as f64);
    println!("Call result cache had {} hits out of {} ({}%)", state.cache_hits, sum, hit_perc);
    let mut cache_stats: Vec<(&Fun, usize)> =
        state.cache.iter().map(|(fun, vec)| (fun, vec.len())).collect();
    cache_stats.sort_by(|a, b| b.1.cmp(&a.1));
    for (fun, calls) in &cache_stats {
        println!("{:?} cached {} distinct invocations", fun.path, calls);
    }
    println!("\nRaw call numbers:");
    let mut fun_call_stats: Vec<(&Fun, _)> = state.fun_calls.iter().collect();
    fun_call_stats.sort_by(|a, b| b.1.cmp(&a.1));
    for (fun, count) in fun_call_stats {
        println!("{:?} called {} times", fun.path, count);
    }
}

/***********************************************
 * Special handling for interpreting sequences *
 ***********************************************/

// TODO: Have this return an Option<Enum> to indicate which function it found
fn is_sequence_fn(fun: &Fun) -> bool {
    matches!(
        path_as_rust_name(&fun.path).as_str(),
        "crate::pervasive::seq::Seq::len"
            | "crate::pervasive::seq::Seq::index"
            | "crate::pervasive::seq::Seq::ext_equal"
            | "crate::pervasive::seq::Seq::last"
            | "crate::pervasive::seq::Seq::empty"
            | "crate::pervasive::seq::Seq::new"
            | "crate::pervasive::seq::Seq::push"
            | "crate::pervasive::seq::Seq::update"
            | "crate::pervasive::seq::Seq::subrange"
            | "crate::pervasive::seq::Seq::add"
    )
}

fn eval_seq(ctx: &Ctx, state: &mut State, exp: &Exp, args: &Exps) -> Result<Exp, VirErr> {
    use ExpX::*;
    use InterpExp::*;
    match &exp.x {
        Call(fun, typs, _old_args) => {
            let exp_new = |e: ExpX| SpannedTyped::new(&exp.span, &exp.typ, e);
            let bool_new = |b: bool| Ok(exp_new(Const(Constant::Bool(b))));
            let int_new = |i: BigInt| Ok(exp_new(Const(Constant::Int(i))));
            let seq_new = |v| Ok(exp_new(Interp(Seq(v))));
            let ok = Ok(exp.clone());
            let get_int = |e: &Exp| match &e.x {
                UnaryOpr(crate::ast::UnaryOpr::Box(_), e) => match &e.x {
                    Const(Constant::Int(index)) => Some(BigInt::to_usize(index).unwrap()),
                    _ => None,
                },
                _ => None,
            };

            match path_as_rust_name(&fun.path).as_str() {
                "crate::pervasive::seq::Seq::empty" => seq_new(Vector::new()),
                "crate::pervasive::seq::Seq::new" => {
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
                                    // TODO: What's the right typ to pass here?
                                    let call =
                                        exp_new(CallLambda(typs[0].clone(), lambda.clone(), args));
                                    eval_expr_internal(ctx, state, &call)
                                })
                                .collect();
                            let im_vec: Vector<Exp> = vec?.into_iter().collect();
                            seq_new(im_vec)
                        }
                        _ => ok,
                    }
                }
                "crate::pervasive::seq::Seq::push" => match &args[0].x {
                    Interp(Seq(s)) => {
                        let mut s = s.clone();
                        s.push_back(args[1].clone());
                        seq_new(s)
                    }
                    _ => ok,
                },
                "crate::pervasive::seq::Seq::update" => match &args[0].x {
                    Interp(Seq(s)) => match get_int(&args[1]) {
                        Some(index) if index < s.len() => {
                            let s = s.update(index, args[2].clone());
                            seq_new(s)
                        }
                        _ => ok,
                    },
                    _ => ok,
                },
                "crate::pervasive::seq::Seq::subrange" => match &args[0].x {
                    Interp(Seq(s)) => {
                        let start = get_int(&args[1]);
                        let end = get_int(&args[2]);
                        match (start, end) {
                            (Some(start), Some(end)) if start <= end && end <= s.len() => {
                                seq_new(s.clone().slice(start..end))
                            }
                            _ => ok,
                        }
                    }
                    _ => ok,
                },
                "crate::pervasive::seq::Seq::add" => match (&args[0].x, &args[1].x) {
                    (Interp(Seq(s1)), Interp(Seq(s2))) => {
                        let mut s = s1.clone();
                        s.append(s2.clone());
                        seq_new(s)
                    }
                    _ => ok,
                },
                "crate::pervasive::seq::Seq::len" => match &args[0].x {
                    Interp(Seq(s)) => int_new(BigInt::from_usize(s.len()).unwrap()),
                    _ => ok,
                },
                "crate::pervasive::seq::Seq::index" => match &args[0].x {
                    Interp(Seq(s)) => match &args[1].x {
                        UnaryOpr(crate::ast::UnaryOpr::Box(_), e) => match &e.x {
                            Const(Constant::Int(index)) => {
                                let index = BigInt::to_usize(index).unwrap();
                                if index < s.len() { Ok(s[index].clone()) } else { ok }
                            }
                            _ => ok,
                        },
                        _ => ok,
                    },
                    _ => ok,
                },
                "crate::pervasive::seq::Seq::ext_equal" => match (&args[0].x, &args[1].x) {
                    (Interp(Seq(l)), Interp(Seq(r))) => {
                        let eq = l
                            .iter()
                            .zip(r.iter())
                            .fold(Some(true), |b, (l, r)| Some(b? && l.syntactic_eq(r)?));
                        match eq {
                            None => ok,
                            Some(b) => bool_new(b),
                        }
                    }
                    _ => ok,
                },
                "crate::pervasive::seq::Seq::last" => match &args[0].x {
                    Interp(Seq(s)) => {
                        if s.len() > 0 {
                            Ok(s.last().unwrap().clone())
                        } else {
                            ok
                        }
                    }
                    _ => ok,
                },
                _ => {
                    println!("***Failed to match {} ***", path_as_rust_name(&fun.path));
                    ok
                }
            }
        }
        //        UnaryOpr(crate::ast::UnaryOpr::Box(_), e) => eval_seq_producing(ctx, state, e),
        //        UnaryOpr(crate::ast::UnaryOpr::Unbox(_), e) => eval_seq_producing(ctx, state, e),
        _ => panic!("Expected sequence expression to be a Call.  Got {:} instead.", exp),
    }
}

/********************
 * Core interpreter *
 ********************/

/// Symbolically execute the expression as far as we can,
/// stopping when we hit a symbolic control-flow decision
fn eval_expr_internal(ctx: &Ctx, state: &mut State, exp: &Exp) -> Result<Exp, VirErr> {
    if ctx.time_start.elapsed() > ctx.time_limit {
        display_perf_stats(state);
        return err_str(&exp.span, "assert_by_compute timed out");
    }
    if state.debug {
        println!("{}Evaluating {:}", "\t".repeat(state.depth), exp);
    }
    let ok = Ok(exp.clone());
    if state.simplified.contains(exp) {
        if state.debug {
            println!("{}=> already simplified as far as it will go", "\t".repeat(state.depth));
        }
        // We've already simplified this expression as much as we can
        return Ok(exp.clone());
    }
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
                if state.debug {
                    println!("Failed to find a match for {:?}", id);
                };
                // "Hide" the variable, so that we don't accidentally
                // mix free and bound variables while interpreting
                exp_new(Interp(InterpExp::FreeVar(id.clone())))
            }
            Some(e) => {
                if state.debug {
                    //println!("Found match for {:?}", id);
                };
                Ok(e.clone())
            }
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
                        BitNot | Clip(_) | Trigger(_) => ok,
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
                                    u128_to_fixed_width(!i, ARCH_SIZE_MIN_BITS)
                                }
                                TypX::Int(ISize) => {
                                    let i = i.to_i128().unwrap();
                                    i128_to_fixed_width(!i, ARCH_SIZE_MIN_BITS)
                                }

                                _ => panic!(
                                    "Type checker should not allow bitwise ops on non-fixed-width types"
                                ),
                            };
                            int_new(r)
                        }
                        Clip(range) => {
                            let apply_range = |lower: BigInt, upper: BigInt| {
                                if i < &lower || i > &upper { ok.clone() } else { Ok(e.clone()) }
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
                                        (BigInt::one() << ARCH_SIZE_MIN_BITS) - BigInt::one(),
                                    );
                                    u
                                }
                                IntRange::ISize => apply_range(
                                    -1 * (BigInt::one() << (ARCH_SIZE_MIN_BITS - 1)),
                                    (BigInt::one() << (ARCH_SIZE_MIN_BITS - 1)) - BigInt::one(),
                                ),
                            }
                        }
                        Not | Trigger(_) => ok,
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
                    UnaryOpr(Box(_), inner_e) => {
                        if state.debug {
                            //println!("Unbox found matching box");
                        };
                        Ok(inner_e.clone())
                    }
                    // Sequences move through unbox
                    Interp(InterpExp::Seq(s)) => exp_new(Interp(InterpExp::Seq(s.clone()))),
                    _ => ok,
                },
                HasType(_) => ok,
                IsVariant { datatype, variant } => match &e.x {
                    Ctor(dt, var, _) => {
                        if state.debug {
                            //println!("IsVariant found matching Ctor!");
                        };
                        bool_new(dt == datatype && var == variant)
                    }
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
                                            u128_to_fixed_width(res, ARCH_SIZE_MIN_BITS)
                                        }
                                        TypX::Int(ISize) => {
                                            let i1 = i1.to_i128().unwrap();
                                            let res = if matches!(op, Shr) {
                                                i1 >> shift
                                            } else {
                                                i1 << shift
                                            };
                                            i128_to_fixed_width(res, ARCH_SIZE_MIN_BITS)
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
            match state.lookup_call(&fun, &args) {
                Some(prev_result) => {
                    state.cache_hits += 1;
                    state.depth -= 1;
                    if state.debug {
                        println!("{}=> {:}", "\t".repeat(state.depth), &prev_result);
                    }
                    return Ok(prev_result);
                }
                None => {
                    state.cache_misses += 1;
                    //println!("{}Calling {}", "\t".repeat(state.depth), exp);
                    let new_args: Result<Vec<Exp>, VirErr> =
                        args.iter().map(|e| eval_expr_internal(ctx, state, e)).collect();
                    let new_args = Arc::new(new_args?);
                    //let new_args_string = new_args.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                    //println!("{} simplified args to {}", "\t".repeat(state.depth), new_args_string);
                    match state.fun_calls.get_mut(fun) {
                        None => {
                            state.fun_calls.insert(fun.clone(), 1);
                        }
                        Some(count) => {
                            *count += 1;
                        }
                    }
                    match state.lookup_call(&fun, &new_args) {
                        Some(prev_result) => {
                            state.cache_hits += 1;
                            Ok(prev_result)
                        }
                        None => {
                            state.cache_misses += 1;
                            let result = if is_sequence_fn(&fun) {
                                eval_seq(ctx, state, exp, &new_args)
                            } else {
                                match ctx.fun_ssts.get(fun) {
                                    None => {
                                        exp_new(Call(fun.clone(), typs.clone(), new_args.clone()))
                                    }
                                    Some((params, body)) => {
                                        state.env.push_scope(true);
                                        for (formal, actual) in params.iter().zip(new_args.iter()) {
                                            if state.debug {
                                                //println!("Binding {:?} to {:?}", formal, actual.x);
                                            }
                                            state
                                                .env
                                                .insert(
                                                    (formal.x.name.clone(), Some(0)),
                                                    actual.clone(),
                                                )
                                                .unwrap();
                                        }
                                        let e = eval_expr_internal(ctx, state, body);
                                        state.env.pop_scope();
                                        e
                                    }
                                }
                            };
                            state.insert_call(fun, &new_args, &result.clone()?);
                            result
                        }
                    }
                }
            }
        }
        CallLambda(_typ, lambda, args) => match &lambda.x {
            Bind(bnd, body) => match &bnd.x {
                BndX::Lambda(bnds) => {
                    let new_args: Result<Vec<Exp>, VirErr> =
                        args.iter().map(|e| eval_expr_internal(ctx, state, e)).collect();
                    let new_args = Arc::new(new_args?);
                    state.env.push_scope(true);
                    for (formal, actual) in bnds.iter().zip(new_args.iter()) {
                        //println!("Binding {:?} to {:?}", formal.name, actual.x);
                        state.env.insert((formal.name.clone(), None), actual.clone()).unwrap();
                    }
                    let e = eval_expr_internal(ctx, state, body);
                    state.env.pop_scope();
                    e
                }
                _ => panic!("CallLambda's binder to contain a lambda.  Instead found {:?}", bnd),
            },
            _ => panic!("CallLambda to contain a lambda.  Instead found {:}", lambda),
        },
        Bind(bnd, e) => match &bnd.x {
            BndX::Let(bnds) => {
                state.env.push_scope(true);
                for b in bnds.iter() {
                    let val = eval_expr_internal(ctx, state, &b.a)?;
                    state.env.insert((b.name.clone(), None), val).unwrap();
                }
                let e = eval_expr_internal(ctx, state, e);
                state.env.pop_scope();
                e
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
        },
        // Ignored by the interpreter at present (i.e., treated as symbolic)
        VarAt(..) | VarLoc(..) | Loc(..) | Old(..) | WithTriggers(..) => ok,
    };
    let res = r?;
    state.depth -= 1;
    if state.debug {
        println!("{}=> {:}", "\t".repeat(state.depth), &res);
    }
    state.simplified.insert(&res);
    Ok(res)
}

pub fn eval_expr(
    exp: &Exp,
    fun_ssts: &SstMap,
    rlimit: u32,
    mode: ComputeMode,
) -> Result<Exp, VirErr> {
    let env = ScopeMap::new();
    let cache = HashMap::new();
    let mut state = State {
        depth: 0,
        env,
        debug: false,
        cache,
        cache_hits: 0,
        cache_misses: 0,
        fun_calls: HashMap::new(),
        simplified: PtrSet::new(),
    };
    // Don't run for more than rlimit seconds
    let time_limit = Duration::new(rlimit as u64, 0);
    let time_start = Instant::now();
    let ctx = Ctx { fun_ssts, time_start, time_limit };
    //println!("Starting from {}", exp);
    let res = eval_expr_internal(&ctx, &mut state, exp)?;
    match mode {
        // Send partial result to Z3
        ComputeMode::Z3 => {
            // Restore the free variables we hid during interpretation
            let res = crate::sst_visitor::map_exp_visitor(&res, &mut |e| match &e.x {
                ExpX::Interp(InterpExp::FreeVar(v)) => {
                    SpannedTyped::new(&e.span, &e.typ, ExpX::Var(v.clone()))
                }
                _ => e.clone(),
            });
            if state.debug {
                if exp.definitely_eq(&res) {
                    println!();
                    println!(
                        "Could not take advantage of compute to simplify expression before sending to z3"
                    );
                    println!("  Unchanged: {}", exp);
                    println!();
                } else {
                    println!("Was able to simplify before sending to Z3");
                    println!("  Old: {}", exp);
                    println!("  New: {}", res);
                    println!();
                }
            }
            Ok(res)
        }
        // Proof must succeed purely through computation
        ComputeMode::ComputeOnly => match res.x {
            ExpX::Const(Constant::Bool(true)) => Ok(res),
            _ => err_str(&exp.span, "assert_by_compute_only failed to result in true"),
        },
    }
}
