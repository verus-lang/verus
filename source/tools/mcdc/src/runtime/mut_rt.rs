// Mutant-schemata runtime. `mcdc mutate` writes this file as src/__mut_rt.rs and the build constants
// as src/__mut_build.rs next to the root of each mutated crate except rust_verify, and appends to the root
//   #[doc(hidden)] #[allow(dead_code, unused)] pub mod __mut { include!("__mut_build.rs"); include!("__mut_rt.rs"); }
// rust_verify uses vir's copy (`use vir::__mut`), so vir and rust_verify share one guard stack.
//
// Active mutants: a bitset read once at startup.
//   MUTANT_BITSET=path   file written by `mcdc mutgen` (format below); refused (exit 2) if its commit,
//                        mutant count or map digest differ from the ones this build was generated with.
//   MUTANT_ID=N          shorthand for a bitset with only bit N.
//   neither              the original program.
// Bitset file: 8 bytes magic "VMUTBS01", 40 bytes source commit (ASCII hex), u32 LE mutant count,
// u64 LE map digest (FNV-1a 64 of mutants.tsv), then ceil((count + 1) / 8) bytes, bit i (LSB first) = id i.
//
// Path log (MUTANT_LOG=dir). Deduplicated per process, written at exit to
// dir/<crate>-<pid>.{reach,inf,stacks,dec}:
//   reach   "point hash"     a mutation point executed with guard stack `hash` on this thread
//   inf     "id hash"        mutant id infected (its alternative differs from the original value or effect)
//   stacks  "hash d:o,.."    the guard stack with that hash (outermost first, at most 64 entries), once
//                            per distinct hash
// MUTANT_LOG_STACKS=0 keeps the reach and infection sets only (hash 0, no stacks file content, depth 0
// in dec): rust_verify_test runs need no path conditions, and deep recursion makes stacks large.
//   dec     "d o depth"      guarded body of decision d entered with outcome o (1 = T, 0 = F, k = match arm)
// The guard stack is thread-local: `guard(d, o)` (inserted at the start of each guarded body) pushes and
// its RAII value pops on drop, so early return, `?`, break and unwinding all pop. Hash 0 = empty stack.
//
// MC/DC: a mutated file also keeps the MC/DC instrumentation of `mcdc instrument`, which calls
// `crate::__mcdc` (runtime/mcdc_rt.rs) directly, so a mutant build writes the same MCDC_DIR records as
// an instrumented build.
// This file must compile under editions 2018, 2021 and 2024.

use std::cell::RefCell;
use std::convert::TryInto;
use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, OnceLock};

// The module includes the build constants first:
//   BUILD_COMMIT: &str, BUILD_COUNT: u32, BUILD_DIGEST: u64,
//   BUILD_MUTANTS: bool (false for `mcdc mutate --mutants-off`: same rewrite, no mutant can be switched on)

const SHARDS: usize = 64;

struct Log {
    dir: std::path::PathBuf,
    /// false with MUTANT_LOG_STACKS=0: reach and infection sets only, every entry with hash 0
    stacks_on: bool,
    reach: Vec<Mutex<HashSet<(u32, u64)>>>,
    inf: Vec<Mutex<HashSet<(u32, u64)>>>,
    stacks: Mutex<HashMap<u64, Vec<(u32, u32)>>>,
    dec: Mutex<HashSet<(u32, u32, u32)>>,
}

struct St {
    any: bool,
    active: Vec<u64>,
    log: Option<Log>,
}

static ST: OnceLock<St> = OnceLock::new();

thread_local! {
    static STK: RefCell<Vec<(u32, u32, u64)>> = const { RefCell::new(Vec::new()) };
}

unsafe extern "C" {
    fn atexit(cb: extern "C" fn()) -> i32;
}

extern "C" fn at_exit() {
    let _ = std::panic::catch_unwind(|| dump());
}

fn dump() {
    let Some(st) = ST.get() else { return };
    let Some(log) = &st.log else { return };
    let krate = option_env!("CARGO_CRATE_NAME").unwrap_or("unknown");
    let pid = std::process::id();
    let w = |ext: &str, s: String| {
        let _ = std::fs::write(log.dir.join(format!("{}-{}.{}", krate, pid, ext)), s);
    };
    for (ext, sets) in [("reach", &log.reach), ("inf", &log.inf)] {
        let mut s = String::new();
        for sh in sets.iter() {
            if let Ok(g) = sh.lock() {
                for (a, h) in g.iter() {
                    s.push_str(&format!("{} {:x}\n", a, h));
                }
            }
        }
        w(ext, s);
    }
    let mut s = String::new();
    if let Ok(g) = log.stacks.lock() {
        for (h, v) in g.iter() {
            let parts: Vec<String> = v.iter().map(|(d, o)| format!("{}:{}", d, o)).collect();
            s.push_str(&format!("{:x} {}\n", h, parts.join(",")));
        }
    }
    w("stacks", s);
    let mut s = String::new();
    if let Ok(g) = log.dec.lock() {
        for (d, o, depth) in g.iter() {
            s.push_str(&format!("{} {} {}\n", d, o, depth));
        }
    }
    w("dec", s);
}

fn fail(msg: String) -> ! {
    eprintln!("mutant runtime: {}", msg);
    std::process::exit(2)
}

fn load_bitset(path: &str, active: &mut Vec<u64>) {
    let data = std::fs::read(path).unwrap_or_else(|e| fail(format!("cannot read MUTANT_BITSET {}: {}", path, e)));
    if data.len() < 60 || &data[0..8] != b"VMUTBS01" {
        fail(format!("MUTANT_BITSET {}: bad magic", path));
    }
    let commit = std::str::from_utf8(&data[8..48]).unwrap_or("");
    let count = u32::from_le_bytes(data[48..52].try_into().unwrap());
    let digest = u64::from_le_bytes(data[52..60].try_into().unwrap());
    if commit != BUILD_COMMIT || count != BUILD_COUNT || digest != BUILD_DIGEST {
        fail(format!(
            "MUTANT_BITSET {} was made for commit {} / {} mutants / map digest {:016x}, but this build is commit {} / {} mutants / map digest {:016x}",
            path, commit, count, digest, BUILD_COMMIT, BUILD_COUNT, BUILD_DIGEST
        ));
    }
    let bits = &data[60..];
    if bits.len() < (count as usize + 1 + 7) / 8 {
        fail(format!("MUTANT_BITSET {}: truncated", path));
    }
    for i in 1..=count as usize {
        if (bits[i / 8] >> (i % 8)) & 1 == 1 {
            active[i / 64] |= 1u64 << (i % 64);
        }
    }
}

fn init() -> St {
    let words = (BUILD_COUNT as usize + 64) / 64 + 1;
    let mut active = vec![0u64; words];
    if !BUILD_MUTANTS && (std::env::var_os("MUTANT_BITSET").is_some() || std::env::var_os("MUTANT_ID").is_some()) {
        fail("this build has its mutants compiled off; MUTANT_BITSET / MUTANT_ID are refused".to_string());
    }
    if let Ok(p) = std::env::var("MUTANT_BITSET") {
        if !p.is_empty() {
            load_bitset(&p, &mut active);
        }
    }
    if let Ok(v) = std::env::var("MUTANT_ID") {
        match v.trim().parse::<usize>() {
            Ok(0) => {}
            Ok(i) if i <= BUILD_COUNT as usize => active[i / 64] |= 1u64 << (i % 64),
            _ => fail(format!("MUTANT_ID={} is not in 0..={}", v, BUILD_COUNT)),
        }
    }
    let any = active.iter().any(|w| *w != 0);
    let dir = std::env::var_os("MUTANT_LOG");
    let log = match dir {
        Some(d) if !d.is_empty() => {
            let d = std::path::PathBuf::from(d);
            let _ = std::fs::create_dir_all(&d);
            unsafe {
                atexit(at_exit);
            }
            Some(Log {
                dir: d,
                stacks_on: std::env::var("MUTANT_LOG_STACKS").map_or(true, |v| v != "0"),
                reach: (0..SHARDS).map(|_| Mutex::new(HashSet::new())).collect(),
                inf: (0..SHARDS).map(|_| Mutex::new(HashSet::new())).collect(),
                stacks: Mutex::new(HashMap::new()),
                dec: Mutex::new(HashSet::new()),
            })
        }
        _ => None,
    };
    St { any, active, log }
}

#[inline(always)]
fn st() -> &'static St {
    ST.get_or_init(init)
}

fn top_hash() -> u64 {
    STK.with(|s| s.borrow().last().map_or(0, |x| x.2))
}

fn record(log: &Log, set: &[Mutex<HashSet<(u32, u64)>>], id: u32) {
    let h = if log.stacks_on { top_hash() } else { 0 };
    let sh = (id as usize ^ (h as usize)) % SHARDS;
    let new = set[sh].lock().map(|mut g| g.insert((id, h))).unwrap_or(false);
    if new && h != 0 {
        if let Ok(mut g) = log.stacks.lock() {
            if !g.contains_key(&h) {
                // the outermost MAX_STACK entries: deep recursion would otherwise make the file
                // quadratic in the depth
                let v = STK.with(|s| s.borrow().iter().take(MAX_STACK).map(|x| (x.0, x.1)).collect());
                g.insert(h, v);
            }
        }
    }
}

/// RAII guard: pops the guard stack on drop when it pushed.
pub struct G(bool);
impl Drop for G {
    #[inline]
    fn drop(&mut self) {
        if self.0 {
            STK.with(|s| {
                s.borrow_mut().pop();
            });
        }
    }
}

/// Stacks deeper than this are written truncated to their outermost entries.
const MAX_STACK: usize = 64;

#[inline]
pub fn guard(d: u32, o: u32) -> G {
    let s = st();
    let Some(log) = &s.log else { return G(false) };
    if !log.stacks_on {
        if let Ok(mut g) = log.dec.lock() {
            g.insert((d, o, 0));
        }
        return G(false);
    }
    let depth = STK.with(|stk| {
        let mut stk = stk.borrow_mut();
        let prev = stk.last().map_or(0x9E3779B97F4A7C15u64, |x| x.2);
        let mut h = prev ^ (((d as u64) << 32) | o as u64);
        h = (h ^ (h >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        h = (h ^ (h >> 27)).wrapping_mul(0x94D049BB133111EB);
        h ^= h >> 31;
        if h == 0 {
            h = 1;
        }
        stk.push((d, o, h));
        stk.len() as u32
    });
    if let Ok(mut g) = log.dec.lock() {
        g.insert((d, o, depth));
    }
    G(true)
}

#[inline(always)]
fn on(s: &St, i: u32) -> bool {
    let i = i as usize;
    i / 64 < s.active.len() && (s.active[i / 64] >> (i % 64)) & 1 == 1
}

/// Marks point `base` REACHED. Returns k in 1..=n for the first active mutant base + k - 1, else 0.
#[inline]
pub fn sel(base: u32, n: u32) -> u32 {
    let s = st();
    if let Some(log) = &s.log {
        record(log, &log.reach, base);
    }
    if !s.any {
        return 0;
    }
    for k in 0..n {
        if on(s, base + k) {
            return k + 1;
        }
    }
    0
}

/// Marks mutant `id` INFECTED: its alternative differs from the original value or effect here.
#[inline]
pub fn infect(id: u32) {
    if let Some(log) = &st().log {
        record(log, &log.inf, id);
    }
}

/// Single-mutant point (statement deletion, skipped error return, operator swap, decision negation).
/// Reaching the point infects the mutant.
#[inline]
pub fn is(base: u32) -> bool {
    let k = sel(base, 1);
    infect(base);
    k == 1
}

/// Atom or condition: base = force true, base+1 = force false, base+2 = negate.
#[inline]
pub fn b(base: u32, v: bool) -> bool {
    let k = sel(base, 3);
    if !v {
        infect(base)
    } else {
        infect(base + 1)
    }
    infect(base + 2);
    match k {
        1 => true,
        2 => false,
        3 => !v,
        _ => v,
    }
}

/// While condition: base = force false (other alternatives would hang).
#[inline]
pub fn bw(base: u32, v: bool) -> bool {
    let k = sel(base, 1);
    if v {
        infect(base)
    }
    if k == 1 { false } else { v }
}

/// Decision negation (swaps the branches of an if/else, or activates/deactivates the guarded code).
#[inline]
pub fn n(base: u32, v: bool) -> bool {
    if is(base) { !v } else { v }
}

/// Returned bool: base = negate, base+1 = true, base+2 = false.
#[inline]
pub fn rb(base: u32, v: bool) -> bool {
    let k = sel(base, 3);
    infect(base);
    if !v {
        infect(base + 1)
    } else {
        infect(base + 2)
    }
    match k {
        1 => !v,
        2 => true,
        3 => false,
        _ => v,
    }
}

// op codes: 0 <, 1 <=, 2 >, 3 >=
/// Relational operator replaced by its boundary neighbour: < to <=, <= to <, > to >=, >= to >.
#[inline]
pub fn ord<T: PartialOrd<U> + ?Sized, U: ?Sized>(base: u32, op: u8, a: &T, b: &U) -> bool {
    let k = sel(base, 1);
    let (orig, alt) = match op {
        0 => (a < b, a <= b),
        1 => (a <= b, a < b),
        2 => (a > b, a >= b),
        _ => (a >= b, a > b),
    };
    if orig != alt {
        infect(base)
    }
    if k == 1 { alt } else { orig }
}

// op codes: 0 ==, 1 !=
/// Equality operator replaced by its negation.
#[inline]
pub fn eq<T: PartialEq<U> + ?Sized, U: ?Sized>(base: u32, op: u8, a: &T, b: &U) -> bool {
    let k = sel(base, 1);
    infect(base);
    let orig = if op == 0 { a == b } else { a != b };
    if k == 1 { !orig } else { orig }
}

pub trait Obo: Copy {
    fn p1(self) -> Self;
    fn m1(self) -> Self;
}
macro_rules! obo {
    ($($t:ty)*) => { $(impl Obo for $t {
        #[inline] fn p1(self) -> Self { self.wrapping_add(1) }
        #[inline] fn m1(self) -> Self { self.wrapping_sub(1) }
    })* }
}
obo!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

/// Integer constant or index: base = +1, base+1 = -1 (wrapping).
#[inline]
pub fn ob<T: Obo>(base: u32, v: T) -> T {
    let k = sel(base, 2);
    infect(base);
    infect(base + 1);
    match k {
        1 => v.p1(),
        2 => v.m1(),
        _ => v,
    }
}

/// `e?` with the error swallowed: an Err becomes Ok(Default::default()). Infected only when e is Err.
#[inline]
pub fn q<T: Default, E>(base: u32, r: Result<T, E>) -> Result<T, E> {
    let k = sel(base, 1);
    match r {
        Err(e) => {
            infect(base);
            if k == 1 { Ok(T::default()) } else { Err(e) }
        }
        ok => ok,
    }
}

/// An `Err(..)` value replaced by Ok(Default::default()).
#[inline]
pub fn okd<T: Default, E>(base: u32, r: Result<T, E>) -> Result<T, E> {
    let k = sel(base, 1);
    match r {
        Err(e) => {
            infect(base);
            if k == 1 { Ok(T::default()) } else { Err(e) }
        }
        ok => ok,
    }
}

/// vec![e0, .., e(n-1)]: mutant base+i removes element i.
#[inline]
pub fn rv<T>(base: u32, n: u32, mut v: Vec<T>) -> Vec<T> {
    let k = sel(base, n);
    for i in 0..n.min(v.len() as u32) {
        infect(base + i);
    }
    if k > 0 && (k as usize) <= v.len() {
        v.remove(k as usize - 1);
    }
    v
}

// ---- container / Option / enum operators ----

/// Selector that always infects (enum-variant swaps): returns k in 1..=n or 0.
#[inline]
pub fn seli(base: u32, n: u32) -> u32 {
    let k = sel(base, n);
    for i in 0..n {
        infect(base + i);
    }
    k
}

/// contains / is_empty negated.
#[inline]
pub fn nb(base: u32, v: bool) -> bool {
    if is(base) { !v } else { v }
}

/// len(): base = +1, base+1 = saturating -1.
#[inline]
pub fn ln(base: u32, v: usize) -> usize {
    let k = sel(base, 2);
    infect(base);
    if v > 0 {
        infect(base + 1)
    }
    match k {
        1 => v + 1,
        2 => v.saturating_sub(1),
        _ => v,
    }
}

/// get / get_mut / Some(..) replaced by None.
#[inline]
pub fn none<T>(base: u32, v: Option<T>) -> Option<T> {
    let k = sel(base, 1);
    if v.is_some() {
        infect(base)
    }
    if k == 1 { None } else { v }
}

/// first() <-> last().
#[inline]
pub fn fl<'a, T>(base: u32, a: Option<&'a T>, b: Option<&'a T>) -> Option<&'a T> {
    let k = sel(base, 1);
    if a.map(|r| r as *const T) != b.map(|r| r as *const T) {
        infect(base)
    }
    if k == 1 { b } else { a }
}

/// iter() -> iter().rev() (boxed so both have one type).
#[inline]
pub fn it<'a, I: DoubleEndedIterator + 'a>(base: u32, i: I) -> Box<dyn Iterator<Item = I::Item> + 'a> {
    let k = sel(base, 1);
    infect(base);
    if k == 1 { Box::new(i.rev()) } else { Box::new(i) }
}

/// retain(p) -> retain(!p).
#[inline]
pub fn negp<T: ?Sized, F: FnMut(&T) -> bool>(base: u32, mut f: F) -> impl FnMut(&T) -> bool {
    let k = sel(base, 1);
    infect(base);
    move |x: &T| {
        let r = f(x);
        if k == 1 { !r } else { r }
    }
}

/// x.unwrap_or(d) -> d.
pub trait MutUnwrapOr<T> {
    fn m(self, base: u32, d: T) -> T;
}
impl<T> MutUnwrapOr<T> for Option<T> {
    #[inline]
    fn m(self, base: u32, d: T) -> T {
        let k = sel(base, 1);
        if self.is_some() {
            infect(base)
        }
        if k == 1 { d } else { self.unwrap_or(d) }
    }
}
impl<T, E> MutUnwrapOr<T> for Result<T, E> {
    #[inline]
    fn m(self, base: u32, d: T) -> T {
        let k = sel(base, 1);
        if self.is_ok() {
            infect(base)
        }
        if k == 1 { d } else { self.unwrap_or(d) }
    }
}

/// insert / remove used as a value: the "absent" result (None / false).
pub trait Absent {
    fn absent(&self) -> bool;
    fn make_absent(self) -> Self;
}
impl Absent for bool {
    #[inline]
    fn absent(&self) -> bool {
        !*self
    }
    #[inline]
    fn make_absent(self) -> Self {
        false
    }
}
impl<T> Absent for Option<T> {
    #[inline]
    fn absent(&self) -> bool {
        self.is_none()
    }
    #[inline]
    fn make_absent(self) -> Self {
        None
    }
}
#[inline]
pub fn absent<T: Absent>(base: u32, v: T) -> T {
    let k = sel(base, 1);
    if !v.absent() {
        infect(base)
    }
    if k == 1 { v.make_absent() } else { v }
}
