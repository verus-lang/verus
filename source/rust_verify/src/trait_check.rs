//! This file was previously concerned with lifetime checking of tracked code,
//! but now all it does is invoke the trait-conflict checker.

// In functions executed through the trait-conflict checker rustc driver, use `ldbg!` for debug output.

use crate::spans::SpanContext;
use crate::trait_check_emit::*;
use crate::trait_check_generate::*;
use crate::util::error;
use serde::Deserialize;
use std::fs::File;
use std::io::Write;
use std::sync::Arc;
use vir::ast::VirErr;
use vir::messages::{Message, MessageLevel, message_bare};

const LDBG_PREFIX: &str = "!!!ldbg!!! ";

#[allow(unused)]
fn ldbg_prefix_all_lines(s: String) -> String {
    let mut s2 = s.lines().map(|l| LDBG_PREFIX.to_string() + l).fold(
        String::with_capacity(s.len()),
        |mut acc, l| {
            acc += &l;
            acc += "\n";
            acc
        },
    );
    s2.pop().unwrap();
    s2
}

// Derived from rust's std::dbg!
#[macro_export]
macro_rules! ldbg {
    // NOTE: We cannot use `concat!` to make a static string as a format argument
    // of `eprintln!` because `file!` could contain a `{` or
    // `$val` expression could be a block (`{ .. }`), in which case the `eprintln!`
    // will be malformed.
    () => {
        ::std::eprintln!("{}[trait-conflict-checking {}:{}]", LDBG_PREFIX, $crate::file!(), $crate::line!())
    };
    ($val:expr $(,)?) => {
        // Use of `match` here is intentional because it affects the lifetimes
        // of temporaries - https://stackoverflow.com/a/48732525/1063961
        match $val {
            tmp => {
                let __string = ::std::format!("[trait-conflict-checking {}:{}] {} = {:#?}", ::std::file!(), ::std::line!(), ::std::stringify!($val), &tmp);
                ::std::eprintln!("{}", $crate::trait_check::ldbg_prefix_all_lines(__string));
                tmp
            }
        }
    };
    ($($val:expr),+ $(,)?) => {
        ($(ldbg!($val)),+,)
    };
}

const PROOF_FN_ONCE: u8 = 1;
const PROOF_FN_MUT: u8 = 2;
const PROOF_FN: u8 = 3;
const PROOF_FN_COPY: u8 = 4;
const PROOF_FN_SEND: u8 = 5;
const PROOF_FN_SYNC: u8 = 6;

// REVIEW: Most of this may be unnecessary now that lifetime-checking has moved out of here
const PRELUDE: &str = "\
#![feature(negative_impls)]
#![feature(with_negative_coherence)]
#![feature(box_patterns)]
#![feature(ptr_metadata)]
#![feature(never_type)]
#![feature(allocator_api)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(tuple_trait)]
#![feature(f16)]
#![feature(f128)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unconditional_recursion)]
#![allow(unused_mut)]
#![allow(unused_labels)]
use std::marker::PhantomData;
use std::marker::Tuple;
use std::rc::Rc;
use std::sync::Arc;
use std::alloc::Allocator;
use std::alloc::Global;
use std::mem::ManuallyDrop;
use std::ptr::Pointee;
use std::ptr::Thin;
fn op<A, B>(a: A) -> B { panic!() }
fn static_ref<T>(t: T) -> &'static T { panic!() }
fn tracked_new<T>(t: T) -> Tracked<T> { panic!() }
fn tracked_exec_borrow<'a, T>(t: &'a T) -> &'a Tracked<T> { panic!() }
fn clone<T>(t: &T) -> T { panic!() }
fn rc_new<T>(t: T) -> std::rc::Rc<T> { panic!() }
fn arc_new<T>(t: T) -> std::sync::Arc<T> { panic!() }
fn box_new<T>(t: T) -> Box<T> { panic!() }
struct Tracked<A> { a: PhantomData<A> }
impl<A> Tracked<A> {
    pub fn get(self) -> A { panic!() }
    pub fn borrow(&self) -> &A { panic!() }
    pub fn borrow_mut(&mut self) -> &mut A { panic!() }
}
struct Ghost<A> { a: PhantomData<A> }
impl<A> Clone for Ghost<A> { fn clone(&self) -> Self { panic!() } }
impl<A> Copy for Ghost<A> { }
impl<A: Copy> Clone for Tracked<A> { fn clone(&self) -> Self { panic!() } }
impl<A: Copy> Copy for Tracked<A> { }
#[derive(Clone, Copy)] struct int;
#[derive(Clone, Copy)] struct nat;
#[derive(Clone, Copy)] struct real;
struct FnSpec<Args, Output> { x: PhantomData<(Args, Output)> }
struct InvariantBlockGuard;
fn open_atomic_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_local_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_invariant_end<V>(_guard: InvariantBlockGuard, _v: V) { panic!() }
fn index<'a, V, Idx, Output>(v: &'a V, index: Idx) -> &'a Output { panic!() }
trait IndexSet{
fn index_set<Idx, V>(&mut self, index: Idx, val: V) { panic!() }
}
impl<A:?Sized> IndexSet for A {}
struct C<const N: usize, A: ?Sized>(Box<A>);
struct Arr<A: ?Sized, const N: usize>(Box<A>);
struct Dyn<const N: usize, A>(Box<A>, [bool]);
fn use_type_invariant<A>(a: A) -> A { a }

struct FnProof<'a, P, M, N, A, O>(PhantomData<P>, PhantomData<M>, PhantomData<N>, PhantomData<&'a fn(A) -> O>);
struct FOpts<const B: u8, C, const D: u8, const E: u8, const G: u8>(PhantomData<C>);
trait ProofFnOnce {}
trait ProofFnMut: ProofFnOnce {}
trait ProofFn: ProofFnMut {}
struct ProofFnConfirm;
trait ConfirmCopy<const D: u8, F> {}
trait ConfirmUsage<A, O, const B: u8, F> {}
impl<const B: u8, C, const E: u8, const G: u8> Clone for FOpts<B, C, (PROOF_FN_COPY), E, G> { fn clone(&self) -> Self { panic!() } }
impl<const B: u8, C, const E: u8, const G: u8> Copy for FOpts<B, C, (PROOF_FN_COPY), E, G> {}
impl<const B: u8, C, const D: u8, const E: u8, const G: u8> ProofFnOnce for FOpts<B, C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFnMut for FOpts<(PROOF_FN_MUT), C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFnMut for FOpts<(PROOF_FN), C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFn for FOpts<(PROOF_FN), C, D, E, G> {}
impl<'a, P: Copy, M, N, A, O> Clone for FnProof<'a, P, M, N, A, O> { fn clone(&self) -> Self { panic!() } }
impl<'a, P: Copy, M, N, A, O> Copy for FnProof<'a, P, M, N, A, O> {}
impl<'a, P: ProofFnOnce, M, N, A: Tuple, O> FnOnce<A> for FnProof<'a, P, M, N, A, O> {
    type Output = O;
    extern \"rust-call\" fn call_once(self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<'a, P: ProofFnMut, M, N, A: Tuple, O> FnMut<A> for FnProof<'a, P, M, N, A, O> {
    extern \"rust-call\" fn call_mut(&mut self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<'a, P: ProofFn, M, N, A: Tuple, O> Fn<A> for FnProof<'a, P, M, N, A, O> {
    extern \"rust-call\" fn call(&self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<F: Copy> ConfirmCopy<(PROOF_FN_COPY), F> for ProofFnConfirm {}
impl<F> ConfirmCopy<0, F> for ProofFnConfirm {}
impl<A: Tuple, O, F: FnOnce<A, Output = O>> ConfirmUsage<A, O, (PROOF_FN_ONCE), F> for ProofFnConfirm {}
impl<A: Tuple, O, F: FnMut<A, Output = O>> ConfirmUsage<A, O, (PROOF_FN_MUT), F> for ProofFnConfirm {}
impl<A: Tuple, O, F: Fn<A, Output = O>> ConfirmUsage<A, O, (PROOF_FN), F> for ProofFnConfirm {}
pub fn closure_to_fn_proof<'a, const B: u8, const D: u8, const E: u8, const G: u8, M, N, A, O, F: 'a>(_f: F) -> FnProof<'a, FOpts<B, (), D, E, G>, M, N, A, O>
where ProofFnConfirm: ConfirmUsage<A, O, B, F>, ProofFnConfirm: ConfirmCopy<D, F>, M: Tuple, A: Tuple,
{ panic!() }

fn main() {}
";

fn emit_check_trait_conflicts<'tcx>(
    spans: &SpanContext,
    emit_state: &mut EmitState,
    vir_crate: &vir::ast::Krate,
) -> State {
    let mut gen_state = crate::trait_check_generate::State::new();
    crate::trait_conflicts::gen_check_trait_impl_conflicts(spans, vir_crate, &mut gen_state);

    let prelude = PRELUDE
        .replace("(PROOF_FN_ONCE)", &PROOF_FN_ONCE.to_string())
        .replace("(PROOF_FN_MUT)", &PROOF_FN_MUT.to_string())
        .replace("(PROOF_FN)", &PROOF_FN.to_string())
        .replace("(PROOF_FN_COPY)", &PROOF_FN_COPY.to_string())
        .replace("(PROOF_FN_SEND)", &PROOF_FN_SEND.to_string())
        .replace("(PROOF_FN_SYNC)", &PROOF_FN_SYNC.to_string());
    for line in prelude.split('\n') {
        emit_state.writeln(line.replace("\r", ""));
    }

    for t in gen_state.trait_decls.iter() {
        emit_trait_decl(emit_state, t);
    }
    for d in gen_state.datatype_decls.iter() {
        emit_datatype_decl(emit_state, d);
    }
    for t in gen_state.trait_impls.iter() {
        emit_trait_impl(emit_state, t);
    }
    gen_state
}

pub(crate) struct TCFileLoader {
    pub(crate) rust_code: String,
}

impl TCFileLoader {
    const FILENAME: &'static str = "dummyrs.rs";
}

impl rustc_span::source_map::FileLoader for TCFileLoader {
    fn file_exists(&self, _path: &std::path::Path) -> bool {
        panic!("unexpected call to file_exists")
    }

    fn read_file(&self, path: &std::path::Path) -> Result<String, std::io::Error> {
        assert!(path.display().to_string() == Self::FILENAME);
        Ok(self.rust_code.clone())
    }

    fn read_binary_file(&self, path: &std::path::Path) -> Result<Arc<[u8]>, std::io::Error> {
        assert!(path.display().to_string() == Self::FILENAME);
        Ok(self.rust_code.as_bytes().into())
    }
}

#[derive(Debug, Deserialize)]
struct DiagnosticSpan {
    line_start: usize,
    line_end: usize,
    column_start: usize,
    column_end: usize,
}

#[derive(Debug, Deserialize)]
struct Diagnostic {
    message: String,
    level: String,
    spans: Vec<DiagnosticSpan>,
    rendered: Option<String>,
}

pub const TC_DRIVER_ARG: &'static str = "--internal-trait-conflict-driver";

pub fn trait_check_rustc_driver(rustc_args: &[String], rust_code: String) {
    let mut callbacks = crate::driver::TCCallbacks { code: rust_code };
    rustc_driver::run_compiler(rustc_args, &mut callbacks)
}

pub(crate) fn check_trait_conflicts<'tcx>(
    spans: &SpanContext,
    vir_crate: &vir::ast::Krate,
    tc_log_file: Option<File>,
) -> Result<Vec<Message>, VirErr> {
    let mut emit_state = EmitState::new();
    let gen_state = emit_check_trait_conflicts(spans, &mut emit_state, vir_crate);
    let mut rust_code: String = String::new();
    for line in &emit_state.lines {
        rust_code.push_str(&line.text);
        rust_code.push('\n');
    }
    if let Some(mut file) = tc_log_file {
        write!(file, "{}", &rust_code).expect("error writing to trait-conflict log file");
    }
    let rustc_args = [TC_DRIVER_ARG, TCFileLoader::FILENAME, "--error-format=json"];

    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        // avoid warning about jobserver fd
        .env_remove("CARGO_MAKEFLAGS")
        .args(&rustc_args[..])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("could not execute trait-conflict rustc process");
    let mut child_stdin = child.stdin.take().expect("take stdin");
    child_stdin
        .write_all(rust_code.as_bytes())
        .expect("failed to send code to trait-conflict rustc");
    std::mem::drop(child_stdin);
    let run = child.wait_with_output().expect("trait-conflict rustc wait failed");
    let rust_output = std::str::from_utf8(&run.stderr[..]).unwrap().trim();
    let mut msgs: Vec<Message> = Vec::new();
    let debug = false;
    if rust_output.len() > 0 {
        for ss in rust_output.split("\n") {
            if let Some(ss) = ss.strip_prefix(LDBG_PREFIX) {
                eprintln!("{}", ss);
            } else {
                let diag: Diagnostic = serde_json::from_str(ss).expect("serde_json from_str");
                if diag.level == "failure-note" {
                    continue;
                }
                if diag.level == "warning" {
                    dbg!("internal error: unexpected warning");
                    dbg!(diag);
                    continue;
                }
                assert!(diag.level == "error");
                let msg_text = gen_state.unmangle_names(&diag.message);
                let mut msg = message_bare(MessageLevel::Error, &msg_text);
                if debug {
                    dbg!(&msg);
                }
                use std::collections::HashSet;
                let mut missing_span = diag.spans.len() == 0;
                let mut missing_span_line_seqs: HashSet<(usize, usize)> = HashSet::new();
                for dspan in &diag.spans {
                    if debug {
                        dbg!(&dspan);
                    }
                    let span = emit_state.get_span(
                        dspan.line_start - 1,
                        dspan.column_start - 1,
                        dspan.line_end - 1,
                        dspan.column_end - 1,
                    );
                    if let Some(span) = span {
                        msg = msg.primary_span(&spans.to_air_span(span));
                    } else {
                        eprintln!(
                            "note: could not find span associated with error message; printing raw error message instead"
                        );
                        missing_span = true;
                        let mut l1 = dspan.line_start - 1;
                        let mut l2 = dspan.line_end - 1;
                        while l1 > 0 && !emit_state.lines[l1].start_of_decl {
                            l1 -= 1;
                        }
                        while l2 + 1 < emit_state.lines.len() && !emit_state.lines[l2].start_of_decl
                        {
                            l2 += 1;
                        }
                        if !missing_span_line_seqs.contains(&(l1, l2)) {
                            for i in l1..=l2 {
                                eprintln!("{}", &emit_state.lines[i].text);
                            }
                            missing_span_line_seqs.insert((l1, l2));
                        }
                    }
                }
                if missing_span {
                    eprintln!("{}", &diag.rendered.unwrap());
                }
                msgs.push(msg);
            }
        }
    }
    if debug {
        dbg!(msgs.len());
    }
    if msgs.len() == 0 && !run.status.success() {
        Err(error("trait-conflict checking failed"))
    } else {
        Ok(msgs)
    }
}
