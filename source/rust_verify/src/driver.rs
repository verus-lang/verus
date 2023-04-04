use crate::verifier::{Verifier, VerifierCallbacksEraseMacro};
use rustc_errors::ErrorGuaranteed;
use std::time::{Duration, Instant};

fn mk_compiler<'a, 'b>(
    rustc_args: &'a [String],
    verifier: &'b mut (dyn verus_rustc_driver::Callbacks + Send),
    file_loader: Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>,
) -> verus_rustc_driver::RunCompiler<'a, 'b> {
    let mut compiler = verus_rustc_driver::RunCompiler::new(rustc_args, verifier);
    compiler.set_file_loader(Some(file_loader));
    compiler
}

fn run_compiler<'a, 'b>(
    mut rustc_args: Vec<String>,
    syntax_macro: bool,
    erase_ghost: bool,
    verifier: &'b mut (dyn verus_rustc_driver::Callbacks + Send),
    file_loader: Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>,
    build_test_mode: bool,
) -> Result<(), ErrorGuaranteed> {
    crate::config::enable_default_features_and_verus_attr(
        &mut rustc_args,
        syntax_macro,
        erase_ghost,
    );
    mk_compiler(&rustc_args, verifier, file_loader).run()
}

fn print_verification_results(verifier: &Verifier) {
    if !verifier.encountered_vir_error {
        println!(
            "verification results:: verified: {} errors: {}",
            verifier.count_verified, verifier.count_errors
        );
    }
}

/*
When using the --erasure macro option (Erasure::Macro),
we have to run rustc twice on the original source code,
once erasing ghost code and once keeping ghost code.

exec code --> type-check, mode-check --> lifetime (borrow) check exec code --> compile

all code --> type-check, mode-check --+
                                      |
                                      +--> lifetime (borrow) check proof code

This causes some tension in the order of operations:
it would be cleanest to run one rustc invocation entirely,
and then the other entirely, but this would be slow.
For example, if we ran the ghost-erase rustc and then the ghost-keep rustc,
then the user would receive no feedback about verification until parsing and macro expansion
for both rustc invocations had completed.
On the other hand, if we ran the ghost-keep rustc and then the ghost-erase rustc,
the user would receive no feedback about ownership/lifetime/borrow checking errors
in exec functions until verification had completed.
So for better latency, the implementation interleaves the two rustc invocations
(marked GHOST for keeping ghost and EXEC for erasing ghost):

GHOST: Parsing, AST construction, macro expansion (including the Verus syntax macro, keeping ghost code)
GHOST: Rust AST -> HIR
GHOST: Rust's type checking
GHOST: Verus HIR/THIR -> VIR conversion
GHOST: Verus mode checking
GHOST: Verus lifetime/borrow checking for both proof and exec code (by generating synthetic code and running rustc), but delaying any lifetime/borrow checking error messages until EXEC has a chance to run
GHOST: If there were no lifetime/borrow checking errors, run Verus SMT solving
EXEC: Parsing, AST construction, macro expansion (including the Verus syntax macro, erasing ghost code)
EXEC: Rust AST -> HIR
EXEC: Rust's type checking
EXEC: Rust HIR/THIR -> MIR conversion
EXEC: Rust's lifetime/borrow checking for non-ghost (exec) code
GHOST: If there were no EXEC errors, but there were GHOST lifetime/borrow checking errors, print the GHOST lifetime/borrow checking errors
EXEC: Rust compilation to machine code (if --compile is set)

To avoid having to run the EXEC lifetime/borrow checking before verification,
which would add latency before verification,
we use the synthetic code ownership/lifetime/borrow checking in lifetime.rs to perform
a quick early test for ownership/lifetime/borrow checking on all code (even pure exec code).
If this detects any ownership/lifetime/borrow errors, the implementation skips verification
and gives the EXEC rustc a chance to run,
on the theory that the EXEC rustc will generate better error messages
for any exec ownership/lifetime/borrow errors.
The GHOST lifetime/borrow errors are printed only if the EXEC rustc finds no errors.

In the long run, we'd like to move to a model where rustc only runs once on the original source code.
This would avoid the complex interleaving above and avoid needing to use lifetime.rs
for all functions (it would only be needed for functions with tracked data in proof code).
*/
pub struct CompilerCallbacksEraseMacro {
    pub lifetimes_only: bool,
}

impl verus_rustc_driver::Callbacks for CompilerCallbacksEraseMacro {
    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &verus_rustc_interface::interface::Compiler,
        queries: &'tcx verus_rustc_interface::Queries<'tcx>,
    ) -> verus_rustc_driver::Compilation {
        if self.lifetimes_only {
            crate::lifetime::check(queries);
            verus_rustc_driver::Compilation::Stop
        } else {
            verus_rustc_driver::Compilation::Continue
        }
    }
}

pub struct Stats {
    pub time_verify: Duration,
    pub time_lifetime: Duration,
    pub time_compile: Duration,
    pub time_erasure: Duration,
}

pub(crate) fn run_with_erase_macro_compile(
    mut rustc_args: Vec<String>,
    file_loader: Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>,
    compile: bool,
    build_test_mode: bool,
) -> Result<(), ErrorGuaranteed> {
    let mut callbacks = CompilerCallbacksEraseMacro { lifetimes_only: !compile };
    rustc_args.extend(["--cfg", "verus_macro_erase_ghost"].map(|s| s.to_string()));
    let allow = &[
        "unused_imports",
        "unused_variables",
        "unreachable_patterns",
        "unused_parens",
        "unused_braces",
        "dead_code",
        "unreachable_code",
        "unused_mut",
        "unused_labels",
        "unused_attributes",
    ];
    for a in allow {
        rustc_args.extend(["-A", a].map(|s| s.to_string()));
    }
    run_compiler(rustc_args, true, true, &mut callbacks, file_loader, build_test_mode)
}

struct VerusRoot {
    path: std::path::PathBuf,
    in_vargo: bool,
}

fn find_verusroot() -> Option<VerusRoot> {
    std::env::var("VARGO_TARGET_DIR")
        .ok()
        .and_then(|target_dir| {
            let path = std::path::PathBuf::from(&target_dir);
            Some(VerusRoot { path, in_vargo: true })
        })
        .or_else(|| {
            std::env::var("VERUS_ROOT").ok().and_then(|verusroot| {
                let mut path = std::path::PathBuf::from(&verusroot);
                if !path.is_absolute() {
                    path = std::env::current_dir().expect("working directory invalid").join(path);
                }
                Some(VerusRoot { path, in_vargo: false })
            })
        })
}

#[cfg(target_os = "macos")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "dylib";
    pub const EXE: &str = "exe";
}

#[cfg(target_os = "linux")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "so";
    pub const EXE: &str = "";
}

#[cfg(target_os = "windows")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "";
    pub const LIB_DL: &str = "dll";
    pub const EXE: &str = "exe";
}

use lib_exe_names::{LIB_DL, LIB_PRE};

#[derive(Debug)]
pub struct VerusExterns<'a> {
    path: &'a std::path::PathBuf,
    has_vstd: bool,
}

impl<'a> VerusExterns<'a> {
    pub fn to_args(&self) -> impl Iterator<Item = String> {
        let mut args = vec![
            format!("--extern"),
            format!(
                "builtin={}",
                self.path.join(format!("{LIB_PRE}builtin.rlib")).to_str().unwrap()
            ),
            format!("--extern"),
            format!(
                "builtin_macros={}",
                self.path.join(format!("{LIB_PRE}builtin_macros.{LIB_DL}")).to_str().unwrap()
            ),
            format!("--extern"),
            format!(
                "state_machines_macros={}",
                self.path
                    .join(format!("{LIB_PRE}state_machines_macros.{LIB_DL}"))
                    .to_str()
                    .unwrap()
            ),
        ];
        if self.has_vstd {
            args.push(format!("--extern"));
            args.push(format!(
                "vstd={}",
                self.path.join(format!("{LIB_PRE}vstd.rlib")).to_str().unwrap()
            ));
        }
        args.into_iter()
    }
}

pub fn run<F>(
    mut verifier: Verifier,
    mut rustc_args: Vec<String>,
    file_loader: F,
    build_test_mode: bool,
) -> (Verifier, Stats, Result<(), ()>)
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    if !build_test_mode {
        if let Some(VerusRoot { path: verusroot, in_vargo }) = find_verusroot() {
            verifier
                .args
                .import
                .push((format!("vstd"), verusroot.join("vstd.vir").to_str().unwrap().to_string()));
            rustc_args.push(format!("--edition"));
            rustc_args.push(format!("2018"));
            let externs = VerusExterns { path: &verusroot, has_vstd: !verifier.args.no_vstd };
            rustc_args.extend(externs.to_args());
            if in_vargo && !std::env::var("VERUS_Z3_PATH").is_ok() {
                std::env::set_var(
                    "VERUS_Z3_PATH",
                    verusroot
                        .parent()
                        .and_then(|x| x.parent())
                        .unwrap()
                        .join(if cfg!(windows) { "z3.exe" } else { "z3" })
                        .to_str()
                        .unwrap(),
                );
            }
        }
    } else if verifier.args.no_vstd {
        panic!("cannot use --no-vstd in test mode");
    }

    let time0 = Instant::now();

    // Build VIR and run verification
    let mut verifier_callbacks = VerifierCallbacksEraseMacro {
        verifier,
        lifetime_start_time: None,
        rustc_args: rustc_args.clone(),
        file_loader: Some(Box::new(file_loader.clone())),
        build_test_mode,
    };
    let status = run_compiler(
        rustc_args.clone(),
        true,
        false,
        &mut verifier_callbacks,
        Box::new(file_loader.clone()),
        build_test_mode,
    );
    if !verifier_callbacks.verifier.encountered_vir_error {
        print_verification_results(&verifier_callbacks.verifier);
    }
    let VerifierCallbacksEraseMacro { verifier, lifetime_start_time, .. } = verifier_callbacks;
    let time2 = Instant::now();
    let time1 = lifetime_start_time.unwrap_or(time2);

    if status.is_err() || verifier.encountered_vir_error {
        return (
            verifier,
            Stats {
                time_verify: time1 - time0,
                time_lifetime: time2 - time1,
                time_compile: Duration::new(0, 0),
                time_erasure: Duration::new(0, 0),
            },
            Err(()),
        );
    }

    let compile_status = run_with_erase_macro_compile(
        rustc_args,
        Box::new(file_loader),
        verifier.args.compile,
        build_test_mode,
    );

    let time3 = Instant::now();

    let stats = Stats {
        time_verify: time1 - time0,
        time_lifetime: time2 - time1,
        time_compile: time3 - time2,
        time_erasure: Duration::new(0, 0),
    };

    // Run borrow checker and compiler with #[exec] (not #[proof])
    if let Err(_) = compile_status {
        return (verifier, stats, Err(()));
    }

    (verifier, stats, Ok(()))
}
