use crate::config::Vstd;
use crate::externs::VerusExterns;
use crate::verifier::{Verifier, VerifierCallbacksEraseMacro};
use rustc_hir::{ImplItemKind, ItemKind, MaybeOwner, OwnerNode};
use rustc_middle::ty::TyCtxt;
use std::time::{Duration, Instant};

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

pub fn run_rustc_compiler_directly(rustc_args: &Vec<String>) -> () {
    rustc_driver::run_compiler(&rustc_args, &mut DefaultCallbacks)
}

fn run_compiler<'a, 'b>(
    mut rustc_args: Vec<String>,
    syntax_macro: bool,
    erase_ghost: bool,
    verifier: &'b mut (dyn rustc_driver::Callbacks + Send),
) -> Result<(), ()> {
    crate::config::enable_default_features_and_verus_attr(
        &mut rustc_args,
        syntax_macro,
        erase_ghost,
    );
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        rustc_driver::run_compiler(&rustc_args, verifier)
    }));
    result.map_err(|_| ())
}

pub fn is_verifying_entire_crate(verifier: &Verifier) -> bool {
    verifier.args.verify_function.is_none()
        && verifier.args.verify_module.is_empty()
        && !verifier.args.verify_root
}

// Call Rust's mir_borrowck to check lifetimes of #[spec] and #[proof] code and variables
pub(crate) fn check<'tcx>(tcx: TyCtxt<'tcx>, do_lifetime: bool) {
    rustc_hir_analysis::check_crate(tcx);
    if tcx.dcx().err_count() != 0 {
        return;
    }
    if !do_lifetime {
        return;
    }
    let krate = tcx.hir_crate(());
    for owner in &krate.owners {
        if let MaybeOwner::Owner(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => match &item.kind {
                    rustc_hir::ItemKind::Fn { .. } => {
                        tcx.ensure_ok().mir_borrowck(item.owner_id.def_id); // REVIEW(main_new) correct?
                    }
                    ItemKind::Impl(impll) => {
                        for item_id in impll.items {
                            let item = tcx.hir_impl_item(*item_id);
                            match item.kind {
                                ImplItemKind::Fn { .. } => {
                                    tcx.ensure_ok().mir_borrowck(item.owner_id.def_id); // REVIEW(main_new) correct?
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => (),
                },
                _ => {}
            }
        }
    }
}

pub(crate) struct TCCallbacks {
    pub(crate) code: String,
}

impl rustc_driver::Callbacks for TCCallbacks {
    // note: we only need to call into config here,
    // to change the file_loader
    fn config<'tcx>(&mut self, cfg: &mut rustc_interface::interface::Config) {
        cfg.file_loader =
            Some(Box::new(crate::trait_check::TCFileLoader { rust_code: self.code.clone() }));
    }

    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        // REVIEW: is this call needed for trait-conflict checking?
        check(queries, false);
        rustc_driver::Compilation::Stop
    }
}

/*
We have to run rustc twice on the original source code,
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
struct CompilerCallbacksEraseMacro {
    pub do_compile: bool,
}

impl rustc_driver::Callbacks for CompilerCallbacksEraseMacro {
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        if !self.do_compile {
            check(tcx, true);
            rustc_driver::Compilation::Stop
        } else {
            rustc_driver::Compilation::Continue
        }
    }
}

/// Captures the verification and compilation time
pub struct Stats {
    /// time spent in rustc for parsing, initialization, macro expansion, etc.
    /// (from run_compiler until we enter the `after_expansion` callback)
    pub time_rustc: Duration,
    /// time it took to verify the crate (this includes VIR generation, SMT solving, etc.)
    pub time_verify: Duration,
    /// tiem for lifetime/borrow checking
    pub time_trait_conflicts: Duration,
    /// compilation time
    pub time_compile: Duration,
}

pub(crate) fn run_with_erase_macro_compile(
    mut rustc_args: Vec<String>,
    compile: bool,
    vstd: Vstd,
) -> Result<(), ()> {
    let mut callbacks = CompilerCallbacksEraseMacro { do_compile: compile };
    rustc_args.extend(["--cfg", "verus_keep_ghost"].map(|s| s.to_string()));
    if matches!(vstd, Vstd::IsCore | Vstd::ImportedViaCore) {
        rustc_args.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    } else if vstd == Vstd::NoVstd {
        rustc_args.extend(["--cfg", "verus_no_vstd"].map(|s| s.to_string()));
    }
    let allow = &[
        "unused_imports",
        "unused_variables",
        "unused_assignments",
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
    run_compiler(rustc_args, true, true, &mut callbacks)
}

pub struct VerusRoot {
    pub path: std::path::PathBuf,
    in_vargo: bool,
}

pub fn find_verusroot() -> Option<VerusRoot> {
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
        .or_else(|| {
            let current_exe = std::env::current_exe().ok()
                .and_then(|c| {
                    if c.symlink_metadata().ok()?.is_symlink() {
                        std::fs::read_link(c).ok()
                    } else {
                        Some(c)
                    }
                });
            current_exe.and_then(|current| {
                current.parent().and_then(|p| {
                    let mut path = std::path::PathBuf::from(&p);
                    if path.join("verus-root").is_file() {
                        if !path.is_absolute() {
                            path =
                                std::env::current_dir().expect("working directory invalid").join(path);
                        }
                        Some(VerusRoot { path, in_vargo: false })
                    } else {
                        // TODO suppress warning when building verus itself
                        eprintln!("warning: did not find a valid verusroot; continuing, but the verus_builtin and vstd crates are likely missing");
                        None
                    }
                })
            })
        })
}

pub fn run(
    verifier: Verifier,
    mut rustc_args: Vec<String>,
    verus_root: Option<VerusRoot>,
    build_test_mode: bool,
) -> (Verifier, Stats, Result<(), ()>) {
    if !rustc_args.iter().any(|a| a.starts_with("--edition")) {
        rustc_args.push(format!("--edition"));
        rustc_args.push(format!("2021"));
    }
    // TODO simplify
    let verus_externs = if !build_test_mode {
        if let Some(VerusRoot { path: verusroot, in_vargo }) = verus_root {
            let externs = VerusExterns {
                verus_root: verusroot.clone(),
                has_vstd: verifier.args.vstd == Vstd::Imported,
                has_builtin: !matches!(verifier.args.vstd, Vstd::IsCore | Vstd::ImportedViaCore),
            };
            rustc_args.extend(externs.to_args());
            if in_vargo && !std::env::var("VERUS_Z3_PATH").is_ok() {
                panic!("we are in vargo, but VERUS_Z3_PATH is not set; this is a bug");
            }
            if !in_vargo { Some(externs) } else { None }
        } else {
            None
        }
    } else {
        None
    };

    let time0 = Instant::now();
    let mut rustc_args_verify = rustc_args.clone();
    rustc_args_verify.extend(["--cfg", "verus_keep_ghost"].map(|s| s.to_string()));
    rustc_args_verify.extend(["--cfg", "verus_keep_ghost_body"].map(|s| s.to_string()));
    if matches!(verifier.args.vstd, Vstd::IsCore | Vstd::ImportedViaCore) {
        rustc_args_verify.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    }
    // Build VIR and run verification
    let mut verifier_callbacks = VerifierCallbacksEraseMacro {
        verifier,
        rust_start_time: Instant::now(),
        rust_end_time: None,
        tc_start_time: None,
        tc_end_time: None,
        rustc_args: rustc_args.clone(),
        verus_externs,
        spans: None,
    };
    let status = run_compiler(rustc_args_verify.clone(), true, false, &mut verifier_callbacks);
    let VerifierCallbacksEraseMacro {
        verifier,
        rust_start_time,
        rust_end_time,
        tc_start_time,
        tc_end_time,
        ..
    } = verifier_callbacks;
    let time1 = Instant::now();
    let time_trait_conflicts = match (tc_start_time, tc_end_time) {
        (Some(t1), Some(t2)) => t2 - t1,
        _ => Duration::new(0, 0),
    };

    let time_rustc = match rust_end_time {
        Some(t1) => t1 - rust_start_time,
        _ => Duration::new(0, 0),
    };

    if status.is_err() || verifier.encountered_vir_error {
        return (
            verifier,
            Stats {
                time_rustc,
                time_verify: (time1 - time0) - time_trait_conflicts,
                time_trait_conflicts,
                time_compile: Duration::new(0, 0),
            },
            Err(()),
        );
    }

    let compile_status = if !verifier.compile && verifier.args.no_lifetime {
        Ok(())
    } else {
        run_with_erase_macro_compile(rustc_args, verifier.compile, verifier.args.vstd)
    };

    let time2 = Instant::now();

    let stats = Stats {
        time_rustc,
        time_verify: (time1 - time0) - time_trait_conflicts,
        time_trait_conflicts,
        time_compile: time2 - time1,
    };

    // Run borrow checker and compiler with #[exec] (not #[proof])
    if let Err(_) = compile_status {
        return (verifier, stats, Err(()));
    }

    (verifier, stats, Ok(()))
}
