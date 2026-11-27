use crate::config::Vstd;
use crate::externs::VerusExterns;
use crate::verifier::{Verifier, VerifierCallbacksEraseMacro};
use rustc_hir::attrs::AttributeKind;
use rustc_hir::{Attribute, AttributeMap};
use rustc_hir::{HirId, ItemKind, OwnerId, OwnerNode};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::{OutFileName, OutputType};
use rustc_span::{Span, sym};
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
        && verifier.args.verify_only_module.is_empty()
        && !verifier.args.verify_root
}

// Call Rust's mir_borrowck to check lifetimes of #[spec] and #[proof] code and variables

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
        rustc_hir_analysis::check_crate(queries);
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
    pub override_stability: bool,
    pub second_pass_dep_info: Option<std::path::PathBuf>,
}

impl rustc_driver::Callbacks for CompilerCallbacksEraseMacro {
    // Adding `override_stability` and `stable_attr` functions is a hacky solution specifically for verifying core,
    // to fix an issue with stability attributes.
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        if self.override_stability {
            config.override_queries = Some(|_session, providers| {
                providers.queries.hir_attr_map = |tcx, owner_id| {
                    let mut map = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.hir_attr_map)(
                        tcx, owner_id,
                    );
                    if needs_stable_attr(tcx, owner_id) && !has_stable_attr(&map, owner_id) {
                        map = add_stable_attr(tcx, owner_id, map);
                    }
                    map
                };
            });
        }
    }

    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        if tcx.sess.opts.output_types.contains_key(&OutputType::DepInfo) {
            if let OutFileName::Real(path) = tcx.output_filenames(()).path(OutputType::DepInfo) {
                self.second_pass_dep_info = Some(path);
            }
        }
        rustc_driver::Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        _tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        if self.do_compile {
            rustc_driver::Compilation::Continue
        } else {
            rustc_driver::Compilation::Stop
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
    /// time for lifetime/borrow checking
    pub time_trait_conflicts: Duration,
    /// compilation time
    pub time_compile: Duration,
}

pub const ERASE_DRIVER_ARG: &'static str = "--internal-erase-compile-driver";

fn vstd_to_str(vstd: Vstd) -> &'static str {
    match vstd {
        Vstd::IsVstd => "IsVstd",
        Vstd::NoVstd => "NoVstd",
        Vstd::Imported => "Imported",
        Vstd::IsCore => "IsCore",
        Vstd::ImportedViaCore => "ImportedViaCore",
    }
}

/// The environment variable that names the file in which the subprocess spawned by
/// `run_with_erase_macro_compile` records the path of the dep-info file it wrote, if any
const ERASE_DEP_INFO_OUT_VAR: &str = "VERUS_ERASE_DEP_INFO_OUT";

/// Entry point of the subprocess spawned by `run_with_erase_macro_compile`:
/// `verus ERASE_DRIVER_ARG <do_compile 0|1> <vstd> <rustc args...>`.
pub fn erase_compile_driver(args: &[String]) -> ! {
    let do_compile = args[0] == "1";
    let vstd = match args[1].as_str() {
        "IsVstd" => Vstd::IsVstd,
        "NoVstd" => Vstd::NoVstd,
        "Imported" => Vstd::Imported,
        "IsCore" => Vstd::IsCore,
        "ImportedViaCore" => Vstd::ImportedViaCore,
        other => panic!("erase_compile_driver: unknown vstd mode {other}"),
    };
    let rustc_args = args[2..].to_vec();
    let r = run_with_erase_macro_compile_in_process(rustc_args, do_compile, vstd);
    if let (Ok(Some(dep_info)), Ok(out)) = (&r, std::env::var(ERASE_DEP_INFO_OUT_VAR)) {
        if std::fs::write(&out, dep_info.as_os_str().as_encoded_bytes()).is_err() {
            std::process::exit(1);
        }
    }
    std::process::exit(if r.is_ok() { 0 } else { 1 })
}

/// The erased compilation re-expands every macro. Proc macros may keep global state between
/// invocations (enum_dispatch records trait and enum definitions, for example), and in the
/// process that just ran the verification pass that state is no longer fresh, so the second
/// expansion could differ from the first. Running the pass in a new process gives it the
/// same starting state as the verification pass (and as a plain `rustc` run).
/// `VERUS_ERASE_IN_PROCESS=1` restores the old in-process behaviour.
pub(crate) fn run_with_erase_macro_compile(
    rustc_args: Vec<String>,
    do_compile: bool,
    vstd: Vstd,
) -> Result<Option<std::path::PathBuf>, ()> {
    if std::env::var("VERUS_ERASE_IN_PROCESS").as_deref() == Ok("1") {
        return run_with_erase_macro_compile_in_process(rustc_args, do_compile, vstd);
    }
    let Ok(exe) = std::env::current_exe() else {
        return run_with_erase_macro_compile_in_process(rustc_args, do_compile, vstd);
    };
    // the subprocess writes the path of its dep-info file (if it wrote one) to this file
    let dep_info_out = std::env::temp_dir().join(format!(
        "verus-erase-dep-info-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    let status = std::process::Command::new(exe)
        .arg(ERASE_DRIVER_ARG)
        .arg(if do_compile { "1" } else { "0" })
        .arg(vstd_to_str(vstd))
        .args(&rustc_args)
        .env(ERASE_DEP_INFO_OUT_VAR, &dep_info_out)
        .status();
    let dep_info = std::fs::read(&dep_info_out).ok();
    let _ = std::fs::remove_file(&dep_info_out);
    match status {
        Ok(s) if s.success() => Ok(dep_info.map(|bytes| {
            // SAFETY: the bytes were written by `erase_compile_driver` with `as_encoded_bytes`,
            // on the same platform
            std::path::PathBuf::from(unsafe {
                std::ffi::OsString::from_encoded_bytes_unchecked(bytes)
            })
        })),
        _ => Err(()),
    }
}

fn run_with_erase_macro_compile_in_process(
    mut rustc_args: Vec<String>,
    do_compile: bool,
    vstd: Vstd,
) -> Result<Option<std::path::PathBuf>, ()> {
    let mut callbacks = CompilerCallbacksEraseMacro {
        do_compile,
        override_stability: matches!(vstd, Vstd::IsCore | Vstd::ImportedViaCore),
        second_pass_dep_info: None,
    };
    rustc_args.extend(["--cfg", "verus_only", "--cfg", "verus_keep_ghost"].map(|s| s.to_string()));
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
        "non_shorthand_field_patterns", // The verus macro rewrites the shorthand syntax `MyStruct { field_name }`
                                        // to `MyStruct { field_name: field_name }`, which triggers this lint warning
    ];
    for a in allow {
        rustc_args.extend(["-A", a].map(|s| s.to_string()));
    }
    run_compiler(rustc_args, true, true, &mut callbacks)?;
    Ok(callbacks.second_pass_dep_info)
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
            let current_exe = std::env::current_exe().ok().and_then(|c| {
                if c.symlink_metadata().ok()?.is_symlink() {
                    std::fs::read_link(c).ok()
                } else {
                    Some(c)
                }
            });
            current_exe.and_then(|current| {
                current.parent().and_then(|p| {
                    let mut path = std::path::PathBuf::from(&p);
                    if let Err(missing) =
                        cargo_verus_toolchains::installed::check_required_artifacts(&path)
                    {
                        eprintln!("warning: Verus installation is incomplete; missing components:");
                        for path in missing {
                            eprintln!("  {}", path.display());
                        }
                        None
                    } else {
                        if !path.is_absolute() {
                            path = std::env::current_dir()
                                .expect("working directory invalid")
                                .join(path);
                        }
                        Some(VerusRoot { path, in_vargo: false })
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
    rustc_args_verify.extend(["--cfg", "verus_only"].map(|s| s.to_string()));
    rustc_args_verify.extend(["--cfg", "verus_keep_ghost"].map(|s| s.to_string()));
    rustc_args_verify.extend(["--cfg", "verus_keep_ghost_body"].map(|s| s.to_string()));
    if matches!(verifier.args.vstd, Vstd::IsCore | Vstd::ImportedViaCore) {
        rustc_args_verify.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    }
    // Build VIR and run verification
    let mut verifier_callbacks = VerifierCallbacksEraseMacro {
        first_pass_dep_info: None,
        verifier,
        rust_start_time: Instant::now(),
        rust_end_time: None,
        tc_start_time: None,
        tc_end_time: None,
        verus_externs,
        spans: None,
        unresolved_import_deps: std::collections::HashSet::new(),
    };
    let first_pass_result =
        run_compiler(rustc_args_verify.clone(), true, false, &mut verifier_callbacks);
    let VerifierCallbacksEraseMacro {
        verifier,
        rust_start_time,
        rust_end_time,
        tc_start_time,
        tc_end_time,
        first_pass_dep_info,
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

    let first_pass_failed = first_pass_result.is_err() || verifier.encountered_vir_error;
    let second_pass_result = if first_pass_failed {
        Err(())
    } else if verifier.has_second_compile_pass() {
        let do_compile = verifier.compile || verifier.via_cargo_args.is_some();
        run_with_erase_macro_compile(rustc_args, do_compile, verifier.args.vstd)
    } else {
        Ok(None)
    };

    let time2 = if first_pass_failed { time1 } else { Instant::now() };

    // Rustc writes dep-info after after_expansion, so combine files after the passes return.
    let second_pass_dep_info = second_pass_result.as_ref().ok().and_then(|path| path.as_ref());
    let dep_info_result = combine_dep_info(
        first_pass_dep_info.as_deref(),
        second_pass_dep_info.map(|path| path.as_path()),
    );

    let stats = Stats {
        time_rustc,
        time_verify: (time1 - time0) - time_trait_conflicts,
        time_trait_conflicts,
        time_compile: time2 - time1,
    };

    if let Err(err) = dep_info_result {
        eprintln!("error: {err}");
        return (verifier, stats, Err(()));
    }

    // Run borrow checker and compiler with #[exec] (not #[proof])
    if let Err(_) = second_pass_result {
        return (verifier, stats, Err(()));
    }

    (verifier, stats, Ok(()))
}

fn combine_dep_info(
    first_pass_dep_info: Option<&std::path::Path>,
    second_pass_dep_info: Option<&std::path::Path>,
) -> Result<(), String> {
    use crate::verifier::rename_first_pass_dep_info;

    match (first_pass_dep_info, second_pass_dep_info) {
        (Some(original_first), Some(second)) => {
            let renamed_first = rename_first_pass_dep_info(original_first);
            let info_1 = rustc_dep_info::Contents::read_file(&renamed_first).map_err(|err| {
                format!(
                    "failed to read first-pass dep-info from `{}`: {err}",
                    renamed_first.display()
                )
            })?;
            let info_2 = rustc_dep_info::Contents::read_file(&second).map_err(|err| {
                format!("failed to read second-pass dep-info from `{}`: {err}", second.display())
            })?;
            // Shared dependencies must not change between verification and compilation.
            let mut checksums_changed = false;
            let mut env_vars_changed = false;
            let merged = info_1.merge(
                info_2,
                |source, meta_1, meta_2| {
                    if meta_1 != meta_2 {
                        checksums_changed = true;
                        eprintln!("dep-info checksum changed between `rustc` passes: {source}");
                    }
                    meta_1
                },
                |key, val_1, val_2| {
                    if val_1 != val_2 {
                        env_vars_changed = true;
                        eprintln!("dep-info env var changed between `rustc` passes: {key}");
                    }
                    val_1
                },
            );
            if checksums_changed || env_vars_changed {
                return Err(format!(
                    "dep-info changes were detected between `rustc` passes, for details compare {} and {}",
                    renamed_first.display(),
                    second.display()
                ));
            }
            merged.write_file(&second).map_err(|err| {
                format!("failed to write combined dep-info to `{}`: {err}", second.display())
            })?;
            std::fs::remove_file(&renamed_first).unwrap_or_else(|err| {
                eprintln!("warning: failed to remove `{}`: {err}", renamed_first.display())
            });
        }
        (Some(original_first), None) => {
            let renamed_first = rename_first_pass_dep_info(original_first);
            std::fs::rename(renamed_first, original_first).map_err(|err| {
                format!("failed to restore dep-info `{}`: {err}", original_first.display())
            })?;
        }
        (None, Some(second)) => {
            return Err(format!(
                "second-pass dep-info `{}` has no corresponding first-pass dep-info",
                second.display()
            ));
        }
        (None, None) => {}
    }
    Ok(())
}

fn stable_attr(span: Span) -> Attribute {
    use rustc_hir::*;
    Attribute::Parsed(AttributeKind::Stability {
        stability: Stability {
            level: StabilityLevel::Unstable {
                reason: rustc_hir::attrs::UnstableReason::Default,
                issue: None,
                implied_by: None,
                old_name: None,
            },
            feature: sym::rustc_private,
        },
        span,
    })
}

fn has_stable_attr(attrmap: &AttributeMap, owner_id: OwnerId) -> bool {
    let hir_id = HirId::from(owner_id);
    match attrmap.map.get(&hir_id.local_id) {
        None => false,
        Some(attrs) => {
            attrs.iter().any(|a| matches!(a, Attribute::Parsed(AttributeKind::Stability { .. })))
        }
    }
}

fn add_stable_attr<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_id: OwnerId,
    attrmap: &'tcx AttributeMap,
) -> &'tcx AttributeMap<'tcx> {
    let hir_id = HirId::from(owner_id);

    let mut m = AttributeMap {
        map: attrmap.map.clone(),
        define_opaque: attrmap.define_opaque.clone(),
        opt_hash: attrmap.opt_hash.clone(),
    };

    let mut attrs = match m.map.get(&hir_id.local_id) {
        None => vec![],
        Some(attrs) => attrs.to_vec(),
    };

    let span = tcx.hir_span(hir_id);
    attrs.push(stable_attr(span));

    m.map.insert(hir_id.local_id, Box::leak(attrs.into_boxed_slice()));
    Box::leak(Box::new(m))
}

fn needs_stable_attr<'tcx>(tcx: TyCtxt<'tcx>, owner_id: OwnerId) -> bool {
    let owner = tcx.hir_owner_node(owner_id);
    match owner {
        OwnerNode::Item(_item) => true,
        OwnerNode::ForeignItem(_item) => false,
        OwnerNode::TraitItem(_item) => true,
        OwnerNode::ImplItem(_item) => {
            let hir_id = HirId::from(owner_id);
            let parent = tcx.hir_get_parent_item(hir_id);
            match tcx.hir_owner_node(parent) {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Impl(impll) => !impll.of_trait.is_some(),
                    _ => panic!("add_stable_attr"),
                },
                _ => panic!("add_stable_attr"),
            }
        }
        OwnerNode::Crate(_item) => false,
        OwnerNode::Synthetic => false,
    }
}
