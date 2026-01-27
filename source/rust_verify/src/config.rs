use air::context::SmtSolver;
use getopts::Options;
use std::{collections::HashSet, sync::Arc};
use vir::printer::ToDebugSNodeOpts as VirLogOption;

pub const DEFAULT_RLIMIT_SECS: f32 = 10f32;

#[derive(Debug, Clone, Copy)]
pub enum ShowTriggers {
    Silent,
    Selective,
    Module,
    AllModules,
    Verbose,
    VerboseAllModules,
}
impl Default for ShowTriggers {
    fn default() -> Self {
        ShowTriggers::Selective
    }
}

pub const LOG_DIR: &str = ".verus-log";
pub const SOLVER_LOG_DIR: &str = ".verus-solver-log";
pub const VIR_FILE_SUFFIX: &str = ".vir";
pub const VIR_SIMPLE_FILE_SUFFIX: &str = "-simple.vir";
pub const VIR_POLY_FILE_SUFFIX: &str = "-poly.vir";
pub const VIR_SST_FILE_SUFFIX: &str = "-sst.vir";
pub const TRAIT_CONFLICT_FILE_SUFFIX: &str = "-trait-conflicts.rs";
pub const INTERPRETER_FILE_SUFFIX: &str = ".interp";
pub const AIR_INITIAL_FILE_SUFFIX: &str = ".air";
pub const AIR_FINAL_FILE_SUFFIX: &str = "-final.air";
pub const SMT_FILE_SUFFIX: &str = ".smt2";
pub const SMT_TRANSCRIPT_FILE_SUFFIX: &str = ".smt_transcript";
pub const PROFILE_FILE_SUFFIX: &str = ".profile";
pub const SINGULAR_FILE_SUFFIX: &str = ".singular";
pub const TRIGGERS_FILE_SUFFIX: &str = ".triggers";
pub const CALL_GRAPH_FILE_SUFFIX_FULL_INITIAL: &str = "-call-graph-full-initial.dot";
pub const CALL_GRAPH_FILE_SUFFIX_FULL_SIMPLIFIED: &str = "-call-graph-full-simplified.dot";
pub const CALL_GRAPH_FILE_SUFFIX_NOSTD_INITIAL: &str = "-call-graph-nostd-initial.dot";
pub const CALL_GRAPH_FILE_SUFFIX_NOSTD_SIMPLIFIED: &str = "-call-graph-nostd-simplified.dot";

#[derive(Debug, Default)]
pub struct LogArgs {
    pub log_vir: bool,
    pub log_vir_simple: bool,
    pub log_vir_poly: bool,
    pub log_vir_sst: bool,
    pub vir_log_option: VirLogOption,
    pub log_trait_conflicts: bool,
    pub log_interpreter: bool,
    pub log_air_initial: bool,
    pub log_air_final: bool,
    pub log_smt: bool,
    pub log_smt_transcript: bool,
    pub log_triggers: bool,
    pub log_call_graph: bool,
}

/// Describes the relationship between this crate and vstd.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Vstd {
    /// The current crate is vstd.
    IsVstd,
    /// There is no vstd (only verus_builtin). Really only used for testing.
    NoVstd,
    /// Imports the vstd crate like usual.
    Imported,
    /// Embed vstd and verus_builtin as modules, necessary for verifying the `core` library.
    IsCore,
    /// For other crates in stdlib verification that import core
    ImportedViaCore,
}

#[derive(Debug)]
pub struct ArgsX {
    pub export: Option<String>,
    pub import: Vec<(String, String)>,
    pub verify_root: bool,
    pub verify_module: Vec<String>,
    pub verify_only_module: Vec<String>,
    pub verify_function: Option<String>,
    pub no_external_by_default: bool,
    pub no_verify: bool,
    pub no_lifetime: bool,
    pub no_auto_recommends_check: bool,
    pub no_cheating: bool,
    pub time: bool,
    pub time_expanded: bool,
    pub output_json: bool,
    pub rlimit: f32,
    pub smt_options: Vec<(String, String)>,
    pub multiple_errors: u32,
    pub expand_errors: bool,
    pub log_dir: Option<String>,
    pub log_all: bool,
    pub log_args: LogArgs,
    pub show_triggers: ShowTriggers,
    pub ignore_unexpected_smt: bool,
    pub allow_inline_air: bool,
    pub debugger: bool,
    pub profile: bool,
    pub profile_all: bool,
    pub capture_profiles: bool,
    pub spinoff_all: bool,
    pub use_internal_profiler: bool,
    pub vstd: Vstd,
    pub compile: bool,
    pub solver_version_check: bool,
    pub version: bool,
    pub num_threads: usize,
    pub trace: bool,
    pub report_long_running: bool,
    pub use_crate_name: bool,
    pub solver: SmtSolver,
    pub axiom_usage_info: bool,
    pub check_api_safety: bool,
    pub new_mut_ref: bool,
    pub no_bv_simplify: bool,
}

impl ArgsX {
    pub fn new() -> Self {
        Self {
            export: Default::default(),
            import: Default::default(),
            verify_root: Default::default(),
            verify_module: Default::default(),
            verify_only_module: Default::default(),
            verify_function: Default::default(),
            no_external_by_default: Default::default(),
            no_verify: Default::default(),
            no_lifetime: Default::default(),
            no_auto_recommends_check: Default::default(),
            no_cheating: Default::default(),
            time: Default::default(),
            time_expanded: Default::default(),
            output_json: Default::default(),
            rlimit: f32::INFINITY, // NOTE: default rlimit is infinity
            smt_options: Default::default(),
            multiple_errors: Default::default(),
            expand_errors: Default::default(),
            log_dir: Default::default(),
            log_all: Default::default(),
            log_args: Default::default(),
            show_triggers: Default::default(),
            ignore_unexpected_smt: Default::default(),
            allow_inline_air: Default::default(),
            debugger: Default::default(),
            profile: Default::default(),
            profile_all: Default::default(),
            capture_profiles: Default::default(),
            spinoff_all: Default::default(),
            use_internal_profiler: Default::default(),
            vstd: Vstd::Imported,
            compile: Default::default(),
            solver_version_check: Default::default(),
            version: Default::default(),
            num_threads: Default::default(),
            trace: Default::default(),
            report_long_running: Default::default(),
            use_crate_name: Default::default(),
            solver: Default::default(),
            axiom_usage_info: Default::default(),
            check_api_safety: Default::default(),
            new_mut_ref: Default::default(),
            no_bv_simplify: Default::default(),
        }
    }
}

pub type Args = Arc<ArgsX>;

pub struct CargoVerusArgsX {
    pub compile_when_primary_package: bool,
    pub compile_when_not_primary_package: bool,
    pub import_dep_if_present: Vec<String>,
}

impl CargoVerusArgsX {
    pub fn new() -> Self {
        Self {
            compile_when_primary_package: false,
            compile_when_not_primary_package: false,
            import_dep_if_present: Default::default(),
        }
    }
}

pub type CargoVerusArgs = Arc<CargoVerusArgsX>;

pub fn enable_default_features_and_verus_attr(
    rustc_args: &mut Vec<String>,
    syntax_macro: bool,
    _erase_ghost: bool,
) {
    if syntax_macro {
        // REVIEW: syntax macro adds superfluous parentheses and braces
        for allow in
            &["unused_parens", "unused_braces", "unconditional_panic", "arithmetic_overflow"]
        {
            rustc_args.push("-A".to_string());
            rustc_args.push(allow.to_string());
        }
    }
    for allow in &["unused_imports", "unused_mut"] {
        rustc_args.push("-A".to_string());
        rustc_args.push(allow.to_string());
    }
    rustc_args.push("-Zcrate-attr=allow(internal_features)".to_string());
    for feature in &[
        "stmt_expr_attributes",
        "box_patterns",
        "negative_impls",
        "rustc_attrs",
        "unboxed_closures",
        "register_tool",
        "tuple_trait",
        "custom_inner_attributes",
        "try_trait_v2",
    ] {
        rustc_args.push("-Z".to_string());
        rustc_args.push(format!("crate-attr=feature({})", feature));
    }

    rustc_args.push("-Zcrate-attr=register_tool(verus)".to_string());
    rustc_args.push("-Zcrate-attr=register_tool(verifier)".to_string());
    rustc_args.push("-Zcrate-attr=register_tool(verusfmt)".to_string());
}

fn error(msg: String) -> ! {
    eprintln!("Error: {}", msg);
    std::process::exit(-1)
}

fn parse_opts_or_pairs(strs: Vec<String>) -> std::collections::HashMap<String, Option<String>> {
    let mut parsed: std::collections::HashMap<String, Option<String>> =
        std::collections::HashMap::new();
    for o in strs {
        let oo: Vec<_> = o.split("=").collect();
        match &oo[..] {
            [opt] => parsed.insert((*opt).to_owned(), None),
            [key, val] => parsed.insert((*key).to_owned(), Some((*val).to_owned())),
            _ => {
                error(format!("invalid parsed option -V {}", o));
            }
        };
    }
    parsed
}

pub fn parse_cargo_args(_program: &String, args: &mut Vec<String>) -> CargoVerusArgs {
    let mut cargo_verus_args = CargoVerusArgsX::new();

    const CARGO_OPT_COMPILE_WHEN_PRIMARY: &str = "compile-when-primary-package";
    const CARGO_OPT_COMPILE_WHEN_NOT_PRIMARY: &str = "compile-when-not-primary-package";
    const CARGO_OPT_IMPORT_DEP_IF_PRESENT: &str = "import-dep-if-present";

    let mut next_is_via_cargo = false;
    args.retain(|arg| {
        if arg == "--VIA-CARGO" {
            next_is_via_cargo = true;
            false
        } else if next_is_via_cargo {
            if arg == CARGO_OPT_COMPILE_WHEN_PRIMARY {
                cargo_verus_args.compile_when_primary_package = true;
            } else if arg == CARGO_OPT_COMPILE_WHEN_NOT_PRIMARY {
                cargo_verus_args.compile_when_not_primary_package = true;
            } else if arg.starts_with(CARGO_OPT_IMPORT_DEP_IF_PRESENT) {
                let oo: Vec<_> = arg.split("=").collect();
                if let [_, val] = &oo[..] {
                    cargo_verus_args.import_dep_if_present.push(val.to_string());
                } else {
                    error(format!(
                        "expected --VIA-CARGO {}=DEP_NAME",
                        CARGO_OPT_IMPORT_DEP_IF_PRESENT
                    ));
                }
            } else {
                error(format!("unexpected --VIA-CARGO {}", arg));
            }
            next_is_via_cargo = false;
            false
        } else {
            true
        }
    });

    Arc::new(cargo_verus_args)
}

pub fn parse_args_with_imports(
    program: &String,
    args: impl Iterator<Item = String>,
    vstd_import: Option<(String, String)>,
) -> (Args, Vec<String>) {
    const OPT_EXPORT: &str = "export";
    const OPT_IMPORT: &str = "import";
    const OPT_VERIFY_ROOT: &str = "verify-root";
    const OPT_VERIFY_MODULE: &str = "verify-module";
    const OPT_VERIFY_ONLY_MODULE: &str = "verify-only-module";
    const OPT_VERIFY_FUNCTION: &str = "verify-function";
    const OPT_NO_EXTERNAL_BY_DEFAULT: &str = "no-external-by-default";
    const OPT_NO_VERIFY: &str = "no-verify";
    const OPT_NO_LIFETIME: &str = "no-lifetime";
    const OPT_NO_AUTO_RECOMMENDS_CHECK: &str = "no-auto-recommends-check";
    const OPT_NO_CHEATING: &str = "no-cheating";
    const OPT_TIME: &str = "time";
    const OPT_TIME_EXPANDED: &str = "time-expanded";
    const OPT_OUTPUT_JSON: &str = "output-json";
    const OPT_RLIMIT: &str = "rlimit";
    const OPT_SMT_OPTION: &str = "smt-option";
    const OPT_MULTIPLE_ERRORS: &str = "multiple-errors";
    const OPT_NO_VSTD: &str = "no-vstd";
    const OPT_IS_VSTD: &str = "is-vstd";
    const OPT_IS_CORE: &str = "is-core";
    const OPT_IS_STDLIB_OUTSIDE_OF_CORE: &str = "is-stdlib-outside-of-core";
    const OPT_EXPAND_ERRORS: &str = "expand-errors";

    const OPT_LOG_DIR: &str = "log-dir";
    const OPT_LOG_ALL: &str = "log-all";
    const OPT_LOG_MULTI: &str = "log";

    const LOG_VIR: &str = "vir";
    const LOG_VIR_SIMPLE: &str = "vir-simple";
    const LOG_VIR_POLY: &str = "vir-poly";
    const LOG_VIR_SST: &str = "vir-sst";
    const LOG_VIR_OPTION: &str = "vir-option";
    const LOG_TRAIT_CONFLICTS: &str = "trait-conflits";
    const LOG_INTERPRETER: &str = "interpreter";
    const LOG_AIR: &str = "air";
    const LOG_AIR_FINAL: &str = "air-final";
    const LOG_SMT: &str = "smt";
    const LOG_SMT_TRANSCRIPT: &str = "smt-transcript";
    const LOG_TRIGGERS: &str = "triggers";
    const LOG_CALL_GRAPH: &str = "call-graph";

    const LOG_ITEMS: &[(&str, &str)] = &[
        (LOG_VIR, "Log VIR"),
        (LOG_VIR_SIMPLE, "Log simplified VIR"),
        (LOG_VIR_POLY, "Log poly VIR"),
        (LOG_VIR_SST, "Log SST"),
        (
            LOG_VIR_OPTION,
            "Set VIR logging option (e.g. `--log vir-option=no_span+no_type`. Available options: `compact` `no_span` `no_type` `no_encoding` `no_fn_details`) (default: verbose)",
        ),
        (LOG_TRAIT_CONFLICTS, "Log trait-conflict-checking for --erasure macro"),
        (LOG_INTERPRETER, "Log assert_by_compute's interpreter progress"),
        (LOG_AIR, "Log AIR queries in initial form"),
        (LOG_AIR_FINAL, "Log AIR queries in final form"),
        (LOG_SMT, "Log SMT queries"),
        (LOG_SMT_TRANSCRIPT, "Log complete SMT transcript"),
        (LOG_TRIGGERS, "Log automatically chosen triggers"),
        (LOG_CALL_GRAPH, "Log the call graph"),
    ];

    const OPT_TRIGGERS: &str = "triggers";
    const OPT_TRIGGERS_MODE: &str = "triggers-mode";

    const TRIGGERS_MODE_SILENT: &str = "silent";
    const TRIGGERS_MODE_SELECTIVE: &str = "selective";
    const TRIGGERS_MODE_ALL_MODULES: &str = "all-modules";
    const TRIGGERS_MODE_VERBOSE: &str = "verbose";
    const TRIGGERS_MODE_VERBOSE_ALL_MODULES: &str = "verbose-all-modules";

    const TRIGGERS_MODE_ITEMS: &[(&str, &str)] = &[
        (TRIGGERS_MODE_SILENT, "Do not show automatically chosen triggers"),
        (
            TRIGGERS_MODE_SELECTIVE,
            "Show automatically chosen triggers for some potentially ambiguous cases in verified modules (this is the default behavior)",
        ),
        (
            TRIGGERS_MODE_ALL_MODULES,
            "Show all automatically chosen triggers for verified modules and imported definitions from other modules",
        ),
        (TRIGGERS_MODE_VERBOSE, "Show all triggers (manually or auto) for verified modules"),
        (
            TRIGGERS_MODE_VERBOSE_ALL_MODULES,
            "Show all triggers (manually or automatically chosen) for verified modules and imported definitions from other modules",
        ),
    ];

    const OPT_PROFILE: &str = "profile";
    const OPT_PROFILE_ALL: &str = "profile-all";
    const OPT_COMPILE: &str = "compile";
    const OPT_VERSION: &str = "version";
    const OPT_RECORD: &str = "record";
    const OPT_NUM_THREADS: &str = "num-threads";
    const OPT_TRACE: &str = "trace";
    const OPT_NO_REPORT_LONG_RUNNING: &str = "no-report-long-running";

    const OPT_EXTENDED_MULTI: &str = "V";
    const EXTENDED_IGNORE_UNEXPECTED_SMT: &str = "ignore-unexpected-smt";
    const EXTENDED_DEBUG: &str = "debug";
    const EXTENDED_NO_SOLVER_VERSION_CHECK: &str = "no-solver-version-check";
    const EXTENDED_SPINOFF_ALL: &str = "spinoff-all";
    const EXTENDED_CAPTURE_PROFILES: &str = "capture-profiles";
    const EXTENDED_USE_INTERNAL_PROFILER: &str = "use-internal-profiler";
    const EXTENDED_CVC5: &str = "cvc5";
    const EXTENDED_ALLOW_INLINE_AIR: &str = "allow-inline-air";
    const EXTENDED_USE_CRATE_NAME: &str = "use-crate-name";
    const EXTENDED_AXIOM_USAGE_INFO: &str = "axiom-usage-info";
    const EXTENDED_CHECK_API_SAFETY: &str = "check-api-safety";
    const EXTENDED_NEW_MUT_REF: &str = "new-mut-ref";
    const EXTENDED_NO_BV_SIMPLIFY: &str = "no-bv-simplify";
    const EXTENDED_KEYS: &[(&str, &str)] = &[
        (EXTENDED_IGNORE_UNEXPECTED_SMT, "Ignore unexpected SMT output"),
        (EXTENDED_DEBUG, "Enable debugging of proof failures"),
        (
            EXTENDED_NO_SOLVER_VERSION_CHECK,
            "Skip the check that the solver has the expected version (useful to experiment with different versions of z3)",
        ),
        (EXTENDED_SPINOFF_ALL, "Always spinoff individual functions to separate z3 instances"),
        (
            EXTENDED_CAPTURE_PROFILES,
            "Always collect prover performance data, but don't generate output reports",
        ),
        (
            EXTENDED_USE_INTERNAL_PROFILER,
            "Use an internal profiler that shows internal quantifier instantiations",
        ),
        (EXTENDED_CVC5, "Use the cvc5 SMT solver, rather than the default (Z3)"),
        (EXTENDED_ALLOW_INLINE_AIR, "Allow the POTENTIALLY UNSOUND use of inline_air_stmt"),
        (
            EXTENDED_USE_CRATE_NAME,
            "Use the crate name in paths (useful when verifying vstd without --export)",
        ),
        (EXTENDED_AXIOM_USAGE_INFO, "Print usage info for broadcasted axioms, lemmas, and groups"),
        (
            EXTENDED_CHECK_API_SAFETY,
            "Check that the API is memory-safe when called from unverified, safe Rust code. Experimental.",
        ),
        (EXTENDED_NEW_MUT_REF, "incomplete feature for developers only; do not use"),
        (
            EXTENDED_NO_BV_SIMPLIFY,
            "internal option to disable simplification of bit-vector assertions before sending to the SMT solver",
        ),
    ];

    let default_num_threads: usize = std::thread::available_parallelism()
        .map(|x| std::cmp::max(usize::from(x) - 1, 1))
        .unwrap_or(1);

    let mut opts = Options::new();
    opts.optflag(
        "",
        OPT_VERSION,
        "Print version information (add `--output-json` to print as json) ",
    );
    opts.optopt("", OPT_EXPORT, "Export Verus metadata for library crate", "CRATENAME=PATH");
    opts.optmulti("", OPT_IMPORT, "Import Verus metadata from library crate", "CRATENAME=PATH");
    opts.optflag("", OPT_VERIFY_ROOT, "Verify just the root module of crate");
    opts.optmulti(
        "",
        OPT_VERIFY_MODULE,
        "Verify just one submodule and its descendants within the crate (e.g. 'foo' or 'foo::bar'), can be repeated to verify only certain modules",
        "MODULE",
    );
    opts.optmulti(
        "",
        OPT_VERIFY_ONLY_MODULE,
        "Verify just one submodule (excluding its descendants) within the crate (e.g. 'foo' or 'foo::bar'), can be repeated to verify only certain modules",
        "MODULE",
    );
    opts.optopt(
        "",
        OPT_VERIFY_FUNCTION,
        "Verify just one function within the one module specified by verify-module or verify-root, \nmatches on unique substring (foo) or wildcards at ends of the argument (*foo, foo*, *foo*)",
        "MODULE",
    );
    opts.optflag("", OPT_NO_EXTERNAL_BY_DEFAULT, "(deprecated) Verify all items, even those declared outside the verus! macro, and even if they aren't marked #[verifier::verify]");
    opts.optflag("", OPT_NO_VERIFY, "Do not run verification");
    opts.optflag("", OPT_NO_LIFETIME, "Do not run lifetime checking on proofs");
    opts.optflag(
        "",
        OPT_NO_AUTO_RECOMMENDS_CHECK,
        "Do not automatically check recommends after verification failures",
    );
    opts.optflag(
        "",
        OPT_NO_CHEATING,
        "Do not allow assume, admit, verifier::external_body, and assume_specification",
    );
    opts.optflag("", OPT_TIME, "Measure and report time taken");
    opts.optflag("", OPT_TIME_EXPANDED, "Measure and report time taken with module breakdown");
    opts.optflag("", OPT_OUTPUT_JSON, "Emit verification results and timing as json");
    opts.optopt(
        "",
        OPT_RLIMIT,
        format!("Set SMT resource limit (roughly in seconds). Default: {}.", DEFAULT_RLIMIT_SECS)
            .as_str(),
        "FLOAT",
    );
    opts.optmulti("", OPT_SMT_OPTION, "Set an SMT option (e.g. smt.random_seed=7)", "OPTION=VALUE");
    opts.optopt("", OPT_MULTIPLE_ERRORS, "If 0, look for at most one error per function; if > 0, always find first error in function and make extra queries to find more errors (default: 2)", "INTEGER");
    opts.optflag("", OPT_NO_VSTD, "Do not load or link against the vstd library");
    opts.optflag("", OPT_IS_VSTD, "Indicates the crate being verified is vstd");
    opts.optflag(
        "",
        OPT_IS_CORE,
        "Indicates the crate being verified is core (requires a specialized setup)",
    );
    opts.optflag(
        "",
        OPT_IS_STDLIB_OUTSIDE_OF_CORE,
        "Indicates the crate being verified is the stdlib (requires a specialized setup)",
    );
    opts.optflag(
        "",
        OPT_EXPAND_ERRORS,
        "When the proof fails, try to minimize the failing predicate",
    );
    opts.optopt(
        "",
        OPT_LOG_DIR,
        "Set directory for log file generation (default: .verus-log)",
        "DIRECTORY_NAME",
    );
    opts.optflag("", OPT_LOG_ALL, "Log everything");
    opts.optmulti(
        "",
        OPT_LOG_MULTI,
        {
            let mut s = "Log selected items:\n".to_owned();
            for (f, d) in LOG_ITEMS {
                s += format!("--{} {} : {}\n", OPT_LOG_MULTI, *f, d).as_str();
            }
            s
        }
        .as_str(),
        "OPTION=VALUE",
    );

    opts.optflag("", OPT_TRIGGERS, "Show all automatically chosen triggers for verified modules");
    opts.optopt(
        "",
        OPT_TRIGGERS_MODE,
        {
            let mut s = "Display triggers:\n".to_owned();
            for (f, d) in TRIGGERS_MODE_ITEMS {
                s += format!("--{} {} : {}\n", OPT_TRIGGERS_MODE, *f, d).as_str();
            }
            s
        }
        .as_str(),
        &TRIGGERS_MODE_ITEMS.iter().map(|(x, _)| x.to_owned()).collect::<Vec<_>>().join("|"),
    );
    opts.optflag(
        "",
        OPT_PROFILE,
        "Collect and report prover performance data when resource limits are hit",
    );
    opts.optflag("", OPT_PROFILE_ALL, "Always collect and report prover performance data");
    opts.optflag("", OPT_COMPILE, "Run Rustc compiler after verification");
    opts.optopt(
        "",
        OPT_NUM_THREADS,
        format!("Number of threads to use for verification. Default: {} (available parallelism on this system).", default_num_threads)
            .as_str(),
        "INTEGER",
    );
    opts.optflag("", OPT_TRACE, "Print progress information");
    opts.optflag(
        "",
        OPT_NO_REPORT_LONG_RUNNING,
        "Suppress notes and progress bars for functions that take a while to verify",
    );

    opts.optflag("h", "help", "print this help menu");
    opts.optflag(
        "",
        OPT_RECORD,
        "Rerun verus and package source files of the current crate to the current directory, alongside with output and version information. The file will be named YYYY-MM-DD-HH-MM-SS.zip. If you are reporting an error, please keep the original arguments in addition to this flag",
    );

    opts.optmulti(
        OPT_EXTENDED_MULTI,
        "",
        {
            let mut s = "Extended/experimental options:\n".to_owned();
            for (f, d) in EXTENDED_KEYS {
                s += format!("-{} {} : {}\n", OPT_EXTENDED_MULTI, *f, d).as_str();
            }
            s
        }
        .as_str(),
        "OPTION[=VALUE]",
    );

    let print_usage = || {
        let brief = format!("Usage: {} INPUT [options]", program);
        eprint!("{}", opts.usage(&brief));
    };

    let (matches, unmatched) = match opts.parse_partial(args) {
        Ok((m, mut unmatched)) => {
            if m.opt_present("h") {
                print_usage();
                std::process::exit(0);
            }
            unmatched.insert(0, program.clone());
            (m, unmatched)
        }
        Err(f) => error(f.to_string()),
    };

    let split_pair_eq = |pair: &String| {
        let v = pair.split('=').map(|s| s.trim()).collect::<Vec<_>>();
        if v.len() == 2 {
            (v[0].to_string(), v[1].to_string())
        } else {
            error("expected option of form option_name=option_value".to_string())
        }
    };

    let no_vstd = matches.opt_present(OPT_NO_VSTD);
    let is_vstd = matches.opt_present(OPT_IS_VSTD);
    let is_core = matches.opt_present(OPT_IS_CORE);
    let is_stdlib_outside_of_core = matches.opt_present(OPT_IS_STDLIB_OUTSIDE_OF_CORE);
    if is_vstd && is_core {
        error("contradictory options --is-core and --is-vstd".to_string());
    }
    let vstd = if is_vstd {
        Vstd::IsVstd
    } else if is_core {
        Vstd::IsCore
    } else if is_stdlib_outside_of_core {
        Vstd::ImportedViaCore
    } else if no_vstd {
        Vstd::NoVstd
    } else {
        Vstd::Imported
    };

    let mut import =
        matches.opt_strs(OPT_IMPORT).iter().map(split_pair_eq).collect::<Vec<(String, String)>>();
    if let Some(vstd_import) = vstd_import {
        if vstd == Vstd::Imported {
            import.push(vstd_import);
        }
    }

    let log = parse_opts_or_pairs(matches.opt_strs(OPT_LOG_MULTI));

    let extended = parse_opts_or_pairs(matches.opt_strs(OPT_EXTENDED_MULTI));
    {
        let extended_keys_set: HashSet<_> = EXTENDED_KEYS.iter().map(|(k, _)| *k).collect();
        for extended_key in extended.keys() {
            if !extended_keys_set.contains(extended_key.as_str()) {
                error(format!("unexpected extended option -V {}", extended_key));
            }
        }
    }

    let args = ArgsX {
        verify_root: matches.opt_present(OPT_VERIFY_ROOT),
        export: matches.opt_str(OPT_EXPORT),
        import: import,
        verify_module: matches.opt_strs(OPT_VERIFY_MODULE),
        verify_only_module: matches.opt_strs(OPT_VERIFY_ONLY_MODULE),
        verify_function: {
            if matches.opt_present(OPT_VERIFY_FUNCTION) {
                if matches.opt_present(OPT_VERIFY_MODULE) {
                    error("When using --verify-function, use --verify-only-module instead of --verify-module".to_owned())
                }
                if !matches.opt_present(OPT_VERIFY_ONLY_MODULE)
                    && !matches.opt_present(OPT_VERIFY_ROOT)
                {
                    error(
                        "--verify-function option requires --verify-only-module or --verify-root"
                            .to_owned(),
                    )
                }
                if matches.opt_count(OPT_VERIFY_ONLY_MODULE)
                    + (if matches.opt_present(OPT_VERIFY_ROOT) { 1 } else { 0 })
                    > 1
                {
                    error("Must pass at most one --verify-only-module or --verify-root when using --verify-function".to_string())
                }
            }
            matches.opt_str(OPT_VERIFY_FUNCTION)
        },
        no_external_by_default: matches.opt_present(OPT_NO_EXTERNAL_BY_DEFAULT),
        no_verify: matches.opt_present(OPT_NO_VERIFY),
        no_lifetime: matches.opt_present(OPT_NO_LIFETIME),
        no_auto_recommends_check: matches.opt_present(OPT_NO_AUTO_RECOMMENDS_CHECK),
        no_cheating: matches.opt_present(OPT_NO_CHEATING),
        time: matches.opt_present(OPT_TIME) || matches.opt_present(OPT_TIME_EXPANDED),
        time_expanded: matches.opt_present(OPT_TIME_EXPANDED),
        output_json: matches.opt_present(OPT_OUTPUT_JSON),
        rlimit: {
            let rlimit = matches
                .opt_get::<f32>(OPT_RLIMIT)
                .ok()
                .or_else(|| {
                    matches.opt_get::<String>(OPT_RLIMIT).ok().and_then(|v| {
                        if v == Some("infinity".to_owned()) {
                            Some(Some(f32::INFINITY))
                        } else {
                            None
                        }
                    })
                })
                .unwrap_or_else(|| error("expected number or `infinity` after rlimit".to_string()))
                .unwrap_or(DEFAULT_RLIMIT_SECS);
            if rlimit == 0.0 {
                error("rlimit 0 is not allowed".to_string());
            } else {
                rlimit
            }
        },
        smt_options: matches.opt_strs(OPT_SMT_OPTION).iter().map(split_pair_eq).collect(),
        multiple_errors: matches
            .opt_get::<u32>(OPT_MULTIPLE_ERRORS)
            .unwrap_or_else(|_| error("expected integer after multiple-errors".to_string()))
            .unwrap_or(2),
        expand_errors: matches.opt_present(OPT_EXPAND_ERRORS),
        log_dir: matches.opt_str(OPT_LOG_DIR),
        log_all: matches.opt_present(OPT_LOG_ALL),
        log_args: LogArgs {
            log_vir: log.contains_key(LOG_VIR),
            log_vir_simple: log.contains_key(LOG_VIR_SIMPLE),
            log_vir_poly: log.contains_key(LOG_VIR_POLY),
            log_vir_sst: log.contains_key(LOG_VIR_SST),
            vir_log_option: {
                if let Some(oo) = log.get(LOG_VIR_OPTION) {
                    let Some(oo) = oo else {
                        error("expected --log vir-option=OPT1+OPT2+OPT3".to_string())
                    };
                    let vir_opts = oo.split('+').map(|s| s.trim()).collect::<Vec<_>>();
                    if vir_opts.contains(&"compact") {
                        vir::printer::COMPACT_TONODEOPTS
                    } else {
                        VirLogOption {
                            no_span: vir_opts.contains(&"no_span"),
                            no_type: vir_opts.contains(&"no_type"),
                            no_fn_details: vir_opts.contains(&"no_fn_details"),
                            no_encoding: vir_opts.contains(&"no_encoding"),
                        }
                    }
                } else {
                    Default::default()
                }
            },
            log_trait_conflicts: log.contains_key(LOG_TRAIT_CONFLICTS),
            log_interpreter: log.contains_key(LOG_INTERPRETER),
            log_air_initial: log.contains_key(LOG_AIR),
            log_air_final: log.contains_key(LOG_AIR_FINAL),
            log_smt: log.contains_key(LOG_SMT),
            log_smt_transcript: log.contains_key(LOG_SMT_TRANSCRIPT),
            log_triggers: log.contains_key(LOG_TRIGGERS),
            log_call_graph: log.contains_key(LOG_CALL_GRAPH),
        },
        show_triggers: if matches.opt_present(OPT_TRIGGERS) {
            if matches.opt_present(OPT_TRIGGERS_MODE) {
                error("--triggers and --triggers-mode are mutually exclusive".to_owned())
            }
            ShowTriggers::Module
        } else if let Some(triggers_mode) = matches.opt_str(OPT_TRIGGERS_MODE) {
            match triggers_mode.as_str() {
                TRIGGERS_MODE_ALL_MODULES => ShowTriggers::AllModules,
                TRIGGERS_MODE_SELECTIVE => ShowTriggers::Selective,
                TRIGGERS_MODE_SILENT => ShowTriggers::Silent,
                TRIGGERS_MODE_VERBOSE_ALL_MODULES => ShowTriggers::VerboseAllModules,
                TRIGGERS_MODE_VERBOSE => ShowTriggers::Verbose,
                _ => error(format!("invalid --triggers-mode {triggers_mode}")),
            }
        } else {
            ShowTriggers::default()
        },
        ignore_unexpected_smt: extended.contains_key(EXTENDED_IGNORE_UNEXPECTED_SMT),
        allow_inline_air: extended.contains_key(EXTENDED_ALLOW_INLINE_AIR),
        debugger: extended.contains_key(EXTENDED_DEBUG),
        profile: {
            if matches.opt_present(OPT_PROFILE) {
                if matches.opt_present(OPT_PROFILE_ALL) {
                    error("--profile and --profile-all are mutually exclusive".to_string())
                }
            };
            matches.opt_present(OPT_PROFILE)
        },
        profile_all: {
            if matches.opt_present(OPT_PROFILE_ALL) {
                if !(matches.opt_present(OPT_VERIFY_ONLY_MODULE)
                    || matches.opt_present(OPT_VERIFY_ROOT))
                {
                    error("Must pass --verify-only-module or --verify-root when using profile-all. To capture a full project's profile, consider -V capture-profiles".to_string())
                }
                if matches.opt_present(OPT_VERIFY_MODULE) {
                    error("When using --profile-all, use --verify-only-module instead of --verify-module".to_string())
                }
                if matches.opt_count(OPT_VERIFY_ONLY_MODULE) > 1 {
                    error(
                        "Must pass at most one --verify-only-module when using profile-all"
                            .to_string(),
                    )
                }
                if matches.opt_present(OPT_PROFILE) {
                    error("--profile and --profile-all are mutually exclusive".to_string())
                }
            };
            matches.opt_present(OPT_PROFILE_ALL)
        },
        capture_profiles: {
            if extended.contains_key(EXTENDED_CAPTURE_PROFILES) {
                if matches.opt_present(OPT_PROFILE) {
                    error("--profile and --capture-profiles are mutually exclusive".to_string())
                }
            };
            extended.contains_key(EXTENDED_CAPTURE_PROFILES)
        },
        spinoff_all: extended.contains_key(EXTENDED_SPINOFF_ALL),
        use_internal_profiler: extended.contains_key(EXTENDED_USE_INTERNAL_PROFILER),
        compile: matches.opt_present(OPT_COMPILE),
        vstd,
        solver_version_check: !extended.contains_key(EXTENDED_NO_SOLVER_VERSION_CHECK),
        version: matches.opt_present(OPT_VERSION),
        num_threads: matches
            .opt_get::<usize>(OPT_NUM_THREADS)
            .unwrap_or_else(|_| error("expected integer after num_threads".to_string()))
            .unwrap_or(default_num_threads),
        trace: matches.opt_present(OPT_TRACE),
        report_long_running: !matches.opt_present(OPT_NO_REPORT_LONG_RUNNING),
        use_crate_name: extended.contains_key(EXTENDED_USE_CRATE_NAME),
        solver: if extended.contains_key(EXTENDED_CVC5) { SmtSolver::Cvc5 } else { SmtSolver::Z3 },
        axiom_usage_info: extended.contains_key(EXTENDED_AXIOM_USAGE_INFO),
        check_api_safety: extended.contains_key(EXTENDED_CHECK_API_SAFETY),
        new_mut_ref: extended.contains_key(EXTENDED_NEW_MUT_REF),
        no_bv_simplify: extended.contains_key(EXTENDED_NO_BV_SIMPLIFY),
    };

    if args.new_mut_ref {
        NEW_MUT_REF.store(true, std::sync::atomic::Ordering::SeqCst);
    }

    (Arc::new(args), unmatched)
}

pub(crate) static NEW_MUT_REF: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

pub(crate) fn new_mut_ref() -> bool {
    NEW_MUT_REF.load(std::sync::atomic::Ordering::SeqCst)
}
