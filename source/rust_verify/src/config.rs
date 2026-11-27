use air::context::{SmtEncoding, SmtSolver};
use clap::{CommandFactory, FromArgMatches};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};
use vir::printer::ToDebugSNodeOpts as VirLogOption;

pub const DEFAULT_RLIMIT_SECS: f32 = 10f32;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum ShowTriggers {
    Silent,
    #[default]
    Selective,
    #[value(skip)]
    Module,
    AllModules,
    Verbose,
    VerboseAllModules,
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
pub const IMPL_NAMES_SUFFIX: &str = ".impl_names";
pub const CALL_GRAPH_FILE_SUFFIX_FULL_INITIAL: &str = "-call-graph-full-initial.dot";
pub const CALL_GRAPH_FILE_SUFFIX_FULL_SIMPLIFIED: &str = "-call-graph-full-simplified.dot";
pub const CALL_GRAPH_FILE_SUFFIX_NOSTD_INITIAL: &str = "-call-graph-nostd-initial.dot";
pub const CALL_GRAPH_FILE_SUFFIX_NOSTD_SIMPLIFIED: &str = "-call-graph-nostd-simplified.dot";

const OPT_VERIFY_ROOT: &str = "verify-root";
const OPT_VERIFY_MODULE: &str = "verify-module";
const OPT_VERIFY_ONLY_MODULE: &str = "verify-only-module";
const OPT_VERIFY_FUNCTION: &str = "verify-function";
const OPT_NO_LIFETIME: &str = "no-lifetime";
const OPT_NO_TRAIT_CONFLICTS: &str = "no-trait-conflicts";
const OPT_NO_ERASURE_CHECK: &str = "no-erasure-check";
const OPT_NO_CHEATING: &str = "no-cheating";
const OPT_NO_CHECK_DROPS: &str = "no-check-drops";
const OPT_IS_VSTD: &str = "is-vstd";
const OPT_IS_CORE: &str = "is-core";
const OPT_IS_STDLIB_OUTSIDE_OF_CORE: &str = "is-stdlib-outside-of-core";

const LOG_VIR: &str = "vir";
const LOG_VIR_SIMPLE: &str = "vir-simple";
const LOG_VIR_POLY: &str = "vir-poly";
const LOG_VIR_SST: &str = "vir-sst";
const LOG_VIR_OPTION: &str = "vir-option";
const LOG_TRAIT_CONFLICTS: &str = "trait-conflicts";
const LOG_INTERPRETER: &str = "interpreter";
const LOG_AIR: &str = "air";
const LOG_AIR_FINAL: &str = "air-final";
const LOG_SMT: &str = "smt";
const LOG_SMT_TRANSCRIPT: &str = "smt-transcript";
const LOG_TRIGGERS: &str = "triggers";
const LOG_IMPL_NAMES: &str = "impl-names";
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
    (LOG_IMPL_NAMES, "Log rustc's internal trait impl names"),
    (LOG_CALL_GRAPH, "Log the call graph"),
];

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

const EXTENDED_IGNORE_UNEXPECTED_SMT: &str = "ignore-unexpected-smt";
const EXTENDED_NO_SOLVER_VERSION_CHECK: &str = "no-solver-version-check";
const EXTENDED_SPINOFF_ALL: &str = "spinoff-all";
const EXTENDED_CAPTURE_PROFILES: &str = "capture-profiles";
const EXTENDED_CVC5: &str = "cvc5";
const EXTENDED_CVC5_SMTLIB: &str = "cvc5-smtlib";
const EXTENDED_ALLOW_INLINE_AIR: &str = "allow-inline-air";
const EXTENDED_USE_CRATE_NAME: &str = "use-crate-name";
const EXTENDED_AXIOM_USAGE_INFO: &str = "axiom-usage-info";
const EXTENDED_CHECK_API_SAFETY: &str = "check-api-safety";
const EXTENDED_NO_BV_SIMPLIFY: &str = "no-bv-simplify";
const EXTENDED_OBSERVER: &str = "observer";
const EXTENDED_KEYS: &[(&str, &str)] = &[
    (EXTENDED_IGNORE_UNEXPECTED_SMT, "Ignore unexpected SMT output"),
    (
        EXTENDED_NO_SOLVER_VERSION_CHECK,
        "Skip the check that the solver has the expected version (useful to experiment with different versions of z3)",
    ),
    (EXTENDED_SPINOFF_ALL, "Always spinoff individual functions to separate z3 instances"),
    (
        EXTENDED_CAPTURE_PROFILES,
        "Always collect prover performance data, but don't generate output reports",
    ),
    (EXTENDED_CVC5, "Use the cvc5 SMT solver, rather than the default (Z3)"),
    (EXTENDED_CVC5_SMTLIB, "Use cvc5-compatible SMT-LIB with the default Z3 solver"),
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
    (
        EXTENDED_NO_BV_SIMPLIFY,
        "internal option to disable simplification of bit-vector assertions before sending to the SMT solver",
    ),
    (EXTENDED_OBSERVER, "Observer to run during verification (e.g., test)"),
];

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
    pub log_impl_names: bool,
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
    pub build_sst: bool,
    pub no_lifetime: bool,
    pub no_trait_conflicts: bool,
    pub no_erasure_check: bool,
    pub no_auto_recommends_check: bool,
    pub no_cheating: bool,
    pub check_drops: bool,
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
    pub profile: bool,
    pub profile_all: bool,
    pub capture_profiles: bool,
    pub spinoff_all: bool,
    pub vstd: Vstd,
    pub compile: bool,
    pub solver_version_check: bool,
    pub version: bool,
    pub num_threads: usize,
    pub trace: bool,
    pub report_long_running: bool,
    pub use_crate_name: bool,
    pub solver: SmtSolver,
    pub smt_encoding: SmtEncoding,
    pub axiom_usage_info: bool,
    pub check_api_safety: bool,
    pub no_bv_simplify: bool,
    pub observer: Option<String>,
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
            build_sst: Default::default(),
            no_lifetime: Default::default(),
            no_trait_conflicts: Default::default(),
            no_erasure_check: Default::default(),
            no_auto_recommends_check: Default::default(),
            no_cheating: Default::default(),
            check_drops: true,
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
            profile: Default::default(),
            profile_all: Default::default(),
            capture_profiles: Default::default(),
            spinoff_all: Default::default(),
            vstd: Vstd::Imported,
            compile: Default::default(),
            solver_version_check: Default::default(),
            version: Default::default(),
            num_threads: Default::default(),
            trace: Default::default(),
            report_long_running: Default::default(),
            use_crate_name: Default::default(),
            solver: Default::default(),
            smt_encoding: Default::default(),
            axiom_usage_info: Default::default(),
            check_api_safety: Default::default(),
            no_bv_simplify: Default::default(),
            observer: None,
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

/// Value parser for `--rlimit`; accepts a float or `infinity`, rejects 0.
pub fn parse_rlimit(s: &str) -> Result<f32, String> {
    let rlimit: f32 =
        s.parse().map_err(|_| "expected number or `infinity` after `--rlimit`".to_string())?;
    if rlimit == 0.0 {
        return Err("rlimit 0 is not allowed".to_string());
    }
    Ok(rlimit)
}

fn default_num_threads() -> usize {
    std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or_default()
        .saturating_sub(1)
        .max(1)
}

/// Clap model of verus's command-line arguments (the options currently handled by
/// `parse_args_with_imports`).
#[derive(clap::Parser, Debug)]
#[command(name = "verus", about = "The Verus verifier")]
pub struct VerusCli {
    /// Print version information (add `--output-json` to print as json)
    #[arg(long)]
    pub version: bool,

    /// Export Verus metadata for library crate
    #[arg(long, value_name = "PATH")]
    pub export: Option<String>,

    /// Import Verus metadata from library crate
    #[arg(long, value_name = "CRATENAME=PATH")]
    pub import: Vec<String>,

    /// Verify just the root module of crate
    #[arg(long)]
    pub verify_root: bool,

    /// Verify just one submodule and its descendants within the crate (e.g. 'foo' or 'foo::bar'), can be repeated to verify only certain modules
    #[arg(long, value_name = "MODULE")]
    pub verify_module: Vec<String>,

    /// Verify just one submodule (excluding its descendants) within the crate (e.g. 'foo' or 'foo::bar'), can be repeated to verify only certain modules
    #[arg(long, value_name = "MODULE")]
    pub verify_only_module: Vec<String>,

    /// Verify just one function within the one module specified by verify-module or verify-root, matches on unique substring (foo) or wildcards at ends of the argument (*foo, foo*, *foo*)
    #[arg(long, value_name = "FUNCTION")]
    pub verify_function: Option<String>,

    /// (deprecated) Verify all items, even those declared outside the verus! macro, and even if they aren't marked #[verifier::verify]
    #[arg(long)]
    pub no_external_by_default: bool,

    /// Do not run verification
    #[arg(long)]
    pub no_verify: bool,

    /// Always build SST even if no-verify is set
    #[arg(long)]
    pub build_sst: bool,

    /// Do not run lifetime checking on proofs
    #[arg(long)]
    pub no_lifetime: bool,

    /// Do not run trait conflict checking
    #[arg(long)]
    pub no_trait_conflicts: bool,

    /// Do not run the final erasure check
    #[arg(long)]
    pub no_erasure_check: bool,

    /// Do not automatically check recommends after verification failures
    #[arg(long)]
    pub no_auto_recommends_check: bool,

    /// Do not allow assume, admit, verifier::external_body, and assume_specification; also reject options that skip or weaken checks
    #[arg(long)]
    pub no_cheating: bool,

    /// Do not check the implicit drops of no_unwind and atomic exec functions (found in rustc's MIR) against unverified Drop impls of the crate
    #[arg(long)]
    pub no_check_drops: bool,

    /// Measure and report time taken
    #[arg(long)]
    pub time: bool,

    /// Measure and report time taken with module breakdown
    #[arg(long)]
    pub time_expanded: bool,

    /// Emit verification results and timing as json
    #[arg(long)]
    pub output_json: bool,

    /// Set SMT resource limit (roughly in seconds)
    #[arg(long, value_name = "FLOAT", default_value_t = DEFAULT_RLIMIT_SECS, value_parser = parse_rlimit)]
    pub rlimit: f32,

    /// Set an SMT option (e.g. smt.random_seed=7)
    #[arg(long, value_name = "OPTION=VALUE")]
    pub smt_option: Vec<String>,

    /// If 0, look for at most one error per function; if > 0, always find first error in function and make extra queries to find more errors
    #[arg(long, value_name = "INTEGER", default_value_t = 2)]
    pub multiple_errors: u32,

    /// Do not load or link against the vstd library
    #[arg(long)]
    pub no_vstd: bool,

    /// Indicates the crate being verified is vstd
    #[arg(long)]
    pub is_vstd: bool,

    /// Indicates the crate being verified is core (requires a specialized setup)
    #[arg(long)]
    pub is_core: bool,

    /// Indicates the crate being verified is the stdlib (requires a specialized setup)
    #[arg(long)]
    pub is_stdlib_outside_of_core: bool,

    /// When the proof fails, try to minimize the failing predicate
    #[arg(long)]
    pub expand_errors: bool,

    /// Set directory for log file generation (default: .verus-log)
    #[arg(long, value_name = "DIRECTORY_NAME")]
    pub log_dir: Option<String>,

    /// Log everything
    #[arg(long)]
    pub log_all: bool,

    /// Log selected items (e.g. `--log vir`, `--log smt`, `--log vir-option=no_span+no_type`)
    #[arg(long, value_name = "OPTION[=VALUE]")]
    pub log: Vec<String>,

    /// Show all automatically chosen triggers for verified modules
    #[arg(long)]
    pub triggers: bool,

    /// Display triggers
    #[arg(long, value_name = "MODE", value_enum)]
    pub triggers_mode: Option<ShowTriggers>,

    /// Collect and report prover performance data when resource limits are hit
    #[arg(long)]
    pub profile: bool,

    /// Always collect and report prover performance data
    #[arg(long)]
    pub profile_all: bool,

    /// Run Rustc compiler after verification
    #[arg(long)]
    pub compile: bool,

    /// Number of threads to use for verification; defaults to available parallelism on this system
    #[arg(long, value_name = "INTEGER", default_value_t = default_num_threads())]
    pub num_threads: usize,

    /// Print progress information
    #[arg(long)]
    pub trace: bool,

    /// Suppress notes and progress bars for functions that take a while to verify
    #[arg(long)]
    pub no_report_long_running: bool,

    /// Rerun verus and package source files of the current crate to the current directory, alongside with output and version information. The file will be named YYYY-MM-DD-HH-MM-SS.zip. If you are reporting an error, please keep the original arguments in addition to this flag
    #[arg(long)]
    pub record: bool,

    /// Extended/experimental options
    #[arg(short = 'V', value_name = "OPTION[=VALUE]")]
    pub extended: Vec<String>,
}

/// Formats a per-item long help list from an items table,
/// e.g. `"--log vir : Log VIR"` for the `--log` option.
fn items_help(header: &str, flag: &str, items: &[(&str, &str)]) -> String {
    let mut s = format!("{header}\n\n");
    for (key, description) in items {
        s += &format!("{flag} {key} : {description}\n");
    }
    s
}

/// The clap command for verus, with long help text generated from the option tables.
fn verus_command() -> clap::Command {
    VerusCli::command()
        .max_term_width(80)
        .mut_arg("extended", |a| {
            a.long_help(items_help("Extended/experimental options:", "-V", EXTENDED_KEYS))
        })
        .mut_arg("log", |a| a.long_help(items_help("Log selected items:", "--log", LOG_ITEMS)))
        .mut_arg("triggers_mode", |a| {
            a.long_help(items_help("Display triggers:", "--triggers-mode", TRIGGERS_MODE_ITEMS))
        })
}

pub fn enable_default_features_and_verus_attr(
    rustc_args: &mut Vec<String>,
    syntax_macro: bool,
    _erase_ghost: bool,
) {
    if syntax_macro {
        // REVIEW: syntax macro adds superfluous parentheses and braces
        for allow in &[
            "unused_parens",
            "unused_braces",
            "unconditional_panic",
            "arithmetic_overflow",
            "irrefutable_let_patterns",
        ] {
            rustc_args.push("-A".to_string());
            rustc_args.push(allow.to_string());
        }
    }
    for allow in &["unused_imports", "unused_mut"] {
        rustc_args.push("-A".to_string());
        rustc_args.push(allow.to_string());
    }
    rustc_args.push("-Zcrate-attr=allow(internal_features)".to_string());
    rustc_args.push("-Zcrate-attr=allow(unused_features)".to_string());
    for feature in &[
        "stmt_expr_attributes",
        "deref_patterns",
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
    eprintln!("error: {}", msg);
    std::process::exit(-1)
}

fn parse_opts_or_pairs(strs: Vec<String>) -> HashMap<String, Option<String>> {
    let mut parsed: HashMap<String, Option<String>> = HashMap::new();
    for o in strs {
        let oo: Vec<_> = o.split("=").collect();
        match &oo[..] {
            [opt] => parsed.insert((*opt).to_owned(), None),
            [key, val] => parsed.insert((*key).to_owned(), Some((*val).to_owned())),
            _ => {
                error(format!("invalid parsed option `-V {}`", o));
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
                        "expected `--VIA-CARGO {}=DEP_NAME`",
                        CARGO_OPT_IMPORT_DEP_IF_PRESENT
                    ));
                }
            } else {
                error(format!("unexpected `--VIA-CARGO {}`", arg));
            }
            next_is_via_cargo = false;
            false
        } else {
            true
        }
    });

    Arc::new(cargo_verus_args)
}

/// Splits the raw argv into verus's own arguments (for clap) and the remaining arguments,
/// which are forwarded to rustc in their original order. This reproduces the permutation
/// behavior of the old getopts `parse_partial`: known verus options are recognized wherever
/// they appear, e.g. `verus --crate-name x input.rs --output-json`.
fn split_verus_args(
    program: String,
    mut args: impl Iterator<Item = String>,
) -> (Vec<String>, Vec<String>) {
    let cmd = verus_command();
    let mut longs = HashMap::new();
    let mut shorts = HashMap::new();
    for arg in cmd.get_arguments() {
        let takes_values = arg.get_action().takes_values();
        if let Some(l) = arg.get_long() {
            longs.insert(l, takes_values);
        }
        if let Some(s) = arg.get_short() {
            shorts.insert(s, takes_values);
        }
    }

    // automatically generated help flag
    longs.insert("help", false);
    shorts.insert('h', false);

    let mut clap_args = vec![program];
    let mut rustc_args = Vec::new();
    while let Some(arg) = args.next() {
        if arg == "--" {
            // everything after `--` is passed through untouched
            rustc_args.extend(args);
            return (clap_args, rustc_args);
        }

        // handle long arguments
        if let Some(rest) = arg.strip_prefix("--") {
            let name = rest.split('=').next().unwrap();
            let has_eq = rest.contains('=');
            match longs.get(name) {
                Some(&true) => {
                    clap_args.push(arg);
                    if !has_eq {
                        if let Some(v) = args.next() {
                            clap_args.push(v);
                        }
                    }
                }
                Some(&false) => clap_args.push(arg),
                None => rustc_args.push(arg),
            }
            continue;
        }

        // handle short arguments
        if arg.len() > 1 && arg.starts_with('-') {
            let c = arg.chars().nth(1).unwrap();
            let separate_value = arg.len() == 2;
            match shorts.get(&c) {
                Some(&true) => {
                    clap_args.push(arg);
                    if separate_value {
                        if let Some(v) = args.next() {
                            clap_args.push(v);
                        }
                    }
                }
                Some(&false) => clap_args.push(arg),
                None => rustc_args.push(arg),
            }
            continue;
        }

        // anything else goes to rustc
        rustc_args.push(arg);
    }

    (clap_args, rustc_args)
}

pub fn parse_args_with_imports(
    program: &String,
    args: impl Iterator<Item = String>,
    vstd_import: Option<(String, String)>,
) -> (Args, Vec<String>) {
    let (clap_args, mut rustc_args) = split_verus_args(program.clone(), args);
    let matches = verus_command().get_matches_from(clap_args);
    let cli = VerusCli::from_arg_matches(&matches).unwrap_or_else(|err| err.exit());

    let split_pair_eq = |pair: &String| {
        let v = pair.split('=').map(|s| s.trim()).collect::<Vec<_>>();
        if v.len() == 2 {
            (v[0].to_string(), v[1].to_string())
        } else {
            error("expected option of form `option_name=option_value`".to_string())
        }
    };

    if cli.is_vstd && cli.is_core {
        error("contradictory options `--is-core` and `--is-vstd`".to_string());
    }

    let vstd = if cli.is_vstd {
        Vstd::IsVstd
    } else if cli.is_core {
        Vstd::IsCore
    } else if cli.is_stdlib_outside_of_core {
        Vstd::ImportedViaCore
    } else if cli.no_vstd {
        Vstd::NoVstd
    } else {
        Vstd::Imported
    };

    let mut import = cli.import.iter().map(split_pair_eq).collect::<Vec<_>>();
    if let Some(vstd_import) = vstd_import {
        if vstd == Vstd::Imported {
            import.push(vstd_import);
        }
    }

    let log = parse_opts_or_pairs(cli.log.clone());
    let extended = parse_opts_or_pairs(cli.extended.clone());
    {
        let extended_keys_set: HashSet<_> = EXTENDED_KEYS.iter().map(|(k, _)| *k).collect();
        for extended_key in extended.keys() {
            if !extended_keys_set.contains(extended_key.as_str()) {
                error(format!("unexpected extended option `-V {}`", extended_key));
            }
        }
    }
    if extended.contains_key(EXTENDED_CVC5) && extended.contains_key(EXTENDED_CVC5_SMTLIB) {
        error("`-V cvc5` and `-V cvc5-smtlib` are mutually exclusive".to_string());
    }
    let solver = if extended.contains_key(EXTENDED_CVC5) { SmtSolver::Cvc5 } else { SmtSolver::Z3 };
    let smt_encoding = if extended.contains_key(EXTENDED_CVC5_SMTLIB) {
        SmtEncoding::Cvc5
    } else {
        solver.default_encoding()
    };

    let args = ArgsX {
        verify_root: cli.verify_root,
        export: cli.export.clone(),
        import: import,
        verify_module: cli.verify_module.clone(),
        verify_only_module: cli.verify_only_module.clone(),
        verify_function: {
            if cli.verify_function.is_some() {
                if !cli.verify_module.is_empty() {
                    error("when using `--verify-function`, use `--verify-only-module` instead of `--verify-module`".to_owned())
                }
                if cli.verify_only_module.is_empty() && !cli.verify_root {
                    error(
                        "`--verify-function` option requires `--verify-only-module` or `--verify-root`"
                            .to_owned(),
                    )
                }
                if cli.verify_only_module.len() + usize::from(cli.verify_root) > 1 {
                    error("must pass at most one `--verify-only-module` or `--verify-root` when using `--verify-function`".to_string())
                }
            }
            cli.verify_function.clone()
        },
        no_external_by_default: cli.no_external_by_default,
        no_verify: cli.no_verify,
        build_sst: cli.build_sst,
        no_lifetime: cli.no_lifetime,
        no_trait_conflicts: cli.no_trait_conflicts,
        no_erasure_check: cli.no_erasure_check,
        no_auto_recommends_check: cli.no_auto_recommends_check,
        no_cheating: cli.no_cheating,
        check_drops: !cli.no_check_drops,
        time: cli.time || cli.time_expanded,
        time_expanded: cli.time_expanded,
        output_json: cli.output_json,
        rlimit: cli.rlimit,
        smt_options: cli.smt_option.iter().map(split_pair_eq).collect(),
        multiple_errors: cli.multiple_errors,
        expand_errors: cli.expand_errors,
        log_dir: cli.log_dir.clone(),
        log_all: cli.log_all,
        log_args: LogArgs {
            log_vir: log.contains_key(LOG_VIR),
            log_vir_simple: log.contains_key(LOG_VIR_SIMPLE),
            log_vir_poly: log.contains_key(LOG_VIR_POLY),
            log_vir_sst: log.contains_key(LOG_VIR_SST),
            vir_log_option: {
                if let Some(oo) = log.get(LOG_VIR_OPTION) {
                    let Some(oo) = oo else {
                        error("expected `--log vir-option=OPT1+OPT2+OPT3`".to_string())
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
            log_impl_names: log.contains_key(LOG_IMPL_NAMES),
            log_call_graph: log.contains_key(LOG_CALL_GRAPH),
        },
        show_triggers: if cli.triggers {
            if cli.triggers_mode.is_some() {
                error("`--triggers` and `--triggers-mode` are mutually exclusive".to_owned())
            }
            ShowTriggers::Module
        } else {
            cli.triggers_mode.unwrap_or_default()
        },
        ignore_unexpected_smt: extended.contains_key(EXTENDED_IGNORE_UNEXPECTED_SMT),
        allow_inline_air: extended.contains_key(EXTENDED_ALLOW_INLINE_AIR),
        profile: {
            if cli.profile && cli.profile_all {
                error("`--profile` and `--profile-all` are mutually exclusive".to_string())
            }
            cli.profile
        },
        profile_all: {
            if cli.profile_all {
                if cli.verify_only_module.is_empty() && !cli.verify_root {
                    error("must pass `--verify-only-module` or `--verify-root` when using `--profile-all`; to capture a full project's profile, consider `-V capture-profiles`".to_string())
                }
                if !cli.verify_module.is_empty() {
                    error("when using `--profile-all`, use `--verify-only-module` instead of `--verify-module`".to_string())
                }
                if cli.verify_only_module.len() > 1 {
                    error(
                        "must pass at most one `--verify-only-module` when using `--profile-all`"
                            .to_string(),
                    )
                }
                if cli.profile {
                    error("`--profile` and `--profile-all` are mutually exclusive".to_string())
                }
            };
            cli.profile_all
        },
        capture_profiles: {
            if extended.contains_key(EXTENDED_CAPTURE_PROFILES) && cli.profile {
                error("`--profile` and `--capture-profiles` are mutually exclusive".to_string())
            }
            extended.contains_key(EXTENDED_CAPTURE_PROFILES)
        },
        spinoff_all: extended.contains_key(EXTENDED_SPINOFF_ALL),
        compile: cli.compile,
        vstd,
        solver_version_check: !extended.contains_key(EXTENDED_NO_SOLVER_VERSION_CHECK),
        version: cli.version,
        num_threads: cli.num_threads,
        trace: cli.trace,
        report_long_running: !cli.no_report_long_running,
        use_crate_name: extended.contains_key(EXTENDED_USE_CRATE_NAME),
        solver,
        smt_encoding,
        axiom_usage_info: extended.contains_key(EXTENDED_AXIOM_USAGE_INFO),
        check_api_safety: extended.contains_key(EXTENDED_CHECK_API_SAFETY),
        no_bv_simplify: extended.contains_key(EXTENDED_NO_BV_SIMPLIFY),
        observer: match extended.get(EXTENDED_OBSERVER) {
            None => None,
            Some(Some(name)) => Some(name.clone()),
            Some(None) => error(format!(
                "-V {} needs a name, e.g. -V {}=test",
                EXTENDED_OBSERVER, EXTENDED_OBSERVER
            )),
        },
    };

    if args.no_cheating {
        let disallowed_flags = [
            (OPT_VERIFY_ROOT, cli.verify_root),
            (OPT_VERIFY_MODULE, !cli.verify_module.is_empty()),
            (OPT_VERIFY_ONLY_MODULE, !cli.verify_only_module.is_empty()),
            (OPT_VERIFY_FUNCTION, cli.verify_function.is_some()),
            (OPT_NO_LIFETIME, cli.no_lifetime),
            (OPT_NO_ERASURE_CHECK, cli.no_erasure_check),
            (OPT_NO_TRAIT_CONFLICTS, cli.no_trait_conflicts),
            (OPT_NO_CHECK_DROPS, cli.no_check_drops),
            (OPT_IS_VSTD, cli.is_vstd),
            (OPT_IS_CORE, cli.is_core),
            (OPT_IS_STDLIB_OUTSIDE_OF_CORE, cli.is_stdlib_outside_of_core),
        ];
        for (flag, present) in disallowed_flags {
            if present {
                error(format!("`--{flag}` is not allowed with `--{OPT_NO_CHEATING}`"));
            }
        }
        let disallowed_extended = [EXTENDED_ALLOW_INLINE_AIR, EXTENDED_IGNORE_UNEXPECTED_SMT];
        for key in disallowed_extended {
            if extended.contains_key(key) {
                error(format!("`-V {key}` is not allowed with `--{OPT_NO_CHEATING}`"));
            }
        }
    }

    if args.compile && args.no_erasure_check {
        error("`--compile` and `--no-erasure-check` are mutually exclusive".to_string())
    }

    rustc_args.insert(0, program.clone());
    (Arc::new(args), rustc_args)
}
