use getopts::Options;
use vir::printer::ToDebugSNodeOpts as VirLogOption;

pub const DEFAULT_RLIMIT_SECS: u32 = 10;

#[derive(Debug, Clone, Copy)]
pub enum ShowTriggers {
    Silent,
    Selective,
    Module,
    Verbose,
}
impl Default for ShowTriggers {
    fn default() -> Self {
        ShowTriggers::Selective
    }
}

pub const LOG_DIR: &str = ".verus-log";
pub const VIR_FILE_SUFFIX: &str = ".vir";
pub const VIR_SIMPLE_FILE_SUFFIX: &str = "-simple.vir";
pub const VIR_POLY_FILE_SUFFIX: &str = "-poly.vir";
pub const LIFETIME_FILE_SUFFIX: &str = "-lifetime.rs";
pub const INTERPRETER_FILE_SUFFIX: &str = ".interp";
pub const AIR_INITIAL_FILE_SUFFIX: &str = ".air";
pub const AIR_FINAL_FILE_SUFFIX: &str = "-final.air";
pub const SMT_FILE_SUFFIX: &str = ".smt2";
pub const SINGULAR_FILE_SUFFIX: &str = ".singular";
pub const TRIGGERS_FILE_SUFFIX: &str = ".triggers";

#[derive(Debug, Default)]
pub struct Args {
    pub pervasive_path: Option<String>,
    pub export: Option<String>,
    pub import: Vec<(String, String)>,
    pub verify_root: bool,
    pub verify_module: Vec<String>,
    pub verify_function: Option<String>,
    pub verify_pervasive: bool,
    pub no_verify: bool,
    pub no_lifetime: bool,
    pub no_auto_recommends_check: bool,
    pub arch_word_bits: vir::prelude::ArchWordBits,
    pub time: bool,
    pub output_json: bool,
    pub rlimit: u32,
    pub smt_options: Vec<(String, String)>,
    pub multiple_errors: u32,
    pub expand_errors: bool,
    pub log_dir: Option<String>,
    pub log_all: bool,
    pub log_vir: bool,
    pub log_vir_simple: bool,
    pub log_vir_poly: bool,
    pub vir_log_option: VirLogOption,
    pub log_lifetime: bool,
    pub log_interpreter: bool,
    pub log_air_initial: bool,
    pub log_air_final: bool,
    pub log_smt: bool,
    pub log_triggers: bool,
    pub show_triggers: ShowTriggers,
    pub print_erased: bool,
    pub print_erased_spec: bool,
    pub ignore_unexpected_smt: bool,
    pub debug: bool,
    pub profile: bool,
    pub profile_all: bool,
    pub no_vstd: bool,
    pub compile: bool,
    pub solver_version_check: bool,
    pub error_report: bool,
}

pub fn enable_default_features_and_verus_attr(
    rustc_args: &mut Vec<String>,
    syntax_macro: bool,
    erase_ghost: bool,
) {
    if syntax_macro {
        // REVIEW: syntax macro adds superfluous parentheses and braces
        for allow in &["unused_parens", "unused_braces"] {
            rustc_args.push("-A".to_string());
            rustc_args.push(allow.to_string());
        }
    }
    if erase_ghost {
        for allow in &["unused_imports", "unused_mut"] {
            rustc_args.push("-A".to_string());
            rustc_args.push(allow.to_string());
        }
    }
    for feature in &[
        "stmt_expr_attributes",
        "box_syntax",
        "box_patterns",
        "negative_impls",
        "rustc_attrs",
        "unboxed_closures",
        "register_tool",
        "tuple_trait",
        "allocator_api",
    ] {
        rustc_args.push("-Z".to_string());
        rustc_args.push(format!("crate-attr=feature({})", feature));
    }

    rustc_args.push("-Zcrate-attr=register_tool(verus)".to_string());
    rustc_args.push("-Zcrate-attr=register_tool(verifier)".to_string());
}

pub fn parse_args(program: &String, args: impl Iterator<Item = String>) -> (Args, Vec<String>) {
    const OPT_PERVASIVE_PATH: &str = "pervasive-path";
    const OPT_EXPORT: &str = "export";
    const OPT_IMPORT: &str = "import";
    const OPT_VERIFY_ROOT: &str = "verify-root";
    const OPT_VERIFY_MODULE: &str = "verify-module";
    const OPT_VERIFY_FUNCTION: &str = "verify-function";
    const OPT_VERIFY_PERVASIVE: &str = "verify-pervasive";
    const OPT_NO_VERIFY: &str = "no-verify";
    const OPT_NO_LIFETIME: &str = "no-lifetime";
    const OPT_NO_AUTO_RECOMMENDS_CHECK: &str = "no-auto-recommends-check";
    const OPT_ARCH_WORD_BITS: &str = "arch-word-bits";
    const OPT_TIME: &str = "time";
    const OPT_OUTPUT_JSON: &str = "output-json";
    const OPT_RLIMIT: &str = "rlimit";
    const OPT_SMT_OPTION: &str = "smt-option";
    const OPT_MULTIPLE_ERRORS: &str = "multiple-errors";
    const OPT_NO_VSTD: &str = "no-vstd";
    const OPT_EXPAND_ERRORS: &str = "expand-errors";
    const OPT_LOG_DIR: &str = "log-dir";
    const OPT_LOG_ALL: &str = "log-all";
    const OPT_LOG_VIR: &str = "log-vir";
    const OPT_LOG_VIR_SIMPLE: &str = "log-vir-simple";
    const OPT_LOG_VIR_POLY: &str = "log-vir-poly";
    const OPT_VIR_LOG_OPTION: &str = "vir-log-option";
    const OPT_LOG_LIFETIME: &str = "log-lifetime";
    const OPT_LOG_INTERPRETER: &str = "log-interpreter";
    const OPT_LOG_AIR_INITIAL: &str = "log-air";
    const OPT_LOG_AIR_FINAL: &str = "log-air-final";
    const OPT_LOG_SMT: &str = "log-smt";
    const OPT_LOG_TRIGGERS: &str = "log-triggers";
    const OPT_TRIGGERS_SILENT: &str = "triggers-silent";
    const OPT_TRIGGERS_SELECTIVE: &str = "triggers-selective";
    const OPT_TRIGGERS: &str = "triggers";
    const OPT_TRIGGERS_VERBOSE: &str = "triggers-verbose";
    const OPT_PRINT_ERASED: &str = "print-erased";
    const OPT_PRINT_ERASED_SPEC: &str = "print-erased-spec";
    const OPT_IGNORE_UNEXPECTED_SMT: &str = "ignore-unexpected-smt";
    const OPT_DEBUG: &str = "debug";
    const OPT_PROFILE: &str = "profile";
    const OPT_PROFILE_ALL: &str = "profile-all";
    const OPT_COMPILE: &str = "compile";
    const OPT_NO_SOLVER_VERSION_CHECK: &str = "no-solver-version-check";
    const OPT_VERSION: &str = "version";
    const OPT_ERROR_REPORT: &str = "error-report";

    let mut opts = Options::new();
    opts.optflag("", OPT_VERSION, "print version information");
    opts.optopt("", OPT_PERVASIVE_PATH, "Path of the pervasive module", "PATH");
    opts.optopt("", OPT_EXPORT, "Export Verus metadata for library crate", "CRATENAME=PATH");
    opts.optmulti("", OPT_IMPORT, "Import Verus metadata from library crate", "CRATENAME=PATH");
    opts.optflag("", OPT_VERIFY_ROOT, "Verify just the root module of crate");
    opts.optmulti(
        "",
        OPT_VERIFY_MODULE,
        "Verify just one submodule within crate (e.g. 'foo' or 'foo::bar'), can be repeated to verify only certain modules",
        "MODULE",
    );
    opts.optopt(
        "",
        OPT_VERIFY_FUNCTION,
        "Verify just one function (e.g. 'foo' or 'foo::bar') within the one module specified by verify-module or verify-root",
        "MODULE",
    );
    opts.optflag("", OPT_VERIFY_PERVASIVE, "Verify trusted pervasive modules (and nothing else)");
    opts.optflag("", OPT_NO_VERIFY, "Do not run verification");
    opts.optflag("", OPT_NO_LIFETIME, "Do not run lifetime checking on proofs");
    opts.optflag(
        "",
        OPT_NO_AUTO_RECOMMENDS_CHECK,
        "Do not automatically check recommends after verification failures",
    );
    opts.optopt("", OPT_ARCH_WORD_BITS, "Size in bits for usize/isize: valid options are either '32', '64', or '32,64'. (default: 32,64)\nWARNING: this flag is a temporary workaround and will be removed in the near future", "BITS");
    opts.optflag("", OPT_TIME, "Measure and report time taken");
    opts.optflag("", OPT_OUTPUT_JSON, "Emit verification results and timing as json");
    opts.optopt(
        "",
        OPT_RLIMIT,
        format!("Set SMT resource limit (roughly in seconds). Default: {}.", DEFAULT_RLIMIT_SECS)
            .as_str(),
        "INTEGER",
    );
    opts.optmulti("", OPT_SMT_OPTION, "Set an SMT option (e.g. smt.random_seed=7)", "OPTION=VALUE");
    opts.optopt("", OPT_MULTIPLE_ERRORS, "If 0, look for at most one error per function; if > 0, always find first error in function and make extra queries to find more errors (default: 2)", "INTEGER");
    opts.optflag("", OPT_NO_VSTD, "Do not load or link against the vstd library");
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
    opts.optflag("", OPT_LOG_VIR, "Log VIR");
    opts.optflag("", OPT_LOG_VIR_SIMPLE, "Log simplified VIR");
    opts.optflag("", OPT_LOG_VIR_POLY, "Log poly VIR");
    opts.optmulti(
         "",
         OPT_VIR_LOG_OPTION,
         "Set VIR logging option (e.g. `--vir-log-option no_span+no_type`. Available options: `compact` `no_span` `no_type` `no_encoding` `no_fn_details`) (default: verbose)",
         "VIR_LOG_OPTION",
    );
    opts.optflag("", OPT_LOG_LIFETIME, "Log lifetime checking for --erasure macro");
    opts.optflag("", OPT_LOG_INTERPRETER, "Log assert_by_compute's interpreter progress");
    opts.optflag("", OPT_LOG_AIR_INITIAL, "Log AIR queries in initial form");
    opts.optflag("", OPT_LOG_AIR_FINAL, "Log AIR queries in final form");
    opts.optflag("", OPT_LOG_SMT, "Log SMT queries");
    opts.optflag("", OPT_LOG_TRIGGERS, "Log automatically chosen triggers");
    opts.optflag("", OPT_TRIGGERS_SILENT, "Do not show automatically chosen triggers");
    opts.optflag("", OPT_TRIGGERS_SELECTIVE, "Show automatically chosen triggers for some potentially ambiguous cases in verified modules (this is the default behavior)");
    opts.optflag("", OPT_TRIGGERS, "Show all automatically chosen triggers for verified modules");
    opts.optflag("", OPT_TRIGGERS_VERBOSE, "Show all automatically chosen triggers for verified modules and imported definitions from other modules");
    opts.optflag("", OPT_PRINT_ERASED, "Print code after erasing spec/proof (requires --compile)");
    opts.optflag("", OPT_PRINT_ERASED_SPEC, "Print code after erasing spec");
    opts.optflag("", OPT_IGNORE_UNEXPECTED_SMT, "Ignore unexpected SMT output");
    opts.optflag("", OPT_DEBUG, "Enable debugging of proof failures");
    opts.optflag(
        "",
        OPT_PROFILE,
        "Collect and report prover performance data when resource limits are hit",
    );
    opts.optflag("", OPT_PROFILE_ALL, "Always collect and report prover performance data");
    opts.optflag("", OPT_COMPILE, "Run Rustc compiler after verification");
    opts.optflag("", OPT_NO_SOLVER_VERSION_CHECK, "Skip the check that the solver has the expected version (useful to experiment with different versions of z3)");
    opts.optflag("h", "help", "print this help menu");
    opts.optflag("", OPT_ERROR_REPORT, "create zip file to reproduce verus error (with version info)");

    let print_usage = || {
        let brief = format!("Usage: {} INPUT [options]", program);
        eprint!("{}", opts.usage(&brief));
    };

    let error = |msg: String| -> ! {
        eprintln!("Error: {}", msg);
        print_usage();
        std::process::exit(-1)
    };

    let (matches, unmatched) = match opts.parse_partial(args) {
        Ok((m, mut unmatched)) => {
            if m.opt_present("h") {
                print_usage();
                std::process::exit(0);
            }
            if m.free.len() == 0 {
                print_usage();
                std::process::exit(-1);
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
            error("expected SMT option of form option_name=option_value".to_string())
        }
    };

    let args = Args {
        pervasive_path: matches.opt_str(OPT_PERVASIVE_PATH),
        verify_root: matches.opt_present(OPT_VERIFY_ROOT),
        export: matches.opt_str(OPT_EXPORT),
        import: matches.opt_strs(OPT_IMPORT).iter().map(split_pair_eq).collect(),
        verify_module: matches.opt_strs(OPT_VERIFY_MODULE),
        verify_function: matches.opt_str(OPT_VERIFY_FUNCTION),
        verify_pervasive: matches.opt_present(OPT_VERIFY_PERVASIVE),
        no_verify: matches.opt_present(OPT_NO_VERIFY),
        no_lifetime: matches.opt_present(OPT_NO_LIFETIME),
        no_auto_recommends_check: matches.opt_present(OPT_NO_AUTO_RECOMMENDS_CHECK),
        arch_word_bits: matches
            .opt_str(OPT_ARCH_WORD_BITS)
            .map(|bits| {
                use vir::prelude::ArchWordBits;
                match bits.as_str() {
                    "32" => ArchWordBits::Exactly(32),
                    "64" => ArchWordBits::Exactly(64),
                    "32,64" => ArchWordBits::Either32Or64,
                    _ => error(format!(
                        "invalid {} option: it must be either '32', '64', or '32,64'",
                        OPT_ARCH_WORD_BITS
                    )),
                }
            })
            .unwrap_or(vir::prelude::ArchWordBits::Either32Or64),
        time: matches.opt_present(OPT_TIME),
        output_json: matches.opt_present(OPT_OUTPUT_JSON),
        rlimit: matches
            .opt_get::<u32>(OPT_RLIMIT)
            .unwrap_or_else(|_| error("expected integer after rlimit".to_string()))
            .unwrap_or(DEFAULT_RLIMIT_SECS),
        smt_options: matches.opt_strs(OPT_SMT_OPTION).iter().map(split_pair_eq).collect(),
        multiple_errors: matches
            .opt_get::<u32>(OPT_MULTIPLE_ERRORS)
            .unwrap_or_else(|_| error("expected integer after multiple-errors".to_string()))
            .unwrap_or(2),
        expand_errors: matches.opt_present(OPT_EXPAND_ERRORS),
        log_dir: matches.opt_str(OPT_LOG_DIR),
        log_all: matches.opt_present(OPT_LOG_ALL),
        log_vir: matches.opt_present(OPT_LOG_VIR),
        log_vir_simple: matches.opt_present(OPT_LOG_VIR_SIMPLE),
        log_vir_poly: matches.opt_present(OPT_LOG_VIR_POLY),
        vir_log_option: {
            let vir_opts: Vec<String> = matches.opt_strs(OPT_VIR_LOG_OPTION);
            if vir_opts.len() == 0 {
                Default::default()
            } else if vir_opts.len() > 1 {
                error("expected VIR_LOG_OPTION of form OPT1+OPT2+OPT3".to_string())
            } else {
                let vir_opts = vir_opts[0].split('+').map(|s| s.trim()).collect::<Vec<_>>();
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
            }
        },
        log_lifetime: matches.opt_present(OPT_LOG_LIFETIME),
        log_interpreter: matches.opt_present(OPT_LOG_INTERPRETER),
        log_air_initial: matches.opt_present(OPT_LOG_AIR_INITIAL),
        log_air_final: matches.opt_present(OPT_LOG_AIR_FINAL),
        log_smt: matches.opt_present(OPT_LOG_SMT),
        log_triggers: matches.opt_present(OPT_LOG_TRIGGERS),
        show_triggers: if matches.opt_present(OPT_TRIGGERS_VERBOSE) {
            ShowTriggers::Verbose
        } else if matches.opt_present(OPT_TRIGGERS) {
            ShowTriggers::Module
        } else if matches.opt_present(OPT_TRIGGERS_SELECTIVE) {
            ShowTriggers::Selective
        } else if matches.opt_present(OPT_TRIGGERS_SILENT) {
            ShowTriggers::Silent
        } else {
            ShowTriggers::default()
        },
        print_erased: matches.opt_present(OPT_PRINT_ERASED),
        print_erased_spec: matches.opt_present(OPT_PRINT_ERASED_SPEC),
        ignore_unexpected_smt: matches.opt_present(OPT_IGNORE_UNEXPECTED_SMT),
        debug: matches.opt_present(OPT_DEBUG),
        profile: matches.opt_present(OPT_PROFILE),
        profile_all: matches.opt_present(OPT_PROFILE_ALL),
        compile: matches.opt_present(OPT_COMPILE),
        no_vstd: matches.opt_present(OPT_NO_VSTD),
        solver_version_check: !matches.opt_present(OPT_NO_SOLVER_VERSION_CHECK),
        error_report: matches.opt_present(OPT_ERROR_REPORT),
    };

    (args, unmatched)
}
