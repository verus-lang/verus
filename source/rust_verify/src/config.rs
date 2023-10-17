use getopts::Options;
use std::sync::Arc;
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
pub const SOLVER_LOG_DIR: &str = ".verus-solver-log";
pub const VIR_FILE_SUFFIX: &str = ".vir";
pub const VIR_SIMPLE_FILE_SUFFIX: &str = "-simple.vir";
pub const VIR_POLY_FILE_SUFFIX: &str = "-poly.vir";
pub const LIFETIME_FILE_SUFFIX: &str = "-lifetime.rs";
pub const INTERPRETER_FILE_SUFFIX: &str = ".interp";
pub const AIR_INITIAL_FILE_SUFFIX: &str = ".air";
pub const AIR_FINAL_FILE_SUFFIX: &str = "-final.air";
pub const SMT_FILE_SUFFIX: &str = ".smt2";
pub const PROFILE_FILE_SUFFIX: &str = ".profile";
pub const SINGULAR_FILE_SUFFIX: &str = ".singular";
pub const TRIGGERS_FILE_SUFFIX: &str = ".triggers";

#[derive(Debug, Default)]
pub struct LogArgs {
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
}

#[derive(Debug, Default)]
pub struct ArgsX {
    pub pervasive_path: Option<String>,
    pub export: Option<String>,
    pub import: Vec<(String, String)>,
    pub verify_root: bool,
    pub verify_module: Vec<String>,
    pub verify_function: Option<String>,
    pub no_verify: bool,
    pub no_lifetime: bool,
    pub no_auto_recommends_check: bool,
    pub arch_word_bits: vir::prelude::ArchWordBits,
    pub time: bool,
    pub time_expanded: bool,
    pub output_json: bool,
    pub rlimit: u32,
    pub smt_options: Vec<(String, String)>,
    pub multiple_errors: u32,
    pub expand_errors: bool,
    pub log_dir: Option<String>,
    pub log_all: bool,
    pub log_args: LogArgs,
    pub show_triggers: ShowTriggers,
    pub ignore_unexpected_smt: bool,
    pub debugger: bool,
    pub profile: bool,
    pub profile_all: bool,
    pub no_vstd: bool,
    pub compile: bool,
    pub solver_version_check: bool,
    pub version: bool,
    pub num_threads: usize,
    pub trace: bool,
}

pub type Args = Arc<ArgsX>;

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
        "box_patterns",
        "negative_impls",
        "rustc_attrs",
        "unboxed_closures",
        "register_tool",
        "tuple_trait",
        "allocator_api",
        "custom_inner_attributes",
    ] {
        rustc_args.push("-Z".to_string());
        rustc_args.push(format!("crate-attr=feature({})", feature));
    }

    rustc_args.push("-Zcrate-attr=register_tool(verus)".to_string());
    rustc_args.push("-Zcrate-attr=register_tool(verifier)".to_string());
}

pub fn parse_args_with_imports(
    program: &String,
    args: impl Iterator<Item = String>,
    vstd: Option<(String, String)>,
) -> (Args, Vec<String>) {
    const OPT_EXPORT: &str = "export";
    const OPT_IMPORT: &str = "import";
    const OPT_VERIFY_ROOT: &str = "verify-root";
    const OPT_VERIFY_MODULE: &str = "verify-module";
    const OPT_VERIFY_FUNCTION: &str = "verify-function";
    const OPT_NO_VERIFY: &str = "no-verify";
    const OPT_NO_LIFETIME: &str = "no-lifetime";
    const OPT_NO_AUTO_RECOMMENDS_CHECK: &str = "no-auto-recommends-check";
    const OPT_ARCH_WORD_BITS: &str = "arch-word-bits";
    const OPT_TIME: &str = "time";
    const OPT_TIME_EXPANDED: &str = "time-expanded";
    const OPT_OUTPUT_JSON: &str = "output-json";
    const OPT_RLIMIT: &str = "rlimit";
    const OPT_SMT_OPTION: &str = "smt-option";
    const OPT_MULTIPLE_ERRORS: &str = "multiple-errors";
    const OPT_NO_VSTD: &str = "no-vstd";
    const OPT_EXPAND_ERRORS: &str = "expand-errors";

    const OPT_LOG_DIR: &str = "log-dir";
    const OPT_LOG_ALL: &str = "log-all";
    const OPT_LOG_MULTI: &str = "log";

    const LOG_VIR: &str = "vir";
    const LOG_VIR_SIMPLE: &str = "vir-simple";
    const LOG_VIR_POLY: &str = "vir-poly";
    const LOG_VIR_OPTION: &str = "vir-option";
    const LOG_LIFETIME: &str = "lifetime";
    const LOG_INTERPRETER: &str = "interpreter";
    const LOG_AIR: &str = "air";
    const LOG_AIR_FINAL: &str = "air-final";
    const LOG_SMT: &str = "smt";
    const LOG_TRIGGERS: &str = "triggers";
    const LOG_ITEMS: &[(&str, &str)] = &[
        (LOG_VIR, "Log VIR"),
        (LOG_VIR_SIMPLE, "Log simplified VIR"),
        (LOG_VIR_POLY, "Log poly VIR"),
        (
            LOG_VIR_OPTION,
            "Set VIR logging option (e.g. `--log vir-option=no_span+no_type`. Available options: `compact` `no_span` `no_type` `no_encoding` `no_fn_details`) (default: verbose)",
        ),
        (LOG_LIFETIME, "Log lifetime checking for --erasure macro"),
        (LOG_INTERPRETER, "Log assert_by_compute's interpreter progress"),
        (LOG_AIR, "Log AIR queries in initial form"),
        (LOG_AIR_FINAL, "Log AIR queries in final form"),
        (LOG_SMT, "Log SMT queries"),
        (LOG_TRIGGERS, "Log automatically chosen triggers"),
    ];

    const OPT_TRIGGERS_SILENT: &str = "triggers-silent";
    const OPT_TRIGGERS_SELECTIVE: &str = "triggers-selective";
    const OPT_TRIGGERS: &str = "triggers";
    const OPT_TRIGGERS_VERBOSE: &str = "triggers-verbose";
    const OPT_PROFILE: &str = "profile";
    const OPT_PROFILE_ALL: &str = "profile-all";
    const OPT_COMPILE: &str = "compile";
    const OPT_VERSION: &str = "version";
    const OPT_RECORD: &str = "record";
    const OPT_NUM_THREADS: &str = "num-threads";
    const OPT_TRACE: &str = "trace";

    const OPT_EXTENDED_MULTI: &str = "V";
    const EXTENDED_IGNORE_UNEXPECTED_SMT: &str = "ignore-unexpected-smt";
    const EXTENDED_DEBUG: &str = "debug";
    const EXTENDED_NO_SOLVER_VERSION_CHECK: &str = "no-solver-version-check";
    const EXTENDED_KEYS: &[(&str, &str)] = &[
        (EXTENDED_IGNORE_UNEXPECTED_SMT, "Ignore unexpected SMT output"),
        (EXTENDED_DEBUG, "Enable debugging of proof failures"),
        (
            EXTENDED_NO_SOLVER_VERSION_CHECK,
            "Skip the check that the solver has the expected version (useful to experiment with different versions of z3)",
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
        "Verify just one submodule within crate (e.g. 'foo' or 'foo::bar'), can be repeated to verify only certain modules",
        "MODULE",
    );
    opts.optopt(
        "",
        OPT_VERIFY_FUNCTION,
        "Verify just one function within the one module specified by verify-module or verify-root, \nmatches on unique substring (foo) or wildcards at ends of the argument (*foo, foo*, *foo*)",
        "MODULE",
    );
    opts.optflag("", OPT_NO_VERIFY, "Do not run verification");
    opts.optflag("", OPT_NO_LIFETIME, "Do not run lifetime checking on proofs");
    opts.optflag(
        "",
        OPT_NO_AUTO_RECOMMENDS_CHECK,
        "Do not automatically check recommends after verification failures",
    );
    opts.optopt("", OPT_ARCH_WORD_BITS, "Size in bits for usize/isize: valid options are either '32', '64', or '32,64'. (default: 32,64)\nWARNING: this flag is a temporary workaround and will be removed in the near future", "BITS");
    opts.optflag("", OPT_TIME, "Measure and report time taken");
    opts.optflag("", OPT_TIME_EXPANDED, "Measure and report time taken with module breakdown");
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

    opts.optflag("", OPT_TRIGGERS_SILENT, "Do not show automatically chosen triggers");
    opts.optflag("", OPT_TRIGGERS_SELECTIVE, "Show automatically chosen triggers for some potentially ambiguous cases in verified modules (this is the default behavior)");
    opts.optflag("", OPT_TRIGGERS, "Show all automatically chosen triggers for verified modules");
    opts.optflag("", OPT_TRIGGERS_VERBOSE, "Show all automatically chosen triggers for verified modules and imported definitions from other modules");
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
            if m.free.len() == 0 && !m.opt_present("version") {
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
            error("expected option of form option_name=option_value".to_string())
        }
    };

    let no_vstd = matches.opt_present(OPT_NO_VSTD);

    let mut import =
        matches.opt_strs(OPT_IMPORT).iter().map(split_pair_eq).collect::<Vec<(String, String)>>();
    if let Some(vstd) = vstd {
        if !no_vstd {
            import.push(vstd);
        }
    }

    let parse_opts_or_pairs = |strs: Vec<String>| {
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
    };

    let log = parse_opts_or_pairs(matches.opt_strs(OPT_LOG_MULTI));

    let extended = parse_opts_or_pairs(matches.opt_strs(OPT_EXTENDED_MULTI));

    let args = ArgsX {
        pervasive_path: None,
        verify_root: matches.opt_present(OPT_VERIFY_ROOT),
        export: matches.opt_str(OPT_EXPORT),
        import: import,
        verify_module: matches.opt_strs(OPT_VERIFY_MODULE),
        verify_function: matches.opt_str(OPT_VERIFY_FUNCTION),
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
        time: matches.opt_present(OPT_TIME) || matches.opt_present(OPT_TIME_EXPANDED),
        time_expanded: matches.opt_present(OPT_TIME_EXPANDED),
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
        log_args: LogArgs {
            log_vir: log.get(LOG_VIR).is_some(),
            log_vir_simple: log.get(LOG_VIR_SIMPLE).is_some(),
            log_vir_poly: log.get(LOG_VIR_POLY).is_some(),
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
            log_lifetime: log.get(LOG_LIFETIME).is_some(),
            log_interpreter: log.get(LOG_INTERPRETER).is_some(),
            log_air_initial: log.get(LOG_AIR).is_some(),
            log_air_final: log.get(LOG_AIR_FINAL).is_some(),
            log_smt: log.get(LOG_SMT).is_some(),
            log_triggers: log.get(LOG_TRIGGERS).is_some(),
        },
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
        ignore_unexpected_smt: extended.get(EXTENDED_IGNORE_UNEXPECTED_SMT).is_some(),
        debugger: extended.get(EXTENDED_DEBUG).is_some(),
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
                if !matches.opt_present(OPT_VERIFY_MODULE) {
                    error("Must pass --verify-module when profiling".to_string())
                }
                if matches.opt_present(OPT_PROFILE) {
                    error("--profile and --profile-all are mutually exclusive".to_string())
                }
            };
            matches.opt_present(OPT_PROFILE_ALL)
        },
        compile: matches.opt_present(OPT_COMPILE),
        no_vstd,
        solver_version_check: !extended.get(EXTENDED_NO_SOLVER_VERSION_CHECK).is_some(),
        version: matches.opt_present(OPT_VERSION),
        num_threads: matches
            .opt_get::<usize>(OPT_NUM_THREADS)
            .unwrap_or_else(|_| error("expected integer after num_threads".to_string()))
            .unwrap_or(default_num_threads),
        trace: matches.opt_present(OPT_TRACE),
    };

    (Arc::new(args), unmatched)
}
