use getopts::Options;

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
pub const AIR_INITIAL_FILE_SUFFIX: &str = ".air";
pub const AIR_FINAL_FILE_SUFFIX: &str = "-final.air";
pub const SMT_FILE_SUFFIX: &str = ".smt2";
pub const SINGULAR_FILE_SUFFIX: &str = ".singular";
pub const TRIGGERS_FILE_SUFFIX: &str = ".triggers";

#[derive(Debug, Default)]
pub struct Args {
    pub pervasive_path: Option<String>,
    pub verify_root: bool,
    pub verify_module: Option<String>,
    pub verify_function: Option<String>,
    pub verify_pervasive: bool,
    pub no_verify: bool,
    pub no_lifetime: bool,
    pub no_auto_recommends_check: bool,
    pub no_enhanced_typecheck: bool,
    pub time: bool,
    pub rlimit: u32,
    pub smt_options: Vec<(String, String)>,
    pub multiple_errors: u32,
    pub log_dir: Option<String>,
    pub log_all: bool,
    pub log_vir: bool,
    pub log_vir_simple: bool,
    pub vir_log_no_span: bool,
    pub vir_log_no_type: bool,
    pub vir_log_no_encoding: bool,
    pub vir_log_pretty: bool,
    pub log_vir_poly: bool,
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
    pub compile: bool,
}

pub fn enable_default_features(rustc_args: &mut Vec<String>) {
    for feature in &["stmt_expr_attributes", "box_syntax", "box_patterns", "negative_impls"] {
        rustc_args.push("-Z".to_string());
        rustc_args.push(format!("enable_feature={}", feature));
    }
}

pub fn parse_args(program: &String, args: impl Iterator<Item = String>) -> (Args, Vec<String>) {
    const OPT_PERVASIVE_PATH: &str = "pervasive-path";
    const OPT_VERIFY_ROOT: &str = "verify-root";
    const OPT_VERIFY_MODULE: &str = "verify-module";
    const OPT_VERIFY_FUNCTION: &str = "verify-function";
    const OPT_VERIFY_PERVASIVE: &str = "verify-pervasive";
    const OPT_NO_VERIFY: &str = "no-verify";
    const OPT_NO_LIFETIME: &str = "no-lifetime";
    const OPT_NO_AUTO_RECOMMENDS_CHECK: &str = "no-auto-recommends-check";
    const OPT_NO_ENHANCED_TYPECHECK: &str = "no-enhanced-typecheck";
    const OPT_TIME: &str = "time";
    const OPT_RLIMIT: &str = "rlimit";
    const OPT_SMT_OPTION: &str = "smt-option";
    const OPT_MULTIPLE_ERRORS: &str = "multiple-errors";
    const OPT_LOG_DIR: &str = "log-dir";
    const OPT_LOG_ALL: &str = "log-all";
    const OPT_LOG_VIR: &str = "log-vir";
    const OPT_LOG_VIR_SIMPLE: &str = "log-vir-simple";
    const OPT_LOG_VIR_POLY: &str = "log-vir-poly";
    const OPT_VIR_LOG_NO_SPAN: &str = "vir-log-no-span";
    const OPT_VIR_LOG_NO_TYPE: &str = "vir-log-no-type";
    const OPT_VIR_LOG_NO_ENCODING: &str = "vir-log-no-encoding";
    const OPT_VIR_LOG_PRETTY: &str = "vir-log-pretty";
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

    let mut opts = Options::new();
    opts.optopt("", OPT_PERVASIVE_PATH, "Path of the pervasive module", "PATH");
    opts.optflag("", OPT_VERIFY_ROOT, "Verify just the root module of crate");
    opts.optopt(
        "",
        OPT_VERIFY_MODULE,
        "Verify just one submodule within crate (e.g. 'foo' or 'foo::bar')",
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
    opts.optflag("", OPT_NO_ENHANCED_TYPECHECK, "Disable extensions to Rust type checker");
    opts.optflag("", OPT_TIME, "Measure and report time taken");
    opts.optopt(
        "",
        OPT_RLIMIT,
        format!("Set SMT resource limit (roughly in seconds). Default: {}.", DEFAULT_RLIMIT_SECS)
            .as_str(),
        "INTEGER",
    );
    opts.optmulti("", OPT_SMT_OPTION, "Set an SMT option (e.g. smt.random_seed=7)", "OPTION=VALUE");
    opts.optopt("", OPT_MULTIPLE_ERRORS, "If 0, look for at most one error per function; if > 0, always find first error in function and make extra queries to find more errors (default: 2)", "INTEGER");
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
    opts.optflag("", OPT_VIR_LOG_NO_SPAN, "Omit span in VIR logs");
    opts.optflag("", OPT_VIR_LOG_NO_TYPE, "Omit type in VIR logs");
    opts.optflag(
        "",
        OPT_VIR_LOG_NO_ENCODING,
        "Omit SMT related encodings(box/unbox/clip) in VIR logs",
    );
    opts.optflag("", OPT_VIR_LOG_PRETTY, "Pretty print exprs in VIR logs");
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
    opts.optflag("h", "help", "print this help menu");

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

    let args = Args {
        pervasive_path: matches.opt_str(OPT_PERVASIVE_PATH),
        verify_root: matches.opt_present(OPT_VERIFY_ROOT),
        verify_module: matches.opt_str(OPT_VERIFY_MODULE),
        verify_function: matches.opt_str(OPT_VERIFY_FUNCTION),
        verify_pervasive: matches.opt_present(OPT_VERIFY_PERVASIVE),
        no_verify: matches.opt_present(OPT_NO_VERIFY),
        no_lifetime: matches.opt_present(OPT_NO_LIFETIME),
        no_auto_recommends_check: matches.opt_present(OPT_NO_AUTO_RECOMMENDS_CHECK),
        no_enhanced_typecheck: matches.opt_present(OPT_NO_ENHANCED_TYPECHECK),
        time: matches.opt_present(OPT_TIME),
        rlimit: matches
            .opt_get::<u32>(OPT_RLIMIT)
            .unwrap_or_else(|_| error("expected integer after rlimit".to_string()))
            .unwrap_or(DEFAULT_RLIMIT_SECS),
        smt_options: matches
            .opt_strs(OPT_SMT_OPTION)
            .iter()
            .map(|line| {
                let v = line.split('=').map(|s| s.trim()).collect::<Vec<_>>();
                if v.len() == 2 {
                    (v[0].to_string(), v[1].to_string())
                } else {
                    error("expected SMT option of form option_name=option_value".to_string())
                }
            })
            .collect(),
        multiple_errors: matches
            .opt_get::<u32>(OPT_MULTIPLE_ERRORS)
            .unwrap_or_else(|_| error("expected integer after multiple-errors".to_string()))
            .unwrap_or(2),
        log_dir: matches.opt_str(OPT_LOG_DIR),
        log_all: matches.opt_present(OPT_LOG_ALL),
        log_vir: matches.opt_present(OPT_LOG_VIR),
        log_vir_simple: matches.opt_present(OPT_LOG_VIR_SIMPLE),
        log_vir_poly: matches.opt_present(OPT_LOG_VIR_POLY),
        vir_log_no_span: matches.opt_present(OPT_VIR_LOG_NO_SPAN),
        vir_log_no_type: matches.opt_present(OPT_VIR_LOG_NO_TYPE),
        vir_log_no_encoding: matches.opt_present(OPT_VIR_LOG_NO_ENCODING),
        vir_log_pretty: matches.opt_present(OPT_VIR_LOG_PRETTY),
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
    };

    (args, unmatched)
}
