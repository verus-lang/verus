use getopts::Options;

#[derive(Debug, Default)]
pub struct Args {
    pub pervasive_path: Option<String>,
    pub verify_root: bool,
    pub verify_module: Option<String>,
    pub verify_pervasive: bool,
    pub external_body: bool,
    pub no_lifetime: bool,
    pub time: bool,
    pub rlimit: u32,
    pub smt_options: Vec<(String, String)>,
    pub multiple_errors: u32,
    pub log_vir: Option<String>,
    pub log_vir_simple: Option<String>,
    pub log_vir_poly: Option<String>,
    pub log_air_initial: Option<String>,
    pub log_air_final: Option<String>,
    pub log_smt: Option<String>,
    pub log_triggers: Option<String>,
    pub show_triggers: bool,
    pub print_erased: bool,
    pub print_erased_spec: bool,
    pub ignore_unexpected_smt: bool,
    pub debug: bool,
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
    const OPT_VERIFY_PERVASIVE: &str = "verify-pervasive";
    const OPT_NO_VERIFY: &str = "no-verify";
    const OPT_NO_LIFETIME: &str = "no-lifetime";
    const OPT_TIME: &str = "time";
    const OPT_RLIMIT: &str = "rlimit";
    const OPT_SMT_OPTION: &str = "smt-option";
    const OPT_MULTIPLE_ERRORS: &str = "multiple-errors";
    const OPT_LOG_VIR: &str = "log-vir";
    const OPT_LOG_VIR_SIMPLE: &str = "log-vir-simple";
    const OPT_LOG_VIR_POLY: &str = "log-vir-poly";
    const OPT_LOG_AIR_INITIAL: &str = "log-air";
    const OPT_LOG_AIR_FINAL: &str = "log-air-final";
    const OPT_LOG_SMT: &str = "log-smt";
    const OPT_LOG_TRIGGERS: &str = "log-triggers";
    const OPT_TRIGGERS: &str = "triggers";
    const OPT_PRINT_ERASED: &str = "print-erased";
    const OPT_PRINT_ERASED_SPEC: &str = "print-erased-spec";
    const OPT_IGNORE_UNEXPECTED_SMT: &str = "ignore-unexpected-smt";
    const OPT_DEBUG: &str = "debug";
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
    opts.optflag("", OPT_VERIFY_PERVASIVE, "Verify trusted pervasive modules");
    opts.optflag("", OPT_NO_VERIFY, "Do not run verification");
    opts.optflag("", OPT_NO_LIFETIME, "Do not run lifetime checking on proofs");
    opts.optflag("", OPT_TIME, "Measure and report time taken");
    opts.optopt("", OPT_RLIMIT, "Set SMT resource limit (roughly in seconds)", "INTEGER");
    opts.optmulti("", OPT_SMT_OPTION, "Set an SMT option (e.g. smt.random_seed=7)", "OPTION=VALUE");
    opts.optopt("", OPT_MULTIPLE_ERRORS, "If 0, look for at most one error per function; if > 0, always find first error in function and make extra queries to find more errors (default: 2)", "INTEGER");
    opts.optopt("", OPT_LOG_VIR, "Log VIR", "FILENAME");
    opts.optopt("", OPT_LOG_VIR_SIMPLE, "Log simplified VIR", "FILENAME");
    opts.optopt(
        "",
        OPT_LOG_VIR_POLY,
        "Log poly VIR, filename prefix (it will be suffixed with the current module name)",
        "FILENAME",
    );
    opts.optopt("", OPT_LOG_AIR_INITIAL, "Log AIR queries in initial form", "FILENAME");
    opts.optopt("", OPT_LOG_AIR_FINAL, "Log AIR queries in final form", "FILENAME");
    opts.optopt("", OPT_LOG_SMT, "Log SMT queries", "FILENAME");
    opts.optopt("", OPT_LOG_TRIGGERS, "Log automatically chosen triggers", "FILENAME");
    opts.optflag("", OPT_TRIGGERS, "Show automatically chosen triggers");
    opts.optflag("", OPT_PRINT_ERASED, "Print code after erasing spec/proof (requires --compile)");
    opts.optflag("", OPT_PRINT_ERASED_SPEC, "Print code after erasing spec");
    opts.optflag("", OPT_IGNORE_UNEXPECTED_SMT, "Ignore unexpected SMT output");
    opts.optflag("", OPT_DEBUG, "Enable debugging of proof failures");
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
        verify_pervasive: matches.opt_present(OPT_VERIFY_PERVASIVE),
        external_body: matches.opt_present(OPT_NO_VERIFY),
        no_lifetime: matches.opt_present(OPT_NO_LIFETIME),
        time: matches.opt_present(OPT_TIME),
        rlimit: matches
            .opt_get::<u32>(OPT_RLIMIT)
            .unwrap_or_else(|_| error("expected integer after rlimit".to_string()))
            .unwrap_or(0),
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
        log_vir: matches.opt_str(OPT_LOG_VIR),
        log_vir_simple: matches.opt_str(OPT_LOG_VIR_SIMPLE),
        log_vir_poly: matches.opt_str(OPT_LOG_VIR_POLY),
        log_air_initial: matches.opt_str(OPT_LOG_AIR_INITIAL),
        log_air_final: matches.opt_str(OPT_LOG_AIR_FINAL),
        log_smt: matches.opt_str(OPT_LOG_SMT),
        log_triggers: matches.opt_str(OPT_LOG_TRIGGERS),
        show_triggers: matches.opt_present(OPT_TRIGGERS),
        print_erased: matches.opt_present(OPT_PRINT_ERASED),
        print_erased_spec: matches.opt_present(OPT_PRINT_ERASED_SPEC),
        ignore_unexpected_smt: matches.opt_present(OPT_IGNORE_UNEXPECTED_SMT),
        debug: matches.opt_present(OPT_DEBUG),
        compile: matches.opt_present(OPT_COMPILE),
    };

    (args, unmatched)
}
