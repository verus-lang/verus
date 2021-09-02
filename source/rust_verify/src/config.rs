use getopts::Options;

#[derive(Debug, Default)]
pub struct Args {
    pub verify_root: bool,
    pub verify_module: Option<String>,
    pub no_verify: bool,
    pub rlimit: u32,
    pub log_vir: Option<String>,
    pub log_air_initial: Option<String>,
    pub log_air_final: Option<String>,
    pub log_smt: Option<String>,
    pub log_triggers: Option<String>,
    pub show_triggers: bool,
    pub debug: bool,
    pub compile: bool,
}

pub fn parse_args(program: &String, args: impl Iterator<Item = String>) -> (Args, Vec<String>) {
    const OPT_VERIFY_ROOT: &str = "verify-root";
    const OPT_VERIFY_MODULE: &str = "verify-module";
    const OPT_NO_VERIFY: &str = "no-verify";
    const OPT_RLIMIT: &str = "rlimit";
    const OPT_LOG_VIR: &str = "log-vir";
    const OPT_LOG_AIR_INITIAL: &str = "log-air";
    const OPT_LOG_AIR_FINAL: &str = "log-air-final";
    const OPT_LOG_SMT: &str = "log-smt";
    const OPT_LOG_TRIGGERS: &str = "log-triggers";
    const OPT_TRIGGERS: &str = "triggers";
    const OPT_DEBUG: &str = "debug";
    const OPT_COMPILE: &str = "compile";

    let mut opts = Options::new();
    opts.optflag("", OPT_VERIFY_ROOT, "Verify just the root module of crate");
    opts.optopt(
        "",
        OPT_VERIFY_MODULE,
        "Verify just one submodule within crate (e.g. 'foo' or 'foo::bar')",
        "MODULE",
    );
    opts.optflag("", OPT_NO_VERIFY, "Do not run verification");
    opts.optopt("", OPT_RLIMIT, "Set SMT resource limit (roughly in seconds)", "INTEGER");
    opts.optopt("", OPT_LOG_VIR, "Log VIR", "FILENAME");
    opts.optopt("", OPT_LOG_AIR_INITIAL, "Log AIR queries in initial form", "FILENAME");
    opts.optopt("", OPT_LOG_AIR_FINAL, "Log AIR queries in final form", "FILENAME");
    opts.optopt("", OPT_LOG_SMT, "Log SMT queries", "FILENAME");
    opts.optopt("", OPT_LOG_TRIGGERS, "Log automatically chosen triggers", "FILENAME");
    opts.optflag("", OPT_TRIGGERS, "Show automatically chosen triggers");
    opts.optflag("", OPT_DEBUG, "Enable debugging of proof failures");
    opts.optflag("", OPT_COMPILE, "Run Rustc compiler after verification");
    opts.optflag("h", "help", "print this help menu");

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
            if m.free.len() == 0 {
                print_usage();
                std::process::exit(-1);
            }
            unmatched.insert(0, program.clone());
            (m, unmatched)
        }
        Err(f) => {
            eprintln!("Error: {}", f.to_string());
            print_usage();
            std::process::exit(-1);
        }
    };

    let args = Args {
        verify_root: matches.opt_present(OPT_VERIFY_ROOT),
        verify_module: matches.opt_str(OPT_VERIFY_MODULE),
        no_verify: matches.opt_present(OPT_NO_VERIFY),
        rlimit: matches
            .opt_get::<u32>(OPT_RLIMIT)
            .expect("expected integer after rlimit")
            .unwrap_or(0),
        log_vir: matches.opt_str(OPT_LOG_VIR),
        log_air_initial: matches.opt_str(OPT_LOG_AIR_INITIAL),
        log_air_final: matches.opt_str(OPT_LOG_AIR_FINAL),
        log_smt: matches.opt_str(OPT_LOG_SMT),
        log_triggers: matches.opt_str(OPT_LOG_TRIGGERS),
        show_triggers: matches.opt_present(OPT_TRIGGERS),
        debug: matches.opt_present(OPT_DEBUG),
        compile: matches.opt_present(OPT_COMPILE),
    };

    (args, unmatched)
}
