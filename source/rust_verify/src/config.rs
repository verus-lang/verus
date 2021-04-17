use getopts::Options;

#[derive(Debug, Default)]
pub(crate) struct Args {
    pub(crate) rlimit: u32,
    pub(crate) log_vir: Option<String>,
    pub(crate) log_air_initial: Option<String>,
    pub(crate) log_air_final: Option<String>,
    pub(crate) log_smt: Option<String>,
}

pub(crate) fn parse_args(
    program: &String,
    args: impl Iterator<Item = String>,
) -> (Args, Vec<String>) {
    const OPT_RLIMIT: &str = "rlimit";
    const OPT_LOG_VIR: &str = "log-vir";
    const OPT_LOG_AIR_INITIAL: &str = "log-air";
    const OPT_LOG_AIR_FINAL: &str = "log-air-final";
    const OPT_LOG_SMT: &str = "log-smt";

    let mut opts = Options::new();
    opts.optopt("", OPT_RLIMIT, "Set SMT resource limit (roughly in seconds)", "INTEGER");
    opts.optopt("", OPT_LOG_VIR, "Log VIR", "FILENAME");
    opts.optopt("", OPT_LOG_AIR_INITIAL, "Log AIR queries in initial form", "FILENAME");
    opts.optopt("", OPT_LOG_AIR_FINAL, "Log AIR queries in final form", "FILENAME");
    opts.optopt("", OPT_LOG_SMT, "Log SMT queries", "FILENAME");
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
        rlimit: matches
            .opt_get::<u32>(OPT_RLIMIT)
            .expect("expected integer after rlimit")
            .unwrap_or(0),
        log_vir: matches.opt_str(OPT_LOG_VIR),
        log_air_initial: matches.opt_str(OPT_LOG_AIR_INITIAL),
        log_air_final: matches.opt_str(OPT_LOG_AIR_FINAL),
        log_smt: matches.opt_str(OPT_LOG_SMT),
    };

    (args, unmatched)
}
