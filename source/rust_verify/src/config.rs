#[derive(Debug, Default)]
pub(crate) struct Args {
    pub(crate) rlimit: u32,
    pub(crate) log_vir: Option<String>,
    pub(crate) log_air_initial: Option<String>,
    pub(crate) log_air_final: Option<String>,
    pub(crate) log_smt: Option<String>,
}

pub(crate) fn take_our_args(args: &mut Vec<String>) -> Args {
    let mut a: Args = Default::default();
    let mut i = 1;
    if args.len() == i {
        args.push("--help".to_string());
    }
    while i < args.len() {
        let arg = &args[i];
        let next_arg = if i + 1 < args.len() && !args[i + 1].starts_with("-") {
            Some(args[i + 1].clone())
        } else {
            None
        };
        if arg == "-h" || arg == "--help" {
            println!("Usage: rust_verify [OPTIONS] INPUT");
            println!();
            println!("Verifier options:");
            println!(
                "    --rlimit INTEGER              Set SMT resource limit (roughly in seconds)"
            );
            println!("    --log-vir FILENAME            Log VIR");
            println!("    --log-air FILENAME            Log AIR queries in initial form");
            println!("    --log-air-final FILENAME      Log AIR queries in final form");
            println!("    --log-smt FILENAME            Log SMT queries");
            println!();
            i = i + 1;
        } else if arg == "--rlimit" {
            match next_arg {
                None => panic!("expected integer after {}", arg),
                Some(s) => {
                    a.rlimit = s.parse().expect(&format!("expected integer after {}", arg));
                }
            }
            args.remove(i);
            args.remove(i);
        } else if arg == "--log-vir"
            || arg == "--log-air"
            || arg == "--log-air-final"
            || arg == "--log-smt"
        {
            match next_arg {
                None => panic!("expected filename after {}", arg),
                Some(filename) => {
                    if arg == "--log-vir" {
                        a.log_vir = Some(filename);
                    } else if arg == "--log-air" {
                        a.log_air_initial = Some(filename);
                    } else if arg == "--log-air-final" {
                        a.log_air_final = Some(filename);
                    } else if arg == "--log-smt" {
                        a.log_smt = Some(filename);
                    }
                }
            }
            args.remove(i);
            args.remove(i);
        } else {
            i = i + 1;
        }
    }
    a
}
