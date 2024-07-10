use air::ast::CommandX;
#[cfg(feature = "axiom-usage-info")]
use air::context::UsageInfo;
use air::context::{Context, SmtSolver, ValidityResult};
use air::messages::{AirMessage, AirMessageLabel, Reporter};
use air::profiler::{Profiler, PROVER_LOG_FILE};
use getopts::Options;
use sise::Node;
use std::fs::File;
use std::io::Read;

#[cfg(target_family = "windows")]
fn os_setup() -> Result<(), Box<dyn std::error::Error>> {
    // Configure Windows to kill the child SMT process if the parent is killed
    let job = win32job::Job::create()?;
    let mut info = job.query_extended_limit_info()?;
    info.limit_kill_on_job_close();
    job.set_extended_limit_info(&mut info)?;
    job.assign_current_process()?;
    // dropping the job object would kill us immediately, so just let it live forever instead:
    std::mem::forget(job);
    Ok(())
}

#[cfg(target_family = "unix")]
fn os_setup() -> Result<(), Box<dyn std::error::Error>> {
    Ok(())
}

pub fn main() {
    let _ = os_setup();

    let mut args = std::env::args();
    let program = args.next().unwrap();

    let mut opts = Options::new();
    opts.optflag("", "auto-config", "Set Z3 auto_config=true");
    opts.optopt("", "log-air-middle", "Log AIR queries in middle form", "FILENAME");
    opts.optopt("", "log-air-final", "Log AIR queries in final form", "FILENAME");
    opts.optopt("", "log-smt", "Log SMT queries", "FILENAME");
    opts.optflag("", "ignore-unexpected-smt", "Ignore unexpected SMT output");
    opts.optflag("d", "debug", "Debug verification failures");
    opts.optflag(
        "p",
        "profile",
        "Collect and report prover performance data when resource limits are hit",
    );
    opts.optflag("p", "profile_all", "Always collect and report prover performance data");
    opts.optflag("h", "help", "print this help menu");

    let print_usage = || {
        let brief = format!("Usage: {} INPUT [OPTIONS]", program);
        eprint!("{}", opts.usage(&brief));
    };

    let matches = match opts.parse(args) {
        Ok(m) => {
            if m.opt_present("h") {
                print_usage();
                return;
            }
            match m.free.len() {
                0 => {
                    print_usage();
                    std::process::exit(-1);
                }
                1 => m,
                _ => {
                    print_usage();
                    std::process::exit(-1);
                }
            }
        }
        Err(f) => {
            eprintln!("Error: {}", f.to_string());
            print_usage();
            std::process::exit(-1);
        }
    };

    let message_interface = std::sync::Arc::new(air::messages::AirMessageInterface {});

    // Open input file
    let in_filename = &matches.free[0];
    let mut in_bytes: Vec<u8> = Vec::new();
    in_bytes.push('(' as u8);
    {
        File::open(in_filename)
            .and_then(|mut file| file.read_to_end(&mut in_bytes))
            .expect(&format!("could not read file {}", in_filename));
    }
    in_bytes.push(')' as u8);

    // Parse input file to vector of Node
    let mut parser = sise::Parser::new(&in_bytes);
    let node = sise::read_into_tree(&mut parser).unwrap();
    let nodes = match node {
        Node::Atom(_) => panic!("internal error: nodes"),
        Node::List(nodes) => nodes,
    };

    // Parse vector of Node to commands
    let commands = air::parser::Parser::new(message_interface.clone())
        .nodes_to_commands(&nodes)
        .expect("parse error");

    // Start AIR
    let mut air_context = Context::new(message_interface.clone(), SmtSolver::Z3);
    let debug = matches.opt_present("debug");
    air_context.set_debug(debug);
    let profile_all = matches.opt_present("profile_all");
    if profile_all {
        air_context.set_profile_with_logfile_name(PROVER_LOG_FILE.into());
    }
    let ignore_unexpected_smt = matches.opt_present("ignore-unexpected-smt");
    air_context.set_ignore_unexpected_smt(ignore_unexpected_smt);

    // Start logging
    if let Some(filename) = matches.opt_str("log-air-middle") {
        let file =
            File::create(&filename).unwrap_or_else(|_| panic!("could not open file {}", &filename));
        air_context.set_air_middle_log(Box::new(file));
    }
    if let Some(filename) = matches.opt_str("log-air-final") {
        let file =
            File::create(&filename).unwrap_or_else(|_| panic!("could not open file {}", &filename));
        air_context.set_air_final_log(Box::new(file));
    }
    if let Some(filename) = matches.opt_str("log-smt") {
        let file =
            File::create(&filename).unwrap_or_else(|_| panic!("could not open file {}", &filename));
        air_context.set_smt_log(Box::new(file));
    }

    // Send commands
    let mut count_errors = 0;
    let mut count_verified = 0;
    let reporter = Reporter {};
    for command in commands.iter() {
        let result =
            air_context.command(&*message_interface, &reporter, &command, Default::default());
        match result {
            #[cfg(not(feature = "axiom-usage-info"))]
            ValidityResult::Valid() => {
                if let CommandX::CheckValid(_) = &**command {
                    count_verified += 1;
                }
            }
            #[cfg(feature = "axiom-usage-info")]
            ValidityResult::Valid(usage_info) => {
                if let CommandX::CheckValid(_) = &**command {
                    count_verified += 1;

                    if let UsageInfo::UsedAxioms(axioms) = usage_info {
                        println!(
                            "Query used named axioms: {}",
                            axioms
                                .iter()
                                .map(|x| (**x).clone())
                                .collect::<Vec<String>>()
                                .join(", ")
                        )
                    }
                }
            }
            ValidityResult::TypeError(err) => {
                panic!("Type error: {}", err);
            }
            ValidityResult::Invalid(_m, None, _assert_id) => {
                count_errors += 1;
                println!("Error at unknown location");
            }
            ValidityResult::Invalid(_m, Some(err), _assert_id) => {
                count_errors += 1;
                let err: &AirMessage =
                    err.downcast_ref().expect("unexpected value in Any -> Message conversion");
                println!("Error at {}", err.note);
                for AirMessageLabel { note, .. } in &err.labels {
                    println!("Additional error detail at {}", note);
                }
            }
            ValidityResult::Canceled => {
                count_errors += 1;
                if !profile_all {
                    println!(
                        "Resource limit (rlimit) exceeded; consider rerunning with --profile for more details"
                    );
                } else {
                    println!("Resource limit (rlimit) exceeded");
                }
            }
            ValidityResult::UnexpectedOutput(err) => {
                panic!("Unexpected output from solver: {}", err);
            }
        }
        if matches!(**command, CommandX::CheckValid(..)) {
            air_context.finish_query();
        }
    }
    if profile_all {
        match Profiler::parse(
            message_interface.clone(),
            std::path::Path::new(PROVER_LOG_FILE),
            None,
            true,
            &reporter,
            false,
        ) {
            Ok(profiler) => profiler.print_raw_stats(&reporter),
            Err(err) => eprintln!("profile: failed to parse z3 trace: {}", err),
        }
    }
    println!("Verification results:: {} verified, {} errors", count_verified, count_errors);
}
