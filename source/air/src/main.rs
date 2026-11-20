use air::ast::CommandX;
use air::context::UsageInfo;
use air::context::{Context, SmtSolver, ValidityResult};
use air::messages::{AirMessage, AirMessageLabel, Reporter};
use air::profiler::{PROVER_LOG_FILE, Profiler};
use clap::Parser;
use sise::TreeNode as Node;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

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

#[derive(Parser, Debug)]
struct Args {
    /// Input file containing AIR commands
    #[arg(value_name = "INPUT")]
    input: PathBuf,

    /// Set Z3 auto_config=true
    #[arg(long)]
    auto_config: bool,

    /// Log AIR queries in middle form
    #[arg(long, value_name = "FILENAME")]
    log_air_middle: Option<PathBuf>,

    /// Log AIR queries in final form
    #[arg(long, value_name = "FILENAME")]
    log_air_final: Option<PathBuf>,

    /// Log SMT queries
    #[arg(long, value_name = "FILENAME")]
    log_smt: Option<PathBuf>,

    /// Log complete SMT transcript
    #[arg(long, value_name = "FILENAME")]
    log_smt_transcript: Option<PathBuf>,

    /// Ignore unexpected SMT output
    #[arg(long)]
    ignore_unexpected_smt: bool,

    /// Debug verification failures
    #[arg(short, long)]
    debug: bool,

    /// After the first error in a query, look for up to this many more
    #[arg(long, value_name = "INTEGER", default_value_t = 0)]
    multiple_errors: u32,

    /// Print the result of each check-valid query, in order, as a JSON array on stdout
    #[arg(long)]
    output_json: bool,

    /// Collect and report prover performance data when resource limits are hit
    #[arg(short, long)]
    profile: bool,

    /// Always collect and report prover performance data
    #[arg(long, alias = "profile_all")]
    profile_all: bool,
}

pub fn main() {
    let _ = os_setup();
    let args = Args::parse();

    let message_interface = std::sync::Arc::new(air::messages::AirMessageInterface {});

    // Open input file
    let mut in_string = String::new();
    in_string.push('(');
    {
        File::open(&args.input)
            .and_then(|mut file| file.read_to_string(&mut in_string))
            .unwrap_or_else(|e| panic!("could not read file {}: {:?}", args.input.display(), e));
    }
    in_string.push(')');

    // Parse input file to vector of Node
    let mut parser = sise::Parser::new(in_string.as_str());
    let node = sise::parse_tree(&mut parser).unwrap();
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
    air_context.set_debug(args.debug);
    if args.profile_all {
        air_context.set_profile_with_logfile_name(PROVER_LOG_FILE.into());
    }
    air_context.set_ignore_unexpected_smt(args.ignore_unexpected_smt);

    // Start logging
    if let Some(filename) = &args.log_air_middle {
        let file = File::create(filename)
            .unwrap_or_else(|_| panic!("could not open file {}", filename.display()));
        air_context.set_air_middle_log(Box::new(file));
    }
    if let Some(filename) = &args.log_air_final {
        let file = File::create(filename)
            .unwrap_or_else(|_| panic!("could not open file {}", filename.display()));
        air_context.set_air_final_log(Box::new(file));
    }
    if let Some(filename) = &args.log_smt {
        let file = File::create(filename)
            .unwrap_or_else(|_| panic!("could not open file {}", filename.display()));
        air_context.set_smt_log(Box::new(file));
    }
    if let Some(filename) = &args.log_smt_transcript {
        let file = File::create(filename)
            .unwrap_or_else(|_| panic!("could not open file {}", filename.display()));
        air_context.set_smt_transcript_log(Box::new(file));
    }

    // Send commands
    let mut count_errors = 0;
    let mut count_verified = 0;
    let mut json_results: Vec<serde_json::Value> = Vec::new();
    let reporter = Reporter {};
    for command in commands.iter() {
        let is_check_valid = matches!(**command, CommandX::CheckValid(..));
        let mut result =
            air_context.command(&*message_interface, &reporter, &command, Default::default());
        let mut is_first_check = true;
        let mut checks_remaining = args.multiple_errors;
        let mut only_check_earlier = false;
        let mut json_status = "valid";
        let mut json_errors: Vec<serde_json::Value> = Vec::new();
        loop {
            match result {
                ValidityResult::Valid(usage_info) => {
                    if is_check_valid && is_first_check {
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
                    if is_first_check {
                        count_errors += 1;
                    }
                    json_status = "invalid";
                    json_errors
                        .push(serde_json::json!({ "note": null, "span": null, "labels": [] }));
                    println!("Error at unknown location");
                }
                ValidityResult::Invalid(m, Some(err), _assert_id) => {
                    if is_first_check {
                        count_errors += 1;
                    }
                    json_status = "invalid";
                    let err: &AirMessage =
                        err.downcast_ref().expect("unexpected value in Any -> Message conversion");
                    println!("Error at {}", err.note);
                    for AirMessageLabel { note, .. } in &err.labels {
                        println!("Additional error detail at {}", note);
                    }
                    json_errors.push(serde_json::json!({
                        "note": err.note,
                        "span": err.span.as_ref().map(|s| s.as_string.clone()),
                        "labels": err.labels.iter().map(|l| serde_json::json!({
                            "note": l.note,
                            "span": l.span.as_string,
                        })).collect::<Vec<_>>(),
                    }));
                    if m.is_some() && checks_remaining > 0 {
                        // Like Verus's --multiple-errors: disable the failed assertion and retry
                        is_first_check = false;
                        if !only_check_earlier {
                            checks_remaining -= 1;
                            if checks_remaining == 0 {
                                only_check_earlier = true;
                            }
                        }
                        result = air_context.check_valid_again(
                            &reporter,
                            only_check_earlier,
                            Default::default(),
                        );
                        continue;
                    }
                }
                ValidityResult::Canceled => {
                    if is_first_check {
                        count_errors += 1;
                    }
                    if json_status == "valid" {
                        json_status = "canceled";
                    }
                    if !args.profile_all {
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
            break;
        }
        if is_check_valid {
            json_results.push(serde_json::json!({
                "query": json_results.len(),
                "result": json_status,
                "errors": json_errors,
            }));
            air_context.finish_query();
        }
    }
    if args.profile_all {
        match Profiler::parse(
            message_interface.clone(),
            std::path::Path::new(PROVER_LOG_FILE),
            None,
            &reporter,
        ) {
            Ok(profiler) => profiler.print_raw_stats(&reporter),
            Err(err) => eprintln!("profile: failed to parse z3 trace: {}", err),
        }
    }
    println!("Verification results:: {} verified, {} errors", count_verified, count_errors);
    if args.output_json {
        println!("{}", serde_json::Value::Array(json_results));
    }
}
