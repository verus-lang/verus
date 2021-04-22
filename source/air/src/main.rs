use air::ast::{CommandX, Span, ValidityResult};
use air::context::Context;
use getopts::Options;
use sise::Node;
use std::fs::File;
use std::io::Read;

pub fn main() {
    let mut args = std::env::args();
    let program = args.next().unwrap();

    let mut opts = Options::new();
    opts.optflag("", "auto-config", "Set Z3 auto_config=true");
    opts.optopt("", "log-air-final", "Log AIR queries in final form", "FILENAME");
    opts.optopt("", "log-smt", "Log SMT queries", "FILENAME");
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
    let commands = air::print_parse::nodes_to_commands(&nodes).expect("parse error");

    // Start Z3
    let mut z3_config = z3::Config::new();
    z3_config.set_param_value(
        "auto_config",
        if matches.opt_present("auto-config") { "true" } else { "false" },
    );
    let z3_context = z3::Context::new(&z3_config);
    let z3_solver = z3::Solver::new(&z3_context);
    let mut air_context = Context::new(&z3_context, &z3_solver);

    // Start logging
    if let Some(filename) = matches.opt_str("log-air-final") {
        let file = File::create(&filename).expect(&format!("could not open file {}", &filename));
        air_context.set_air_final_log(Box::new(file));
    }
    if let Some(filename) = matches.opt_str("log-smt") {
        let file = File::create(&filename).expect(&format!("could not open file {}", &filename));
        air_context.set_smt_log(Box::new(file));
    }

    // Send commands
    let mut count_errors = 0;
    let mut count_verified = 0;
    for command in commands.iter() {
        let result = air_context.command(&command);
        match result {
            ValidityResult::Valid => {
                if let CommandX::CheckValid(_) = &**command {
                    count_verified += 1;
                }
            }
            ValidityResult::TypeError(err) => {
                panic!("Type error: {}", err);
            }
            ValidityResult::Invalid(span1, span2) => {
                count_errors += 1;
                match &*span1 {
                    None => {
                        println!(
                            "Error at unlabeled assert (use 'assert \"...label...\" e') for better errors"
                        );
                    }
                    Some(Span { as_string, .. }) => {
                        println!("Error at {}", as_string);
                    }
                }
                match &*span2 {
                    None => {}
                    Some(Span { as_string, .. }) => {
                        println!("Additional error detail at {}", as_string);
                    }
                }
            }
        }
    }
    println!("Verification results:: verified: {} errors: {}", count_verified, count_errors);
}
