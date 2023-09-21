use std::{collections::HashMap, path::Path, process::exit};

use getopts::Options;
use qi_graph::{Graph, InstantiationGraph, Quantifier};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let program = args[0].clone();

    let mut opts = Options::new();
    opts.optflag("h", "help", "print this help menu");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            panic!("{}", f.to_string())
        }
    };

    fn print_usage(program: &str, opts: Options) {
        let brief = format!("Usage: {} FILE [options]", program);
        print!("{}", opts.usage(&brief));
    }

    if matches.opt_present("h") {
        print_usage(&program, opts);
        return;
    }

    let input_path = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
    };

    match run(&input_path) {
        Ok(()) => (),
        Err(err) => {
            eprintln!("error: {}", err);
            exit(1);
        }
    }
}

fn run(input_path: &str) -> Result<(), String> {
    let bytes =
        std::fs::read(input_path).map_err(|_e| format!("failed to read file {input_path}"))?;
    let graph: InstantiationGraph =
        bincode::deserialize(&bytes[..]).map_err(|_| format!("input {input_path} is malformed"))?;
    dbg!(graph.graph.0.len());

    let mut simple_graph: HashMap<Quantifier, HashMap<Quantifier, u64>> = HashMap::new();
    for (src, dsts) in graph.graph.0 {
        let new_src = simple_graph.entry(src.quantifier.clone()).or_insert(HashMap::new());
        for (_edge, dst) in dsts {
            *new_src.entry(dst.quantifier.clone()).or_insert(0) += 1;
        }
    }

    let simple_graph: Graph<Quantifier, u64> = Graph(
        simple_graph
            .into_iter()
            .map(|(src, edges)| {
                (src, { edges.into_iter().map(|(dst, count)| (count, dst)).collect() })
            })
            .collect(),
    );
    simple_graph.to_dot_file(
        &Path::new(input_path).with_extension("dot"),
        |n| n.qid.clone(),
        |e| Some(format!("{}", e)),
    )?;

    Ok(())
}

// fn collapse_internal(graph: &InstantiationGraph) {
//
// }
