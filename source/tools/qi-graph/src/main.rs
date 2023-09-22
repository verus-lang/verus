use std::{collections::{HashMap, HashSet}, path::Path, process::exit};

use getopts::Options;
use qi_graph::{Graph, InstantiationGraph, Quantifier, QuantifierKind};

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

/// Takes a graph and predicate on quantifier, and keeps the nodes that satisfy the predicate
/// for those that don't collapse, remove the node, and stitch all parents to point at its children
/// recursively
fn prune_by_predicate(
    simple_graph: &HashMap<Quantifier, HashMap<Quantifier, u64>>,
    predicate: &dyn Fn(&Quantifier) -> bool,
) -> HashMap<Quantifier, HashMap<Quantifier, u64>> {
     // remove the nodes in the graph relating to internal nodes
    let mut pruned_graph: HashMap<Quantifier, HashMap<Quantifier, u64>> = HashMap::new();
    for (src, dsts) in simple_graph {
        // only add back in the nodes satisfying predicate as sources
        if predicate(src) {
            // function to traverse down the non-internal dsts of a source
            fn compute_final_edges(
                visited : &mut HashSet<Quantifier>,
                graph : &HashMap<Quantifier, HashMap<Quantifier, u64>>, 
                predicate: &dyn Fn(&Quantifier) -> bool,
                dsts : &HashMap<Quantifier, u64>) -> HashMap<Quantifier, u64> {
                let mut pruned_edges : HashMap<Quantifier, u64> = HashMap::new();
                // Ex: #1 -> {#2, #3, #4} , #4 internal
                for (dst, count) in dsts {
                    if predicate(dst) {
                        // #2 and #3 directly get added to pruned
                        *pruned_edges.entry(dst.clone()).or_insert(0) += count;                    
                    } else {
                        // don't repeatedly add the same sources in case of cycle
                        if !visited.contains(dst) {
                            visited.insert(dst.clone());
                            // #4 -> {#5, #6}
                            let res = 
                                if let Some(new_dsts) = graph.get(dst) {
                                    compute_final_edges(visited, graph, predicate, new_dsts)
                                } else {
                                    HashMap::new()
                                };
                            // final result: #1 -> {#2, #3, #5, #6}
                            for (new_dst, new_count) in res {
                                assert!(predicate(&new_dst));
                                *pruned_edges.entry(new_dst.clone()).or_insert(0) += new_count;
                            }
                        }
                    }
                }
                pruned_edges
            }
            let res = compute_final_edges(&mut HashSet::new(), simple_graph, predicate, &dsts) ;
            // clean the hashmaps of the destinations
            pruned_graph.insert(src.clone(), res);
        }
    }
    pruned_graph   
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

    let pruned_graph = prune_by_predicate(&simple_graph, &|src : &Quantifier| {src.kind != QuantifierKind::Internal});

    let simple_graph: Graph<Quantifier, u64> = Graph(
        pruned_graph
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
