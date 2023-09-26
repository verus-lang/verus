use std::{
    collections::{HashMap, HashSet},
    path::Path,
    process::exit,
};

use getopts::Options;
use qi_graph::{Graph, Instantiation, InstantiationGraph, QuantifierKind, UserQuantifier};
// use qi_graph::Quantifier;

use petgraph::algo::is_cyclic_directed;
use petgraph::graph::NodeIndex;
use petgraph::Graph as PGraph;
// use petgraph::visit::DfsPostOrder;
// use petgraph::Direction;

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

/// Takes a graph and predicate on quantifier/instantiations, and keeps the nodes that satisfy the predicate
/// for those that don't collapse, remove the node, and stitch all parents to point at its children
/// recursively
fn prune_by_predicate<T>(
    input_graph: &HashMap<T, HashMap<T, u64>>,
    predicate: &dyn Fn(&T) -> bool,
) -> HashMap<T, HashMap<T, u64>>
where
    T: Eq + PartialEq + std::hash::Hash + Clone,
{
    // remove the nodes in the graph relating to internal nodes
    let mut pruned_graph: HashMap<T, HashMap<T, u64>> = HashMap::new();
    for (src, dsts) in input_graph {
        // only add back in the nodes satisfying predicate as sources
        if predicate(src) {
            // function to traverse down the non-internal dsts of a source
            fn compute_final_edges<T>(
                visited: &mut HashSet<T>,
                graph: &HashMap<T, HashMap<T, u64>>,
                predicate: &dyn Fn(&T) -> bool,
                dsts: &HashMap<T, u64>,
            ) -> HashMap<T, u64>
            where
                T: Eq + PartialEq + std::hash::Hash + Clone,
            {
                let mut pruned_edges: HashMap<T, u64> = HashMap::new();
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
                            let res = if let Some(new_dsts) = graph.get(dst) {
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
            let res = compute_final_edges(&mut HashSet::new(), input_graph, predicate, &dsts);
            for (dst, cnt) in &res {
                assert!(predicate(dst));
            }
            assert!(predicate(src));
            // clean the hashmaps of the destinations
            pruned_graph.insert(src.clone(), res);
        }
    }
    pruned_graph
}

fn convert_to_petgraph(
    graph: &InstantiationGraph,
) -> (PGraph<Instantiation, ()>, HashMap<Instantiation, NodeIndex>) {
    let mut pgraph: PGraph<Instantiation, ()> = PGraph::new();
    let mut node_map = HashMap::new();
    let mut inst_set = HashSet::new();
    for (src, tgts) in &graph.graph.0 {
        inst_set.insert(src.clone());
        for (_, tgt) in tgts {
            inst_set.insert(tgt.clone());
        }
    }
    for inst in &inst_set {
        let x = pgraph.add_node(inst.clone());
        node_map.insert(inst.clone(), x);
    }

    for (src, tgts) in &graph.graph.0 {
        let src_node = node_map.get(src).unwrap();
        for (_, tgt) in tgts {
            let tgt_node = node_map.get(tgt).unwrap();
            pgraph.add_edge(src_node.clone(), tgt_node.clone(), ());
        }
    }
    (pgraph , node_map)
}
// string: Module name
// u64: uniue identifier
fn merge_sibling_nodes(
    src_graph: &HashMap<Instantiation, HashMap<Instantiation, u64>>,
    insts: &Vec<Instantiation>,
    module_graph: &mut HashMap<(String, u64), HashMap<(String, u64), u64>>,
    id_counter: &mut u64,
) -> (HashMap<(String, u64), u64>, u64) {
    let mut groups = HashMap::new();
    for inst in insts.iter() {
        let module = inst.quantifier.module.clone();
        groups.entry(module.clone()).or_insert(Vec::new()).push(inst.clone());
    }

    let mut result = HashMap::new();
    let mut children_total = 0;
    for (module, nodes) in groups {
        let cur_id = (module.unwrap(), *id_counter);
        *id_counter += 1;

        let group_children: HashSet<Instantiation> = nodes
            .iter()
            .flat_map(|x| {
                src_graph.get(x).iter().flat_map(|x| x.iter().map(|(dst, count)| {
                    assert!(*count == 1);
                    dst
                })).collect::<Vec<_>>().into_iter()
            })
            .cloned()
            .collect();
        let (edges, total) = merge_sibling_nodes(
            src_graph,
            &group_children.iter().cloned().collect(),
            module_graph,
            id_counter,
        );
        module_graph.insert(cur_id.clone(), edges);

        result.insert(cur_id, nodes.len() as u64 + total);
        children_total += nodes.len() as u64;
        children_total += total;
    }
    (result, children_total)
}

fn run(input_path: &str) -> Result<(), String> {
    let bytes =
        std::fs::read(input_path).map_err(|_e| format!("failed to read file {input_path}"))?;
    let graph: InstantiationGraph =
        bincode::deserialize(&bytes[..]).map_err(|_| format!("input {input_path} is malformed"))?;
    dbg!(graph.graph.0.len());

    let mut in_deg : HashMap<Instantiation, u64> = HashMap::new();
    for (_, tgts) in &graph.graph.0 {
        for (_, tgt) in tgts {
            *in_deg.entry(tgt.clone()).or_insert(0) += 1;
        }
    }
    let max_in_deg = in_deg.iter().fold(1, |acc, (_, n)| {if *n > acc {*n} else {acc} });
    dbg!(max_in_deg);
    for i in 0..max_in_deg {
        let in_degree = i + 1; 
        let num_nodes = in_deg.iter().fold(0, |acc, (_, n)| {if *n == i + 1 {acc + 1} else {acc} });
        dbg!(in_degree, num_nodes);
    }
    let (pgraph, _) = convert_to_petgraph(&graph);
    let cyclic = is_cyclic_directed(&pgraph);
    dbg!(cyclic);

    // let mut simple_graph: HashMap<Quantifier, HashMap<Quantifier, u64>> = HashMap::new();
    // for (src, dsts) in graph.graph.0 {
    //     let new_src = simple_graph.entry(src.quantifier.clone()).or_insert(HashMap::new());
    //     for (_edge, dst) in dsts {
    //         *new_src.entry(dst.quantifier.clone()).or_insert(0) += 1;
    //     }
    // }
    // 
    // let pruned_graph = prune_by_predicate(&simple_graph, &|src: &Quantifier| {
    //     src.kind != QuantifierKind::Internal
    // });

    // let simple_graph: Graph<Quantifier, u64> = Graph(
    //     pruned_graph
    //         .into_iter()
    //         .map(|(src, edges)| {
    //             (src, { edges.into_iter().map(|(dst, count)| (count, dst)).collect() })
    //         })
    //         .collect(),
    // );

    let input_graph = graph
        .graph
        .0
        .into_iter()
        .map(|(src, dsts)| {
           (src, dsts.into_iter().map(|((), inst)| (inst, 1)).collect::<HashMap<_, _>>())
        })
        .collect();

    let pruned_graph = prune_by_predicate(&input_graph, &|src: &Instantiation| {
        src.quantifier.module.is_some()
    });

    // let module_sets = pruned_graph.iter().fold(HashSet::new(), |(src, tgts)| {});

    let all_tgts : HashSet<Instantiation> = pruned_graph.iter().flat_map(|(src, tgts)| { tgts.iter().map(|(tgt, _)| tgt)} ).cloned().collect();
    let roots : Vec<Instantiation> = pruned_graph
        .iter()
        .map(|x| x.0)
        .filter(|x| !all_tgts.contains(*x))
        .cloned()
        .collect();

    dbg!(roots.len());


    // let simple_graph: Graph<Instantiation, u64> = Graph(
    //     pruned_graph
    //         .into_iter()
    //         .map(|(src, edges)| {
    //             (src, { edges.into_iter().map(|(dst, count)| (count, dst)).collect() })
    //         })
    //         .collect(),
    // );

    let mut unique_id = 0u64;
    let mut module_merged_graph: HashMap<(String, u64), HashMap<(String, u64), u64>> =
        HashMap::new();
    let (_, total_insts) = merge_sibling_nodes(
        &pruned_graph,
        &roots,
        &mut module_merged_graph,
        &mut unique_id,
    );
    dbg!(total_insts);

    let simple_graph: Graph<(String, u64), u64> = Graph(
        module_merged_graph
            .into_iter()
            .map(|(src, edges)| {
                (src, { edges.into_iter().map(|(dst, count)| (count, dst)).collect() })
            })
            .collect(),
    );

    simple_graph.to_dot_file(
        &Path::new(input_path).with_extension("dot"),
        | (modname, id) | format!("{} ({})", modname, id),
        // |n| format!("{} ({}, {})", n.quantifier.qid, n.id.0, n.id.1), // for pruned graph
        // |n| n.qid.clone(), // for quantifier graph
        |e| Some(format!("{}", e)),
    )?;

    Ok(())
}
