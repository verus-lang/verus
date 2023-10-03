use std::{
    collections::{HashMap, HashSet, VecDeque},
    ffi::OsStr,
    path::{Path, PathBuf},
    process::exit,
};

use getopts::Options;
use qi_graph::{Graph, Instantiation, InstantiationGraph};
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
    opts.optopt("d", "output-dir", "output directory", "DIRECTORY");
    opts.optflag("a", "all", "process all graph files in a directory");

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
        PathBuf::from(matches.free[0].clone())
    } else {
        print_usage(&program, opts);
        return;
    };

    let output_dir = matches
        .opt_str("d")
        .map(|x| PathBuf::from(x))
        .unwrap_or(std::env::current_dir().expect("cannot find current directory"));

    let all = matches.opt_present("a");

    match run(&input_path, &output_dir, all) {
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
            for (dst, _) in &res {
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
    (pgraph, node_map)
}
#[derive(PartialEq, Eq, Debug, Clone)]
enum MergePolicy {
    QuantifierName,
    Module,
}
// string: merged name
// u64: unique identifier
fn merge_sibling_nodes(
    src_graph: &HashMap<Instantiation, HashMap<Instantiation, u64>>,
    insts: &Vec<Instantiation>,
    output_graph: &mut HashMap<(String, u64), HashMap<(String, u64), u64>>,
    output_list: &mut HashSet<String>,
    id_counter: &mut u64,
    merge_rule: &MergePolicy
) -> (HashMap<(String, u64), u64>, u64) {
    let mut groups = HashMap::new();
    for inst in insts.iter() {
        let node_name = if matches!(merge_rule, MergePolicy::Module) {
            inst.quantifier.module.clone()
        } else {
            Some(inst.quantifier.qid.clone())
        };
        if let Some(name) = node_name.clone() {
            output_list.insert(name);
        }
        groups.entry(node_name.clone()).or_insert(Vec::new()).push(inst.clone());
    }

    let mut result = HashMap::new();
    let mut children_total = 0;
    for (module, nodes) in groups {
        let cur_id = (module.unwrap(), *id_counter);
        *id_counter += 1;

        let group_children: HashSet<Instantiation> = nodes
            .iter()
            .flat_map(|x| {
                src_graph
                    .get(x)
                    .iter()
                    .flat_map(|x| {
                        x.iter().map(|(dst, count)| {
                            assert!(*count == 1);
                            dst
                        })
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .cloned()
            .collect();
        let (edges, total) = merge_sibling_nodes(
            src_graph,
            &group_children.iter().cloned().collect(),
            output_graph,
            output_list,
            id_counter,
            merge_rule
        );
        output_graph.insert(cur_id.clone(), edges);

        result.insert(cur_id, nodes.len() as u64 + total);
        children_total += nodes.len() as u64;
        children_total += total;
    }
    (result, children_total)
}

fn compute_module_blames(
    src_graph: &HashMap<(String, u64), HashMap<(String, u64), u64>>,
    module_list: &HashSet<String>,
) -> Vec<(String, u64)> {
    // assumes that root has been added as the single parent
    let mut blames = Vec::new();
    for module in module_list {
        // perform a traversal of the tree.
        let mut visited: HashSet<(String, u64)> = HashSet::new();
        let mut queue = VecDeque::from([("root".to_string(), 0)]);
        let mut blame = 0;
        while !queue.is_empty() {
            let head = queue.pop_front().unwrap();
            // should never be recursing on a module that matches name
            assert!(&head.0 != module);
            if !visited.contains(&head) {
                // ensure we don't visit this node again (defensive)
                visited.insert(head.clone());
                let children = src_graph.get(&head).unwrap();
                for (child, count) in children {
                    // defensive, don't think this can happen unless we have cycles
                    if !visited.contains(child) {
                        if &child.0 == module {
                            // found a matching child, add to blame
                            blame += count;
                        } else {
                            // recurse on non-match
                            queue.push_back(child.clone());
                        }
                    }
                }
            }
        }
        blames.push((module.clone(), blame));
    }
    blames
}


fn make_graph<T, S>(base_graph: HashMap<T, HashMap<T, S>>) -> Graph<T, S> 
where 
    T : Eq + std::hash::Hash, S : Eq + std::hash::Hash
{
    Graph(
        base_graph
        .into_iter()
        .map(|(src, edges)| {
            (src, { edges.into_iter().map(|(dst, count)| (count, dst)).collect() })
        })
        .collect(),
    )
    
}

fn run(input_path: &Path, output_dir: &Path, all: bool) -> Result<(), String> {
    let mut module_data: HashMap<String, Vec<ProcessFileOutput>> = HashMap::new();
    if all {
        for entry in std::fs::read_dir(input_path)
            .map_err(|e| format!("cannot read directory {} ({})", input_path.display(), e))?
        {
            let entry = entry.map_err(|e| format!("cannot stat directory entry ({})", e))?;
            if let Some(extension) = entry.path().extension().and_then(|x| x.to_str()) {
                if extension == "graph" {
                    let output = process_file(&entry.path(), output_dir)?;
                    module_data.entry(output.module.clone()).or_insert(Vec::new()).push(output);
                }
            }
        }
    } else {
        let output = process_file(input_path, output_dir)?;
        module_data.entry(output.module.clone()).or_insert(Vec::new()).push(output);
    }

    let json_value = serde_json::Value::Array(module_data.into_iter().map(|(module, data)| {
        fn module_blames_datum(datum: ProcessFileOutput) -> serde_json::Value {
            let data = serde_json::Value::Array(datum.module_blames.into_iter().map(|(module, fraction)|
                serde_json::json!({"module": module, "fraction": fraction})
            ).collect());
            serde_json::json!({
                "bucket_name": datum.bucket_name,
                "module": datum.module,
                "function": datum.function,
                "file_path" : datum.file_path,
                "module_blames": data,
            })
        }

        serde_json::json!({
            "module": module,
            "module_blames_data": serde_json::Value::Array(data.into_iter().map(module_blames_datum).collect()),
        })
    }).collect());

    let module_blames_json_str = serde_json::to_string_pretty(&json_value)
        .map_err(|x| format!("cannot format json ({x})"))?;

    let file_stem = if all {
        OsStr::new("qi-data")
    } else {
        input_path.file_stem().ok_or(format!("invalid input filename"))?
    };

    std::fs::write(
        output_dir.join(Path::new(file_stem).with_extension("json")),
        module_blames_json_str,
    )
    .map_err(|err| format!("i/o failed: {}", err))?;

    Ok(())
}

struct ProcessFileOutput {
    bucket_name: String,
    module: String,
    file_path: String,
    function: Option<String>,
    module_blames: Vec<(String, f64)>,
}

fn process_file(input_path: &Path, output_dir: &Path) -> Result<ProcessFileOutput, String> {
    dbg!(&input_path);

    let bytes = std::fs::read(input_path)
        .map_err(|_e| format!("failed to read file {}", input_path.display()))?;
    let graph: InstantiationGraph = bincode::deserialize(&bytes[..])
        .map_err(|_| format!("input {} is malformed", input_path.display()))?;
    dbg!(graph.graph.0.len());

    let mut in_deg: HashMap<Instantiation, u64> = HashMap::new();
    for (_, tgts) in &graph.graph.0 {
        for (_, tgt) in tgts {
            *in_deg.entry(tgt.clone()).or_insert(0) += 1;
        }
    }
    let max_in_deg = in_deg.iter().fold(1, |acc, (_, n)| if *n > acc { *n } else { acc });
    dbg!(max_in_deg);
    for i in 0..max_in_deg {
        let in_degree = i + 1;
        let num_nodes =
            in_deg.iter().fold(0, |acc, (_, n)| if *n == i + 1 { acc + 1 } else { acc });
        dbg!(in_degree, num_nodes);
    }
    let (pgraph, _) = convert_to_petgraph(&graph);
    let cyclic = is_cyclic_directed(&pgraph);
    dbg!(cyclic);

    let input_graph = graph
        .graph
        .0
        .into_iter()
        .map(|(src, dsts)| {
            (src, dsts.into_iter().map(|((), inst)| (inst, 1)).collect::<HashMap<_, _>>())
        })
        .collect();

    let pruned_graph =
        prune_by_predicate(&input_graph, &|src: &Instantiation| src.quantifier.module.is_some());

    let all_tgts: HashSet<Instantiation> = pruned_graph
        .iter()
        .flat_map(|(_, tgts)| tgts.iter().map(|(tgt, _)| tgt))
        .cloned()
        .collect();
    let roots: Vec<Instantiation> =
        pruned_graph.iter().map(|x| x.0).filter(|x| !all_tgts.contains(*x)).cloned().collect();

    dbg!(roots.len());

    // let simple_graph = make_graph(pruned_graph);

    let mut unique_id = 0u64;
    let mut quantifier_merged_graph: HashMap<(String, u64), HashMap<(String, u64), u64>> =
        HashMap::new();
    let mut quantifier_list = HashSet::new();
    let (top_quants, _) = merge_sibling_nodes(
        &pruned_graph,
        &roots,
        &mut quantifier_merged_graph,
        &mut quantifier_list,
        &mut unique_id,
        &MergePolicy::QuantifierName
    );
    let dummy_root = ("root".to_string(), 0);
    quantifier_merged_graph.insert(dummy_root, top_quants);

    let mut unique_id = 0u64;
    let mut module_merged_graph: HashMap<(String, u64), HashMap<(String, u64), u64>> =
        HashMap::new();
    let mut module_list = HashSet::new();
    let (top_mods, total_insts) = merge_sibling_nodes(
        &pruned_graph,
        &roots,
        &mut module_merged_graph,
        &mut module_list,
        &mut unique_id,
        &MergePolicy::Module
    );
    let dummy_root = ("root".to_string(), 0);
    module_merged_graph.insert(dummy_root, top_mods);
    dbg!(total_insts);

    let module_blames: Vec<_> = {
        let mut module_blames = compute_module_blames(&module_merged_graph, &module_list);
        module_blames.sort_unstable_by_key(|(_, cnt)| *cnt);
        module_blames
            .into_iter()
            .rev()
            .map(|(module, cnt)| (module, cnt as f64 / total_insts as f64))
            .collect()
    };


    let quant_graph = make_graph(quantifier_merged_graph);

    let simple_graph = make_graph(module_merged_graph);


    let file_stem = input_path.file_stem().ok_or(format!("invalid input filename"))?;

    simple_graph.to_dot_file(
        &output_dir.join(Path::new(file_stem).with_extension("dot")),
        |(modname, id)| format!("{} ({})", modname, id),
        // |n| format!("{} ({}, {})", n.quantifier.qid, n.id.0, n.id.1), // for pruned graph
        // |n| n.qid.clone(), // for quantifier graph
        |e| Some(format!("{}", (*e as f64 / total_insts as f64) * 100.0)),
        // |e| Some(format!("{}", e)),
    )?;

    quant_graph.to_dot_file(
        &output_dir.join(Path::new(file_stem).with_extension("quant.dot")),
        |(modname, id)| format!("{} ({})", modname, id),
        |e| Some(format!("{}", (*e as f64 / total_insts as f64) * 100.0)),
    )?;


    Ok(ProcessFileOutput {
        bucket_name: graph.bucket_name,
        module: graph.module,
        file_path: file_stem.to_str().unwrap().to_string(),
        function: graph.function,
        module_blames,
    })
}
