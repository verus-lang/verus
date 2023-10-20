use vir::{ast::Fun, ast_util::fun_as_friendly_rust_name};

use crate::buckets::BucketId;
use crate::commands::Op;
use crate::verifier::module_name;

use std::{
    collections::{HashMap, HashSet},
    fs::File,
};

pub fn write_instantiation_graph(
    bucket_id: &BucketId,
    op: Option<&Op>,
    func_map: &HashMap<Fun, vir::ast::Function>,
    instantiation_graph: &air::profiler::InstantiationGraph,
    qid_map: &HashMap<String, vir::sst::BndInfo>,
    profile_file_name: std::path::PathBuf,
) {
    let air::profiler::InstantiationGraph { edges, nodes, names } = instantiation_graph;
    use internals_interface::*;
    let name_strs: HashSet<String> = names.values().cloned().collect();
    let quantifiers: HashMap<String, Quantifier> = name_strs
        .iter()
        .map(|n| {
            let bnd_info = qid_map.get(n);
            let kind = if n.starts_with(air::profiler::USER_QUANT_PREFIX) {
                QuantifierKind::User(UserQuantifier {
                    span: bnd_info.as_ref().unwrap().user.as_ref().unwrap().span.as_string.clone(),
                })
            } else {
                QuantifierKind::Internal
            };
            (
                n.clone(),
                std::rc::Rc::new(QuantifierX {
                    qid: n.clone(),
                    module: bnd_info.map(|b| {
                        module_name(
                            &func_map[&b.fun].x.owning_module.as_ref().expect("owning module"),
                        )
                    }),
                    kind,
                }),
            )
        })
        .collect();
    let instantiations: HashMap<(u64, usize), Instantiation> = nodes
        .iter()
        .map(|n| {
            (
                n.clone(),
                std::rc::Rc::new(InstantiationX {
                    quantifier: quantifiers[&names[n]].clone(),
                    id: *n,
                }),
            )
        })
        .collect();
    let mut graph: HashMap<Instantiation, HashSet<((), Instantiation)>> = HashMap::new();
    for (src, tgts) in edges {
        let graph_src = graph.entry(instantiations[src].clone()).or_insert(HashSet::new());
        for tgt in tgts {
            graph_src.insert(((), instantiations[tgt].clone()));
        }
    }
    let instantiations: HashSet<Instantiation> = instantiations.values().cloned().collect();
    let quantifiers = quantifiers.into_values().collect();
    let instantiation_graph = InstantiationGraph {
        bucket_name: bucket_id.to_log_string(),
        module: module_name(bucket_id.module()),
        function: op.map(|op| fun_as_friendly_rust_name(&op.get_function().x.name)),
        quantifiers,
        instantiations,
        graph: Graph(graph),
    };
    let file_name = profile_file_name.with_extension("graph");
    let f = File::create(&file_name)
        .expect(&format!("failed to open instantiation graph file {}", file_name.display()));
    instantiation_graph.serialize(f).expect("failed to write instantiation graph");
}
