//! Analyzes prover performance of the SMT solver

use crate::messages::{Diagnostics, MessageLevel};
use std::collections::HashSet;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::BufRead;
use z3tracer::model::QuantCost;
use z3tracer::syntax::{MatchedTerm, QiFrame, QiKey};
use z3tracer::{Model, ModelConfig};

pub const PROVER_LOG_FILE: &str = "verus-prover-trace.log";

pub const USER_QUANT_PREFIX: &str = "user_";
pub const INTERNAL_QUANT_PREFIX: &str = "internal_";

/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
    //log_path: String,
    quantifier_stats: Vec<QuantCost>,
    instantiation_graph: Option<InstantiationGraph>,
}

pub struct InstantiationGraph {
    pub edges: HashMap<(u64, usize), HashSet<(u64, usize)>>,
    pub names: HashMap<(u64, usize), String>,
    pub nodes: HashSet<(u64, usize)>,
}

#[derive(Debug)]
pub enum ProfilerError {
    InvalidTrace(String),
}

impl std::fmt::Display for ProfilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProfilerError::InvalidTrace(e) => write!(f, "invalid trace: {}", e),
        }
    }
}

impl Profiler {
    /// Instantiate a new (singleton) profiler
    pub fn parse(
        message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
        filename: &std::path::Path,
        description: Option<&str>,
        progress_bar: bool,
        diagnostics: &impl Diagnostics,
        compute_instantiation_graph: bool,
    ) -> Result<Self, ProfilerError> {
        let path = filename;

        // Count the number of lines
        let file = std::io::BufReader::new(
            std::fs::File::open(path).expect("Failed to open prover trace log"),
        );
        let line_count = file.lines().count();

        // Reset to actually parse the file
        let file = std::io::BufReader::new(
            std::fs::File::open(path).expect("Failed to open prover trace log"),
        );
        let mut model_config = ModelConfig::default();
        model_config.parser_config.skip_z3_version_check = true;
        model_config.parser_config.ignore_invalid_lines = true;
        model_config.parser_config.show_progress_bar = progress_bar;
        model_config.skip_log_consistency_checks = true;
        model_config.log_internal_term_equalities = false;
        model_config.log_term_equalities = false;
        let mut model = Model::new(model_config);
        if let Some(description) = description {
            diagnostics.report_now(&message_interface.bare(
                MessageLevel::Note,
                &format!("Analyzing prover log for {} ...", description),
            ));
        }
        let _ = model
            .process(
                Some(path.to_str().expect("invalid profile file path").to_owned()),
                file,
                line_count,
            )
            .map_err(|e| ProfilerError::InvalidTrace(e.to_string()))?;
        if let Some(description) = description {
            diagnostics.report_now(
                &message_interface.bare(
                    MessageLevel::Note,
                    &format!("Log analysis complete for {}", description),
                ),
            );
        }

        let instantiation_graph =
            compute_instantiation_graph.then(|| Self::make_instantiation_graph(&model));

        // Analyze the quantifer costs
        let quant_costs = model.quant_costs();
        let mut user_quant_costs = quant_costs
            .into_iter()
            .filter(|cost| cost.quant.starts_with(USER_QUANT_PREFIX))
            .collect::<Vec<_>>();
        user_quant_costs.sort_by_key(|v| v.instantiations * v.cost);
        user_quant_costs.reverse();

        Ok(Profiler { message_interface, quantifier_stats: user_quant_costs, instantiation_graph })
    }

    pub fn instantiation_graph(&self) -> Option<&InstantiationGraph> {
        self.instantiation_graph.as_ref()
    }

    fn make_instantiation_graph(model: &Model) -> InstantiationGraph {
        let quantifier_inst_matches =
            model.instantiations().iter().filter(|(_, quant_inst)| match quant_inst.frame {
                QiFrame::Discovered { .. } => false,
                QiFrame::NewMatch { .. } => true,
            });

        // Track which instantiations caused which enodes to appear
        let mut term_blame = HashMap::new();
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            for inst in &quant_inst.instances {
                for node_ident in &inst.enodes {
                    term_blame.insert(node_ident, qi_key);
                }
            }
        }

        // Create a graph over QuantifierInstances,
        // where U->V if U produced an e-term that
        // triggered V
        let mut graph: BTreeMap<QiKey, BTreeSet<QiKey>> = BTreeMap::new();
        for (qi_key, _) in quantifier_inst_matches.clone() {
            graph.insert(*qi_key, BTreeSet::new());
        }
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            match &quant_inst.frame {
                QiFrame::Discovered { .. } => {
                    panic!("We filtered out all of the Discovered instances already!")
                }
                QiFrame::NewMatch { used: u, .. } => {
                    for used in u.iter() {
                        match used {
                            MatchedTerm::Trigger(t) => {
                                match term_blame.get(&t) {
                                    None => (), //println!("Nobody to blame for {:?}", t),
                                    Some(qi_responsible) =>
                                    // Quantifier instantiation that produced the triggering term
                                    {
                                        if let Some(resp_edges) = graph.get_mut(&qi_responsible) {
                                            resp_edges.insert(*qi_key);
                                        } else {
                                            panic!("Responsible qikey not found!")
                                        }
                                        ()
                                    }
                                }
                            }
                            MatchedTerm::Equality(_t1, _t2) => (), // TODO: Unclear whether/how to use this case
                        }
                    }
                }
            }
        }
        {
            let mut edges: HashMap<(u64, usize), HashSet<(u64, usize)>> = HashMap::new();
            let mut nodes: HashSet<QiKey> = HashSet::new();
            for (src, tgts) in graph.iter() {
                nodes.insert(*src);
                for tgt in tgts {
                    edges
                        .entry((src.key, src.version))
                        .or_insert(std::collections::HashSet::new())
                        .insert((tgt.key, tgt.version));
                    nodes.insert(*tgt);
                }
            }
            let names: HashMap<(u64, usize), String> = nodes
                .iter()
                .map(|k| {
                    let ident = model.instantiations().get(&k).unwrap().frame.quantifier();
                    let name = model.term(ident).expect("not found").name().unwrap();
                    ((k.key, k.version), name.to_owned())
                })
                .collect();
            let nodes = nodes.into_iter().map(|k| (k.key, k.version)).collect();

            InstantiationGraph { edges, names, nodes }
        }
    }

    pub fn quant_count(&self) -> usize {
        self.quantifier_stats.len()
    }

    pub fn total_instantiations(&self) -> u64 {
        self.quantifier_stats.iter().fold(0, |acc, cost| acc + cost.instantiations)
    }

    pub fn print_raw_stats(&self, diagnostics: &impl Diagnostics) {
        for cost in &self.quantifier_stats {
            let count = cost.instantiations;
            let msg = format!(
                "Instantiated {} {} times ({}% of the total)\n",
                cost.quant,
                count,
                100 * count / self.total_instantiations()
            );
            diagnostics.report(&self.message_interface.bare(MessageLevel::Note, msg.as_str()));
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &QuantCost> + '_ {
        self.quantifier_stats.iter()
    }
}
