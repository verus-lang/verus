//! Analyzes prover performance of the SMT solver

use crate::messages::{Diagnostics, MessageLevel};
use smt_scope::analysis::{InstGraph, RawNodeIndex};
use smt_scope::items::QuantIdx;
use smt_scope::parsers::LogParser;
use smt_scope::parsers::z3::Z3Parser;
use std::collections::{HashMap, HashSet};

pub const PROVER_LOG_FILE: &str = "verus-prover-trace.log";

pub const USER_QUANT_PREFIX: &str = "user_";
pub const INTERNAL_QUANT_PREFIX: &str = "internal_";

/// Quantifier cost statistics
#[derive(Debug, Clone)]
pub struct QuantCost {
    pub quant: String,
    pub instantiations: u64,
    pub cost: u64,
}

/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
    //log_path: String,
    quantifier_stats: Vec<QuantCost>,
    instantiation_graph: InstantiationGraph,
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
    fn make_instantiation_graph(
        parser: &Z3Parser,
        inst_graph: &InstGraph,
    ) -> Result<InstantiationGraph, ProfilerError> {
        // Convert smt-scope's graph structure to our InstantiationGraph format
        let mut edges: HashMap<(u64, usize), HashSet<(u64, usize)>> = HashMap::new();
        let mut names: HashMap<(u64, usize), String> = HashMap::new();
        let mut nodes: HashSet<(u64, usize)> = HashSet::new();

        for (inst_idx, inst) in parser.instantiations().iter_enumerated() {
            let inst_id = (usize::from(inst_idx) as u64, 0); // Convert InstIdx to (u64, usize) tuple
            nodes.insert(inst_id);

            // Get the quantifier name for this instantiation
            // We need to provide a name for all instantiations, not just user quantifiers
            let match_data = &parser[inst.match_];
            let name = if let Some(quant_idx) = match_data.kind.quant_idx() {
                let quant = &parser.quantifiers()[quant_idx];
                if let Some(name_istring) = quant.kind.user_name() {
                    parser[name_istring].to_string()
                } else {
                    // For quantifiers without user names, use a default name based on the index
                    format!("quant_{:?}", quant_idx)
                }
            } else {
                // For non-quantifier matches (e.g., theory solving), generate a name
                match &match_data.kind {
                    smt_scope::items::MatchKind::TheorySolving { axiom_id, .. } => {
                        format!("theory_{:?}", axiom_id)
                    }
                    smt_scope::items::MatchKind::Axiom { axiom, .. } => {
                        format!("axiom_{:?}", axiom)
                    }
                    smt_scope::items::MatchKind::MBQI { quant, .. } => {
                        format!("mbqi_{:?}", quant)
                    }
                    _ => format!("unknown_inst_{}", usize::from(inst_idx)),
                }
            };
            names.insert(inst_id, name);

            // Get dependencies from the instantiation graph
            use petgraph::visit::EdgeRef;
            let raw_graph = &inst_graph.raw;
            let node_idx = RawNodeIndex::from(usize::from(inst_idx));

            for edge in raw_graph.graph.edges_directed(node_idx.0, petgraph::Direction::Outgoing) {
                let target_idx = edge.target().index();
                let target_id = (target_idx as u64, 0);
                nodes.insert(target_id);
                edges.entry(inst_id).or_insert_with(HashSet::new).insert(target_id);
            }
        }

        // Ensure all nodes have names (some might have been added via edges)
        for node_id in &nodes {
            if !names.contains_key(node_id) {
                // This shouldn't happen if we iterated through all instantiations,
                // but add a fallback just in case
                names.insert(*node_id, format!("unknown_node_{}", node_id.0));
            }
        }

        Ok(InstantiationGraph { edges, names, nodes })
    }

    fn compute_quantifier_costs(
        parser: &Z3Parser,
        inst_graph: &InstGraph,
    ) -> Result<Vec<QuantCost>, ProfilerError> {
        let graph = &inst_graph.raw.graph;

        // Extract costs from the graph nodes (smt-scope already computed them)
        // Map from InstIdx to cost
        let mut inst_costs: HashMap<usize, f64> = HashMap::new();

        for node_idx in graph.node_indices() {
            if let Some(node) = graph.node_weight(node_idx) {
                // The node index corresponds to the instantiation index
                let inst_idx = node_idx.index();
                inst_costs.insert(inst_idx, node.cost);
            }
        }

        // Aggregate costs per quantifier
        let mut quant_data: HashMap<QuantIdx, (u64, f64)> = HashMap::new();

        // iterate through all instantiations (`[instance]` in z3 trace files)
        for (inst_idx, inst) in parser.instantiations().iter_enumerated() {
            let match_data = &parser[inst.match_];
            if let Some(quant_idx) = match_data.kind.quant_idx() {
                let idx_usize = usize::from(inst_idx);
                let inst_cost = inst_costs.get(&idx_usize).copied().unwrap_or(1.0);

                let entry = quant_data.entry(quant_idx).or_insert((0, 0.0));
                entry.0 += 1; // count
                entry.1 += inst_cost; // total cost
            }
        }

        // Build QuantCost entries for user quantifiers
        let user_quant_costs_per_idx: Vec<QuantCost> = quant_data
            .into_iter()
            .filter_map(|(quant_idx, (count, total_cost))| {
                let quant = &parser.quantifiers()[quant_idx];
                if let Some(name_istring) = quant.kind.user_name() {
                    let name_str = &parser[name_istring];
                    if name_str.starts_with(USER_QUANT_PREFIX) {
                        return Some(QuantCost {
                            quant: name_str.to_string(),
                            instantiations: count,
                            cost: total_cost.round() as u64,
                        });
                    }
                }
                None
            })
            .collect();

        // Merge entries with the same quantifier name
        // there are multiple QuantIdx values for the same user-defined quantifier
        let mut merged: HashMap<String, (u64, f64)> = HashMap::new();
        for cost in user_quant_costs_per_idx {
            let entry = merged.entry(cost.quant).or_insert((0, 0.0));
            entry.0 += cost.instantiations;
            entry.1 += cost.cost as f64; // cost is total cost for this QuantIdx
        }
        let mut user_quant_costs: Vec<QuantCost> = merged
            .into_iter()
            .map(|(quant, (instantiations, total_cost))| QuantCost {
                quant,
                instantiations,
                cost: total_cost.round() as u64,
            })
            .collect();

        // Sort by total cost * instantiations
        user_quant_costs.sort_by_key(|v| v.instantiations * v.cost);
        user_quant_costs.reverse();

        Ok(user_quant_costs)
    }

    /// Instantiate a new (singleton) profiler
    pub fn parse(
        message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
        filename: &std::path::Path,
        description: Option<&str>,
        diagnostics: &impl Diagnostics,
    ) -> Result<Self, ProfilerError> {
        if let Some(description) = description {
            diagnostics.report_now(&message_interface.bare(
                MessageLevel::Note,
                &format!("Analyzing prover log for {} ...", description),
            ));
        }

        let (_, stream_parser) = Z3Parser::from_file(filename)
            .map_err(|e| ProfilerError::InvalidTrace(format!("Failed to parse file: {}", e)))?;

        let parser = stream_parser
            .process_all()
            .map_err(|e| ProfilerError::InvalidTrace(format!("Failed to process log: {}", e)))?;

        // Build instantiation graph once and pass to both functions
        let inst_graph = InstGraph::new(&parser).map_err(|e| {
            ProfilerError::InvalidTrace(format!("Failed to build instantiation graph: {:?}", e))
        })?;

        let instantiation_graph = Self::make_instantiation_graph(&parser, &inst_graph)?;
        let user_quant_costs = Self::compute_quantifier_costs(&parser, &inst_graph)?;

        if let Some(description) = description {
            diagnostics.report_now(
                &message_interface.bare(
                    MessageLevel::Note,
                    &format!("Log analysis complete for {}", description),
                ),
            );
        }

        Ok(Profiler { message_interface, quantifier_stats: user_quant_costs, instantiation_graph })
    }

    pub fn instantiation_graph(&self) -> &InstantiationGraph {
        &self.instantiation_graph
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
