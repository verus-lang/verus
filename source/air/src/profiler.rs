//! Analyzes prover performance of the SMT solver

use crate::messages::{Diagnostics, MessageLevel};
use std::io::BufRead;
use std::io::Write;
use std::collections::{HashMap, BTreeMap, BTreeSet};
use z3tracer::syntax::{QiFrame, QiKey, MatchedTerm};
use z3tracer::model::QuantCost;
// use z3tracer::model::QuantCause;
use z3tracer::{Model, ModelConfig};

pub const PROVER_LOG_FILE: &str = "verus-prover-trace.log";

pub const USER_QUANT_PREFIX: &str = "user_";
pub const INTERNAL_QUANT_PREFIX: &str = "internal_";

/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
    //log_path: String,
    quantifier_stats: Vec<QuantCost>,
    // pub quantifier_causes: Vec<QuantCause>,
}

impl Profiler {
    /// Instantiate a new (singleton) profiler
    pub fn new(
        message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
        filename: &std::path::Path,
        diagnostics: &impl Diagnostics,
    ) -> Self {
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
        model_config.skip_log_consistency_checks = true;
        model_config.log_internal_term_equalities = false;
        model_config.log_term_equalities = false;
        let mut model = Model::new(model_config);
        diagnostics.report(&message_interface.bare(MessageLevel::Note, "Analyzing prover log..."));
        let _ = model
            .process(
                Some(path.to_str().expect("invalid profile file path").to_owned()),
                file,
                line_count,
            )
            .expect("Error processing prover trace");
        diagnostics.report(&message_interface.bare(MessageLevel::Note, "... analysis complete\n"));

        Self::print_quant_graph(path, &model);

        // Analyze the quantifer costs
        let quant_costs = model.quant_costs();
        let mut user_quant_costs = quant_costs
            .into_iter()
            .filter(|cost| cost.quant.starts_with(USER_QUANT_PREFIX))
            .collect::<Vec<_>>();
        user_quant_costs.sort_by_key(|v| v.instantiations * v.cost);
        user_quant_costs.reverse();

        // let quant_causes = model.quant_causes(); 
        // let mut user_quant_causes = quant_causes
        //     .into_iter()
        //     .filter(|cost| cost.quant.starts_with(USER_QUANT_PREFIX))
        //     .collect::<Vec<_>>();
        // user_quant_causes.sort_by_key(|qc| qc.instantiations);
        // user_quant_causes.reverse();

        Profiler { message_interface, quantifier_stats: user_quant_costs }
        // Profiler { message_interface, quantifier_stats: user_quant_costs, quantifier_causes : user_quant_causes }
    }

    fn print_quant_graph(path: &std::path::Path, model : &Model) {
        let quantifier_inst_matches =
            model.instantiations()
                .iter()
                .filter(|(_, quant_inst)| match quant_inst.frame {
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
        let mut graph : BTreeMap<QiKey, BTreeSet<QiKey>> = BTreeMap::new();
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
            let mut seen_edges = HashMap::new();
            for (src, tgts) in graph.iter() {
                let src_ident = model.instantiations().get(src).unwrap().frame.quantifier();
                let src_name = model.term(src_ident).expect("not found").name().unwrap();
                for tgt in tgts {
                    let tgt_ident = model.instantiations().get(tgt).unwrap().frame.quantifier();
                    let tgt_name = model.term(tgt_ident).expect("not found").name().unwrap();
                    let key = (src_name, tgt_name);
                    *seen_edges.entry(key).or_insert(0) += 1;
                }
            }

            let mut file = std::fs::File::create(path.with_extension("dot")).expect("couldn't create dot file"); 
            writeln!(&mut file, "digraph M {{").expect("failed to write instantiation graph");
            writeln!(&mut file, "  rankdir=LR;").expect("failed to write instantiation graph");
            for ((src_name, tgt_name), count) in seen_edges.iter() {
                writeln!(&mut file, "  \"{}\" -> \"{}\" [ label = \"{}\"];", src_name, tgt_name, count).expect("failed to write instantiation graph");
            }
            writeln!(&mut file, "}}").expect("failed to write call graph");
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
