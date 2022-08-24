//! Analyzes prover performance of the SMT solver

use std::io::BufRead;
use z3tracer::model::QuantCost;
use z3tracer::{Model, ModelConfig};

pub const PROVER_LOG_FILE: &str = "verus-prover-trace.log";

pub const USER_QUANT_PREFIX: &str = "user_";
pub const INTERNAL_QUANT_PREFIX: &str = "internal_";

#[derive(Debug)]
/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    //log_path: String,
    quantifier_stats: Vec<QuantCost>,
}

impl Profiler {
    /// Instantiate a new (singleton) profiler
    pub fn new() -> Profiler {
        let path = PROVER_LOG_FILE;

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
        let mut model = Model::new(model_config);
        println!("Analyzing prover log...");
        let _ = model
            .process(Some(path.to_string()), file, line_count)
            .expect("Error processing prover trace");
        println!("... analysis complete\n");

        // Analyze the quantifer costs
        let quant_costs = model.quant_costs();
        let mut user_quant_costs = quant_costs
            .into_iter()
            .filter(|cost| cost.quant.starts_with(USER_QUANT_PREFIX))
            .collect::<Vec<_>>();
        user_quant_costs.sort_by_key(|v| v.instantiations * v.cost);
        user_quant_costs.reverse();

        Profiler { quantifier_stats: user_quant_costs }
    }

    pub fn quant_count(&self) -> usize {
        self.quantifier_stats.len()
    }

    pub fn total_instantiations(&self) -> u64 {
        self.quantifier_stats.iter().fold(0, |acc, cost| acc + cost.instantiations)
    }

    pub fn print_raw_stats(&self) {
        for cost in &self.quantifier_stats {
            let count = cost.instantiations;
            println!(
                "Instantiated {} {} times ({}% of the total)",
                cost.quant,
                count,
                100 * count / self.total_instantiations()
            );
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &QuantCost> + '_ {
        self.quantifier_stats.iter()
    }
}

pub mod simple {
    use std::collections::HashMap;
    use std::io::BufRead;
    use z3tracer::error::RawResult;
    use z3tracer::syntax::*;

    struct SimpleProfiler {
        terms: std::collections::BTreeMap<Ident, Term>,
        instantiations: HashMap<Ident, u64>,
    }

    impl z3tracer::parser::LogVisitor for &mut SimpleProfiler {
        fn add_term(&mut self, ident: Ident, term: Term) -> RawResult<()> {
            self.terms.insert(ident, term);
            Ok(())
        }

        fn add_instantiation(
            &mut self,
            _key: QiKey,
            frame: QiFrame,
        ) -> z3tracer::error::RawResult<()> {
            if let z3tracer::syntax::QiFrame::NewMatch { ref quantifier, .. } = frame {
                *self.instantiations.entry(quantifier.to_owned()).or_insert(0) += 1;
            }
            Ok(())
        }

        fn start_instance(&mut self, _key: QiKey, _instance: QiInstance) -> RawResult<()> {
            Ok(())
        }

        fn end_instance(&mut self) -> RawResult<()> {
            Ok(())
        }

        fn add_equality(&mut self, _id: Ident, _eq: Equality) -> RawResult<()> {
            Ok(())
        }

        fn attach_meaning(&mut self, _id: Ident, _m: Meaning) -> RawResult<()> {
            Ok(())
        }

        fn attach_var_names(&mut self, _id: Ident, _names: Vec<VarName>) -> RawResult<()> {
            Ok(())
        }

        fn attach_enode(&mut self, _id: Ident, _generation: u64) -> RawResult<()> {
            Ok(())
        }

        fn tool_version(&mut self, _s1: String, _s2: String) -> RawResult<()> {
            Ok(())
        }

        fn begin_check(&mut self, _i: u64) -> RawResult<()> {
            Ok(())
        }

        fn assign(&mut self, _lit: Literal, _s: String) -> RawResult<()> {
            Ok(())
        }

        fn conflict(&mut self, _lits: Vec<Literal>, _s: String) -> RawResult<()> {
            Ok(())
        }

        fn push(&mut self, _level: u64) -> RawResult<()> {
            Ok(())
        }

        fn pop(&mut self, _num: u64, _current_level: u64) -> RawResult<()> {
            Ok(())
        }

        fn resolve_lit(&mut self, _i: u64, _lit: Literal) -> RawResult<()> {
            Ok(())
        }

        fn resolve_process(&mut self, _lit: Literal) -> RawResult<()> {
            Ok(())
        }
    }

    const PARSER_CONFIG: z3tracer::parser::ParserConfig =
        z3tracer::parser::ParserConfig { skip_z3_version_check: true, ignore_invalid_lines: true };

    impl SimpleProfiler {
        fn new() -> Self {
            SimpleProfiler {
                instantiations: HashMap::new(),
                terms: std::collections::BTreeMap::new(),
            }
        }

        /// Process some input.
        fn process<R>(
            &mut self,
            path_name: Option<String>,
            input: R,
            line_count: usize,
        ) -> Result<(), ()>
        where
            R: std::io::BufRead,
        {
            let lexer = z3tracer::lexer::Lexer::new(path_name, input, line_count);
            z3tracer::parser::Parser::new(PARSER_CONFIG, lexer, self).parse().map_err(|_| ())
        }

        fn instantiations(&self) -> Vec<(String, u64, Vec<(String, u64)>)> {
            let mut quantifier_counts = HashMap::new();
            for (ident, count) in self.instantiations.iter() {
                let quant_name = match &self.terms[&ident] {
                    Term::Quant { name, .. } => name,
                    _ => panic!("Term for quantifier isn't a Quant"),
                };
                let (ref mut curr_count, ref mut ident_counts) =
                    quantifier_counts.entry(quant_name.clone()).or_insert((0, HashMap::new()));
                *curr_count += count;
                *ident_counts.entry(ident).or_insert(0) += count;
            }
            let mut quantifier_counts: Vec<_> = quantifier_counts
                .into_iter()
                .map(|(qid, (count, icounts))| {
                    (qid, count, {
                        let mut icounts: Vec<(String, u64)> = icounts
                            .into_iter()
                            .map(|(id, icount)| (format!("{:?}", id), icount))
                            .collect();
                        icounts.sort_by_key(|(_, c)| u64::MAX - *c);
                        icounts
                    })
                })
                .collect();
            quantifier_counts.sort_by_key(|(_, c, _)| u64::MAX - *c);
            quantifier_counts
        }
    }

    pub fn profile() -> Vec<(String, u64, Vec<(String, u64)>)> {
        let path = super::PROVER_LOG_FILE;

        // Count the number of lines
        let file = std::io::BufReader::new(
            std::fs::File::open(path).expect("Failed to open prover trace log"),
        );
        let line_count = file.lines().count();

        // Reset to actually parse the file
        let file = std::io::BufReader::new(
            std::fs::File::open(path).expect("Failed to open prover trace log"),
        );

        let mut profile = SimpleProfiler::new();
        println!("Analyzing prover log...");
        let _ = profile
            .process(Some(path.to_string()), file, line_count)
            .expect("Error processing prover trace");
        println!("... analysis complete\n");

        profile.instantiations()
    }
}
