//! Analyzes prover performance of the SMT solver

use crate::messages::{Diagnostics, MessageLevel};
use std::io::BufRead;
use z3tracer::model::QuantCost;
use z3tracer::{Model, ModelConfig};

pub const PROVER_LOG_FILE: &str = "verus-prover-trace.log";

pub const USER_QUANT_PREFIX: &str = "user_";
pub const INTERNAL_QUANT_PREFIX: &str = "internal_";

/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
    //log_path: String,
    quantifier_stats: Vec<QuantCost>,
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

        // Analyze the quantifer costs
        let quant_costs = model.quant_costs();
        let mut user_quant_costs = quant_costs
            .into_iter()
            .filter(|cost| cost.quant.starts_with(USER_QUANT_PREFIX))
            .collect::<Vec<_>>();
        user_quant_costs.sort_by_key(|v| v.instantiations * v.cost);
        user_quant_costs.reverse();

        Ok(Profiler { message_interface, quantifier_stats: user_quant_costs })
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
