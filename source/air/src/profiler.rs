//! Analyzes prover performance of the SMT solver

use z3tracer::{Model, ModelConfig}; 

#[derive(Debug)]
/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    //log_path: String,
    model: Model,
}

impl Profiler {
    /// Instantiate a new (singleton) profiler
    pub fn new() -> Profiler {
        let path = "z3.log";
        let file = std::io::BufReader::new(std::fs::File::open(path).expect("Failed to open Z3 trace log"));
        let mut model_config = ModelConfig::default();
        model_config.parser_config.skip_z3_version_check = true;
//        model_config.parser_config.ignore_invalid_lines = true;
        //let mut model = Model::default();
        let mut model = Model::new(model_config);
        //model.config = ModelConfig { parser_config = ParserConfig { skip_z3_version_check = true, model.config.parser_config
        //model.config.parser_config.skip_z3_version_check = true;
        let _ = model.process(Some(path.to_string()), file).expect("Error processing Z3 trace");
        Profiler {
            model,
        }
    }
//    pub fn translate_variable(&self, sid: &Ident, name: &Ident) -> Option<String> {
//
//    }
}
