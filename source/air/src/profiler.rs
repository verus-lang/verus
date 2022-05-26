//! Analyzes prover performance of the SMT solver

use z3tracer::{Model, ModelConfig}; 
use z3tracer::syntax::Term;
//use std::collections::binary_heap::IntoIterSorted;
use std::io::BufRead;
//use crate::ast::Span;
//use std::collections::HashMap;

#[derive(Debug)]
/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    //log_path: String,
    quantifier_stats: Vec<(String, usize)>,
}

impl Profiler {
    /// Instantiate a new (singleton) profiler
    pub fn new() -> Profiler {
        let path = "z3.log";
//        println!("Going to sleep");
//        std::thread::sleep(std::time::Duration::from_secs(5));
        let file = std::io::BufReader::new(std::fs::File::open(path).expect("Failed to open Z3 trace log"));
        let line_count = file.lines().count();
        let file = std::io::BufReader::new(std::fs::File::open(path).expect("Failed to open Z3 trace log"));
        let mut model_config = ModelConfig::default();
        model_config.parser_config.skip_z3_version_check = true;
//        println!("Config: {:?}", model_config);
        model_config.parser_config.ignore_invalid_lines = true;
        //let mut model = Model::default();
        let mut model = Model::new(model_config);
        //model.config = ModelConfig { parser_config = ParserConfig { skip_z3_version_check = true, model.config.parser_config
        //model.config.parser_config.skip_z3_version_check = true;
        println!("Analyzing Z3 log...");
        let _ = model.process(Some(path.to_string()), file, line_count).expect("Error processing Z3 trace");
        println!("... analysis complete");
        let instantiated_term_counts = model.most_instantiated_terms();
        //println!("Found {} instantiated_term_counts", instantiated_term_counts.len());
//        let top = instantiated_term_counts.into_iter_sorted().take(20).collect::<Vec<_>>();  //IntoIterSorted::from(instantiated_term_counts.clone()).take(20).collect::<Vec<_>>();
//        println!("Top 20 instantiated_term_counts are: {:?}", top);

        // TODO: If we're not grabbing the top K, then we may not need into_iter_sorted
        let quantifiers_sorted = instantiated_term_counts.into_iter_sorted()
            .filter_map(|(count, ident)| {
                        let term = model.term(&ident).expect(format!("failed to find {:?} in the profiler's model", ident).as_str());
                        //println!("Examining {:?}", term); 
                        match term {
                            Term::Quant { name, .. } => 
                                if name.starts_with("crate__") {
                                    Some((name.clone(), count))
                                } else {
                                    None
                                },
                            _ => None,
                        }
                    })
            .collect::<Vec<_>>();

//            .filter(|(count, ident)| {
//                        println!("Examining {:?}", ident); 
//                        std::format!("{:?}", ident).starts_with("crate__")
//                    });
//match term { z3tracer::syntax::Term::Quant{_,_,_,_,_} => true, _ => false});
        //println!("Of those, {} were quantifiers", quantifiers_sorted.len());

//        // Find quantifier instantiations
//        for (count, term) in instantiated_term_counts.into_iter_sorted() {
//
//        }

        Profiler {
            quantifier_stats: quantifiers_sorted,
        }
    }

    pub fn quant_count(&self) -> usize {
        self.quantifier_stats.len()
    }
    
    pub fn total_instantiations(&self) -> usize {
        self.quantifier_stats.iter().fold(0, |acc, (_qid, count)| acc + count)
    }

    pub fn print_raw_stats(&self) {
        for (qid, count) in &self.quantifier_stats {
            println!("Instantiated {} {} times ({}% of the total)", qid, count, 100 * count / self.total_instantiations());
        }
    }

    pub fn iter(&self) -> impl Iterator<Item=&(String, usize)> + '_ {
        self.quantifier_stats.iter()
    }

//    pub fn print_stats(&self, qid_map: &HashMap<String, Span>) {
//        let total_instantiations = self.quantifier_stats.iter().fold(0, |acc, (_qid, count)| acc + count);
//        for (qid, count) in &self.quantifier_stats {
//            let qspan = qid_map.get(qid).expect(format!("Failed to find quantifier {}", qid).as_str());
//            println!("Instantiated {:?} {} times ({}% of the total)", qspan, count, 100 * count / total_instantiations);
//        }
//    }
}
