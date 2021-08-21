use air::ast::Ident;
use air::ast::Span as ASpan;
use vir::model::Model as VModel;
use std::collections::HashMap;
use std::fmt;
use rustc_span::Span;
use rustc_span::source_map::SourceMap;
//use itertools::Itertools;

#[derive(Debug)]
/// Rust-level model of a concrete counterexample
pub struct Model<'a> {
    /// Handle to the AIR-level model; only for internal use, e.g., for `eval`
    vir_model: VModel<'a>,
    /// Internal mapping from a line in the source file to a snapshot ID
    line_map: HashMap<usize, Ident>,
}


impl<'a> Model<'a> {
    pub fn new(vir_model: VModel<'a>, snap_map:&Vec<(ASpan, Ident)>, source_map: &SourceMap) -> Model<'a> {
        let mut line_map = HashMap::new();

        if snap_map.len() > 0 {
            let (air_span, snap_id) = &snap_map[0];
            let span: &Span = (*air_span.raw_span)
                .downcast_ref::<Span>()
                .expect("internal error: failed to cast to Span");
            let (start, end) = source_map.is_valid_span(*span).expect("internal error: invalid Span");
            let mut cur_line = start.line;
            let mut cur_snap = snap_id.clone();
            let mut end_line = end.line;

            for (air_span, snap_id) in snap_map {
                let span: &Span = (*air_span.raw_span)
                    .downcast_ref::<Span>()
                    .expect("internal error: failed to cast to Span");
                let (start, _) = source_map.is_valid_span(*span).expect("internal error: invalid Span");
                for line in cur_line..start.line {
                    line_map.insert(line, cur_snap.clone());
                }
                cur_snap = snap_id.clone();
                cur_line = start.line;
                end_line = end.line;
            }

            // Handle any trailing bits
            for line in cur_line..end_line {
                line_map.insert(line, cur_snap.clone());
            }
        }

        for (air_span, snap_id) in snap_map {
            let span: &Span = (*air_span.raw_span)
                .downcast_ref::<Span>()
                .expect("internal error: failed to cast to Span");
//        let filename: String = match source_map.span_to_filename(*span) {
//            FileName::Real(rfn) => rfn
//                .local_path()
//                .to_str()
//                .expect("internal error: path is not a valid string")
//                .to_string(),
//            _ => unsupported!("non real filenames in verifier errors", air_span),
//        };
            let (start, end) = source_map.is_valid_span(*span).expect("internal error: invalid Span");
    //            for i in start.line..start.end {
    //            }
                println!("Span from {} to {} => {}", start.line, end.line, snap_id);
        }
        Model { vir_model, line_map }
    }
}

impl<'a> fmt::Display for Model<'a> {
    /// Dump the contents of the Rust model for debugging purposes
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\nDisplaying model with {} lines\n", self.line_map.len())?;
        let mut lines:Vec<_> = self.line_map.iter().collect();
        lines.sort_by_key(|t| t.0);
        for (line, snap_id) in lines {
        //for (line, snap_id) in &self.line_map.iter().collect::<(&usize,&Ident)>().sort_by_key(|t| t.0) {
        //for line in &self.line_map.keys().sorted() {
        //for (line, snap_id) in &self.line_map {
            //write!(f, "Line {}: {}\n", line, self.line_map.get(line).unwrap())?;
            write!(f, "Line {}: {}\n", line, snap_id)?;
        }
        Ok(())
    }
}
