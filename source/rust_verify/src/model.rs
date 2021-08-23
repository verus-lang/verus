use air::ast::Ident;
use air::ast::Span as ASpan;
use vir::def::SnapPos;
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
    pub fn new(vir_model: VModel<'a>, snap_map:&Vec<(ASpan, SnapPos)>, source_map: &SourceMap) -> Model<'a> {
        let mut line_map = HashMap::new();

        if snap_map.len() > 0 {
            let (air_span, snap_pos) = &snap_map[0];
            let span: &Span = (*air_span.raw_span)
                .downcast_ref::<Span>()
                .expect("internal error: failed to cast to Span");
            let (start, end) = source_map.is_valid_span(*span).expect("internal error: invalid Span");

            let mut min_snap:Ident = match snap_pos { 
                SnapPos::Start(span_id) => span_id.clone(),
                SnapPos::Full(span_id) => span_id.clone(),
                SnapPos::End(span_id) => span_id.clone(),
            };
            let mut min_line = start.line;
            let mut max_line = end.line;

            for (air_span, snap_pos) in snap_map {
                let span: &Span = (*air_span.raw_span)
                    .downcast_ref::<Span>()
                    .expect("internal error: failed to cast to Span");
                let (span_start, span_end) = source_map.is_valid_span(*span).expect("internal error: invalid Span");

                let (start, end, cur_snap) = match snap_pos {
                    SnapPos::Start(span_id) => (span_start.line, span_start.line + 1, span_id),
                    SnapPos::Full(span_id) => (span_start.line, span_end.line + 1, span_id),
                    SnapPos::End(span_id) => (span_end.line, span_end.line + 1, span_id),
                };

                println!("Apply {} to lines {}..{}", cur_snap, start, end);
                for line in start..end{
                    line_map.insert(line, cur_snap.clone());
                }
                
                if span_start.line < min_line {
                    min_line = span_start.line;
                    min_snap = cur_snap.clone();
                }
                max_line = std::cmp::max(max_line, span_end.line);

            }

            // Fill in any gaps
            let mut cur_snap = min_snap;
            for line in min_line..max_line {
                match line_map.get(&line) {
                    Some(snap) => cur_snap = snap.clone(),
                    None => {
                        let _ = line_map.insert(line, cur_snap.clone());
                        ()
                    }
                }

//                if line_map.contains_key(&line) {
//                    cur_snap = line_map.get(&line).unwrap(); // Checked for key in the line above
//                } else {
//                    line_map.insert(line, cur_snap.clone());
//                }
            }


/*
            let mut cur_line = start.line;
            let mut cur_snap = snap_id.clone();
            let mut end_line = end.line;

            for (air_span, snap_pos) in snap_map {
                let span: &Span = (*air_span.raw_span)
                    .downcast_ref::<Span>()
                    .expect("internal error: failed to cast to Span");
                let (start, _) = source_map.is_valid_span(*span).expect("internal error: invalid Span");
                println!("Apply {} to lines {}..{}", cur_snap, cur_line, start.line);
                for line in cur_line..start.line {
                    line_map.insert(line, cur_snap.clone());
                }
                cur_snap = snap_id.clone();
                cur_line = std::cmp::max(start.line, cur_line);
                end_line = std::cmp::max(end.line, end_line);
            }

            // Handle any trailing bits
            for line in cur_line..end_line {
                line_map.insert(line, cur_snap.clone());
            }
*/
        }

        for (air_span, snap_pos) in snap_map {
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
            println!("Span from {} to {} => {:?}", start.line, end.line, snap_pos);
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
