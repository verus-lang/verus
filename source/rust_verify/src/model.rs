use crate::util::from_raw_span;
use air::ast::Ident;
use air::ast::Span as ASpan;
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use std::collections::HashMap;
use std::fmt;
use vir::def::SnapPos;
use vir::model::Model as VModel;

#[derive(Debug)]
/// Rust-level model of a concrete counterexample
pub struct Model {
    /// Handle to the AIR-level model; only for internal use, e.g., for `eval`
    vir_model: VModel,
    /// Internal mapping from a line in the source file to a snapshot ID
    line_map: HashMap<usize, Ident>,
}

impl Model {
    pub fn new(
        vir_model: VModel,
        snap_map: &Vec<(ASpan, SnapPos)>,
        source_map: &SourceMap,
    ) -> Model {
        let mut line_map = HashMap::new();

        if snap_map.len() > 0 {
            let (air_span, snap_pos) = &snap_map[0];
            let span: &Span = &from_raw_span(&air_span.raw_span);
            let (start, end) =
                source_map.is_valid_span(*span).expect("internal error: invalid Span");

            let mut min_snap: Ident = match snap_pos {
                SnapPos::Start(span_id) => span_id.clone(),
                SnapPos::Full(span_id) => span_id.clone(),
                SnapPos::End(span_id) => span_id.clone(),
            };
            let mut min_line = start.line;
            let mut max_line = end.line;

            for (air_span, snap_pos) in snap_map {
                let span: &Span = &from_raw_span(&air_span.raw_span);
                let (span_start, span_end) =
                    source_map.is_valid_span(*span).expect("internal error: invalid Span");

                let (start, end, cur_snap) = match snap_pos {
                    SnapPos::Start(span_id) => (span_start.line, span_start.line + 1, span_id),
                    SnapPos::Full(span_id) => (span_start.line, span_end.line + 1, span_id),
                    SnapPos::End(span_id) => (span_end.line, span_end.line + 1, span_id),
                };

                println!("Apply {} to lines {}..{}", cur_snap, start, end);
                for line in start..end {
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
            }
        }

        // Debugging sanity checks
        for (air_span, snap_pos) in snap_map {
            let span: &Span = &from_raw_span(&air_span.raw_span);
            let (start, end) =
                source_map.is_valid_span(*span).expect("internal error: invalid Span");
            println!("Span from {} to {} => {:?}", start.line, end.line, snap_pos);
        }
        Model { vir_model, line_map }
    }

    pub fn query_variable(&self, line: usize, name: Ident) -> Option<String> {
        Some(self.vir_model.query_variable(self.line_map.get(&line)?.clone(), name)?)
    }
}

impl fmt::Display for Model {
    /// Dump the contents of the Rust model for debugging purposes
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\nDisplaying model with {} lines\n", self.line_map.len())?;
        let mut lines: Vec<_> = self.line_map.iter().collect();
        lines.sort_by_key(|t| t.0);
        for (line, snap_id) in lines {
            write!(f, "Line {}: {}\n", line, snap_id)?;
        }
        Ok(())
    }
}
