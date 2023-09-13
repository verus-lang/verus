use crate::spans::from_raw_span;
use air::ast::Ident;
use air::model::Model as AModel;
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use sise::Node;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;
use vir::def::{suffix_local_stmt_id, SnapPos, SpanKind};
use vir::messages::Span as ASpan;

#[derive(Debug)]
/// Rust-level model of a concrete counterexample
pub struct Debugger {
    /// Handle to the AIR-level model; only for internal use, e.g., for `eval`
    air_model: AModel,
    /// Internal mapping from a line in the source file to a snapshot ID
    line_map: HashMap<usize, Ident>,
    // the current line number
    line: usize,
}

impl Debugger {
    pub fn new(
        air_model: AModel,
        _assign_map: &HashMap<*const ASpan, HashSet<Arc<String>>>,
        snap_map: &Vec<(ASpan, SnapPos)>,
        source_map: &SourceMap,
    ) -> Debugger {
        let mut line_map = HashMap::new();

        // let mut line_to_assigned = HashMap<usize, HashSet<Arc<String>>>::new();

        // for (air_span, vars) in assign_map {
        //     let span: &Span = &from_raw_span(&(*(*air_span)).raw_span);
        //     let (span_start, span_end) =
        //         source_map.is_valid_span(*span).expect("internal error: invalid Span");

        //     println!("{:?} {:?}", span_end.line, vars);
        // }

        if snap_map.len() > 0 {
            let (air_span, snap_pos) = &snap_map[0];
            let span: &Span = &from_raw_span(&air_span.raw_span).expect("local span");
            let (start, end) =
                source_map.is_valid_span(*span).expect("internal error: invalid Span");

            let mut min_snap: Ident = snap_pos.snapshot_id.clone();

            let mut min_line = start.line;
            let mut max_line = end.line;

            for (air_span, snap_pos) in snap_map {
                let span: &Span = &from_raw_span(&air_span.raw_span).expect("local span");
                let (span_start, span_end) =
                    source_map.is_valid_span(*span).expect("internal error: invalid Span");

                let cur_snap = snap_pos.snapshot_id.clone();
                let (start, end) = match snap_pos.kind {
                    SpanKind::Start => (span_start.line, span_start.line + 1),
                    SpanKind::Full => (span_start.line, span_end.line + 1),
                    SpanKind::End => (span_end.line, span_end.line + 1),
                };

                // println!("Apply {} to lines {}..{}", cur_snap, start, end);
                for line in start..end {
                    if line_map.contains_key(&line) && *(line_map.get(&line).unwrap()) != cur_snap {
                        println!("{:?} {:?}", *(line_map.get(&line).unwrap()), cur_snap);
                        panic!("unexpectedly mapping the same line to a different snapshot");
                    }
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
                    Some(snap) => {
                        println!("{} assigned to {:?}", line, snap);
                        cur_snap = snap.clone();
                    }
                    None => {
                        println!("{} (missing) assigned to {:?}", line, cur_snap);
                        let _ = line_map.insert(line, cur_snap.clone());
                    }
                }
            }
        }

        // Debugging sanity checks
        for (air_span, snap_pos) in snap_map {
            let span: &Span = &from_raw_span(&air_span.raw_span).expect("local span");
            let (start, end) =
                source_map.is_valid_span(*span).expect("internal error: invalid Span");
            println!("Span from {} to {} => {:?}", start.line, end.line, snap_pos);
        }
        Debugger { air_model, line_map, line: 0 }
    }

    fn set_line(&mut self, line: usize) {
        if let None = self.line_map.get(&line) {
            println!("invalid line number {}, no snapshot found", line);
        } else {
            self.line = line;
            println!("line number set to {}", line);
        }
    }

    fn translate_variable(&self, name: &Ident) -> Option<String> {
        let sid = self.line_map.get(&self.line)?;
        let name = suffix_local_stmt_id(&(Arc::new(name.to_string())));
        self.air_model.translate_variable(sid, &name)
    }

    fn rewrite_eval_expr(&self, expr: &sise::Node) -> Option<sise::Node> {
        match expr {
            Node::Atom(var) => {
                let name = self.translate_variable(&Arc::new(String::from(var)))?;
                Some(Node::Atom(name))
            }
            Node::List(app) => {
                if let Node::Atom(var) = &app[0] {
                    // TODO: should use suffix_global_id + path_to_air_ident?
                    let mut func_name = var.clone();
                    func_name.push('.');
                    func_name.push('?');
                    let mut items = vec![Node::Atom(func_name)];
                    for name in app.iter().skip(1) {
                        let name = self.rewrite_eval_expr(name)?;
                        items.push(name);
                    }
                    Some(Node::List(items))
                } else {
                    None
                }
            }
        }
    }

    fn eval_expr(&self, context: &mut air::context::Context, expr: &[u8]) {
        let mut parser = sise::Parser::new(expr);
        let node = sise::read_into_tree(&mut parser).unwrap();
        let expr = self.rewrite_eval_expr(&node).unwrap();
        let result = context.eval_expr(expr);
        println!("{}", result);
    }

    pub fn start_shell(&mut self, context: &mut air::context::Context) {
        println!("welcome to verus debugger shell");

        self.set_line(26);

        self.eval_expr(context, b"x");
        // self.eval_expr(context, b"y");
        self.eval_expr(context, b"(add_one x)");
        // self.eval_expr(context, b"(add_one (add_one x))");
    }
}

impl fmt::Display for Debugger {
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
