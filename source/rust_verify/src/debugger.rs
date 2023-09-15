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
use vir::def::{BOX_INT, POLY};
use vir::messages::Span as ASpan;

#[derive(Debug)]
/// Rust-level model of a concrete counterexample
pub struct Debugger {
    /// Handle to the AIR-level model; only for internal use, e.g., for `eval`
    air_model: AModel,
    /// Internal mapping from a end loc -> start lock -> a snapshot ID
    line_map: HashMap<SingleLineInfo, Ident>,
    // the current line number
    line: SingleLineInfo,
    var_map: HashMap<Ident, ASpan>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct SingleLineInfo {
    pub line: usize,
    pub start_col: usize,
    pub end_col: usize,
}

impl fmt::Display for SingleLineInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.line, self.start_col, self.end_col)
    }
}

fn lineinfo_to_slinfo(line: rustc_span::LineInfo) -> SingleLineInfo {
    SingleLineInfo { line: line.line_index, start_col: line.start_col.0, end_col: line.end_col.0 }
}

fn report_eval_result(
    local_name: String,
    result: String,
    span: &ASpan,
    in_snap: bool,
) -> vir::messages::MessageLabel {
    let prettyresult = match result.parse::<u128>() {
        Ok(val) => {
            format!("0x{:x}", val)
        }
        Err(_) => result,
    };
    if in_snap {
        let assign_str = format!("{} = {}", local_name, prettyresult);
        vir::messages::MessageLabel { span: span.clone(), note: assign_str }
    } else {
        let assign_str = format!("{} = {} in function paramter list", local_name, prettyresult);
        vir::messages::MessageLabel { span: span.clone(), note: assign_str }
    }
}

impl Debugger {
    pub fn new(
        air_model: AModel,
        _assign_map: &HashMap<*const ASpan, HashSet<Arc<String>>>,
        snap_map: &Vec<(ASpan, SnapPos)>,
        source_map: &SourceMap,
    ) -> Debugger {
        let mut line_map = HashMap::new();
        let mut var_map = HashMap::new();

        // let mut line_to_assigned = HashMap<usize, HashSet<Arc<String>>>::new();

        // for (air_span, vars) in assign_map {
        //     let span: &Span = &from_raw_span(&(*(*air_span)).raw_span);
        //     let (span_start, span_end) =
        //         source_map.is_valid_span(*span).expect("internal error: invalid Span");

        //     println!("{:?} {:?}", span_end.line, vars);
        // }

        if snap_map.len() > 0 {
            let (snap_span, snap_pos) = &snap_map[0];
            let mut min_snap: Ident = snap_pos.snapshot_id.clone();
            for (snap_span, snap_pos) in snap_map {
                let span: &Span = &from_raw_span(&snap_span.raw_span).expect("local span");
                let filelines =
                    source_map.span_to_lines(*span).expect("internal error: invalid Span");
                let mut lines: Vec<SingleLineInfo> = Vec::new();
                let cur_snap = snap_pos.snapshot_id.clone();
                match snap_pos.kind {
                    SpanKind::Start => {
                        let mut line = *filelines.lines.first().unwrap();
                        line.end_col = line.start_col;
                        lines.push(lineinfo_to_slinfo(line));
                    }
                    SpanKind::Full => {
                        for line in filelines.lines {
                            lines.push(lineinfo_to_slinfo(line));
                        }
                    }
                    SpanKind::End => {
                        let mut line = *filelines.lines.last().unwrap();
                        line.start_col = line.end_col;
                        lines.push(lineinfo_to_slinfo(line));
                    }
                };
                lines.sort();
                for line in lines {
                    if line_map.contains_key(&line) && *line_map.get(&line).unwrap() != cur_snap {
                        panic!(
                            "unexpectedly mapping the same line to a different snapshot: {:?} {:?} at line {:?}",
                            *(line_map.get(&line).unwrap()),
                            cur_snap,
                            line
                        );
                    }
                    for var in air_model.snapshot_names(&cur_snap) {
                        let uname = air_model.translate_variable(&cur_snap, &var).unwrap();
                        if var_map.contains_key(&uname) {
                            continue;
                        } else {
                            var_map.insert(Ident::new(uname), snap_span.clone());
                        }
                    }
                    line_map.insert(line, cur_snap.clone());
                }
            }
        }
        // Debugging sanity checks
        for (error_span, snap_pos) in snap_map {
            let span: &Span = &from_raw_span(&error_span.raw_span).expect("local span");
            let (start, end) =
                source_map.is_valid_span(*span).expect("internal error: invalid Span");
        }
        Debugger {
            air_model,
            line_map,
            line: SingleLineInfo { line: 0, start_col: 0, end_col: 0 },
            var_map,
        }
    }

    fn set_line(&mut self, line: SingleLineInfo) {
        if let None = self.line_map.get(&line) {
            panic!("invalid line number {:?}, no snapshot found", line);
        } else {
            self.line = line;
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

    fn eval_expr(&self, context: &mut air::context::Context, expr: &[u8]) -> String {
        let mut parser = sise::Parser::new(expr);
        let node = sise::read_into_tree(&mut parser).unwrap();
        let expr = self.rewrite_eval_expr(&node);
        let expr = expr.unwrap();
        let result: String = context.eval_expr(expr);
        return result;
    }

    pub fn eval_translated_var(
        &self,
        context: &mut air::context::Context,
        uname: &Ident,
        span: &ASpan,
        in_snap: bool,
    ) -> vir::messages::MessageLabel {
        let local_name: &str = vir::def::user_local_name(uname.as_str());
        let localvarid = vir::def::user_local_id(uname.as_str());
        let result = context.eval_expr(Node::Atom(uname.to_string()));
        report_eval_result(local_name.to_string(), result, span, in_snap)
    }

    pub fn eval_local_val(
        &self,
        context: &mut air::context::Context,
        in_snap: bool,
        aspan: &ASpan,
        uname: &Arc<String>,
    ) -> Option<vir::messages::MessageLabel> {
        let local_name: &str = vir::def::user_local_name(uname.as_str());
        let uname_no_alt = uname.replace("@", "");
        if let Some(snapshot_name) = self.translate_variable(&Arc::new(uname_no_alt.clone())) {
            let span = if self.var_map.contains_key(&snapshot_name) {
                self.var_map.get(&snapshot_name).unwrap()
            } else {
                aspan
            };
            let local_name: &str = vir::def::user_local_name(uname_no_alt.as_str());
            let mut result: String = self.eval_expr(context, &uname_no_alt.as_bytes());
            if result.starts_with(POLY) {
                let expr = format!("(%{} {})", BOX_INT, uname_no_alt);
                result = self.eval_expr(context, &expr.as_bytes());
            }
            Some(report_eval_result(local_name.to_string(), result, span, in_snap))
        } else {
            return None;
        }
    }

    fn find_snapshot_line(&self, maxline: usize, maxcol: usize) -> SingleLineInfo {
        let mut snapshot_line = SingleLineInfo { line: 0, start_col: 0, end_col: 0 };
        for line in self.line_map.keys() {
            if line.line < maxline || (line.line == maxline && line.end_col <= maxcol) {
                if line.line > snapshot_line.line
                    || (line.line == snapshot_line.line && line.end_col > snapshot_line.end_col)
                {
                    snapshot_line = *line;
                }
            }
        }
        snapshot_line
    }

    pub fn start_shell(
        &mut self,
        context: &mut air::context::Context,
        source_map: &SourceMap,
        tmp_var_map: &HashMap<Ident, ASpan>,
        top_span: &ASpan,
        error_span: &ASpan,
    ) -> Vec<vir::messages::MessageLabel> {
        println!("welcome to verus debugger shell");
        let mut ret = Vec::new();
        let span: &Span = &from_raw_span(&error_span.raw_span).expect("local span");
        let (_start, end) = source_map.is_valid_span(*span).expect("internal error: invalid Span");
        //let min_line = start.line;
        let maxline = end.line;
        let maxcol: usize = end.col.0;
        self.set_line(self.find_snapshot_line(maxline, maxcol));
        let sid = self.line_map.get(&self.line).unwrap();
        let snap_names: HashSet<Arc<String>> = self.air_model.snapshot_names(sid);
        let param_names = self.air_model.param_names();
        for uname in &snap_names {
            match self.eval_local_val(context, true, error_span, uname) {
                Some(res) => {
                    ret.push(res);
                }
                None => {}
            }
        }
        //println!("var_map = {:?}", self.var_map);
        for (uname, span) in &self.var_map {
            ret.push(self.eval_translated_var(context, uname, span, true));
        }
        for uname in &param_names {
            //println!("tmp_var_map = {:?}",tmp_var_map);
            //println!("uname = {}", uname);
            let uname_no_alt = uname.replace("@", "");
            let span = if tmp_var_map.contains_key(&uname_no_alt) {
                tmp_var_map.get(&uname_no_alt).unwrap()
            } else {
                top_span
            };
            match self.eval_local_val(context, false, span, uname) {
                Some(res) => {
                    ret.push(res);
                }
                None => {}
            }
        }
        context.flush_delayed_asserts();
        ret
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
