use crate::ast::{Decl, Expr, Ident, Query};
use crate::context::SmtSolver;
use crate::printer::{NodeWriter, Printer, macro_push_node};
use crate::{node, nodes};
use std::io::Write;

pub(crate) struct Emitter {
    /// AIR/SMT -> Node printer
    printer: Printer,
    /// Node -> string writer
    node_writer: NodeWriter,
    /// buffer for data to be sent across pipe to Z3 process
    pipe_buffer: Option<Vec<u8>>,
    /// log file
    log: Option<Box<dyn std::io::Write>>,
    /// string of space characters representing current indentation level
    current_indent: String,
}

impl Emitter {
    pub fn new(
        message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
        use_pipe: bool,
        print_as_smt: bool,
        writer: Option<Box<dyn std::io::Write>>,
        solver: SmtSolver,
    ) -> Self {
        let pipe_buffer = if use_pipe { Some(Vec::new()) } else { None };
        Emitter {
            printer: Printer::new(message_interface, print_as_smt, solver),
            node_writer: NodeWriter::new(),
            pipe_buffer,
            log: writer,
            current_indent: "".to_string(),
        }
    }

    pub fn set_log(&mut self, writer: Option<Box<dyn std::io::Write>>) {
        self.log = writer;
    }

    fn is_none(&self) -> bool {
        self.pipe_buffer.is_none() && self.log.is_none()
    }

    /// Return all the data in pipe_buffer, and reset pipe_buffer to Some empty vector
    pub fn take_pipe_data(&mut self) -> Vec<u8> {
        let data = self.pipe_buffer.take().expect("use_pipe must be set to true to take pipe");
        self.pipe_buffer = Some(Vec::new());
        data
    }

    pub fn indent(&mut self) {
        if let Some(_) = self.log {
            self.current_indent = self.current_indent.clone() + " ";
        }
    }

    pub fn unindent(&mut self) {
        if let Some(_) = self.log {
            self.current_indent = self.current_indent[1..].to_string();
        }
    }

    pub fn blank_line(&mut self) {
        if let Some(w) = &mut self.log {
            writeln!(w, "").unwrap();
            w.flush().unwrap();
        }
    }

    pub fn comment(&mut self, s: &str) {
        if let Some(w) = &mut self.log {
            writeln!(w, "{};; {}", self.current_indent, s).unwrap();
            w.flush().unwrap();
        }
    }

    pub fn log_node(&mut self, node: &sise::TreeNode) {
        if let Some(w) = &mut self.pipe_buffer {
            writeln!(w, "{}", self.node_writer.node_to_string_indent(&self.current_indent, &node))
                .unwrap();
            w.flush().unwrap();
        }
        if let Some(w) = &mut self.log {
            writeln!(
                w,
                "{}{}",
                self.current_indent,
                self.node_writer.node_to_string_indent(&self.current_indent, &node)
            )
            .unwrap();
            w.flush().unwrap();
        }
    }

    pub fn log_set_option(&mut self, option: &str, value: &str) {
        if !self.is_none() {
            self.log_node(&node!(
                (set-option {sise::TreeNode::Atom(":".to_owned() + option)} {sise::TreeNode::Atom(value.to_string())})
            ));
        }
    }

    pub fn log_get_info(&mut self, param: &str) {
        if !self.is_none() {
            self.log_node(&node!(
                (get-info {sise::TreeNode::Atom(format!(":{}", param))})
            ));
        }
    }

    pub fn log_push(&mut self) {
        if !self.is_none() {
            self.log_node(&nodes!(push));
            self.indent();
        }
    }

    pub fn log_pop(&mut self) {
        if !self.is_none() {
            self.unindent();
            self.log_node(&nodes!(pop));
        }
    }

    /*
    pub fn log_function_decl(&mut self, x: &Ident, typs: &[Typ], typ: &Typ) {
        if let Some(_) = self.log {
            self.log_node(&function_decl_to_node(x, typs, typ));
        }
    }
    */

    pub fn log_decl(&mut self, decl: &Decl) {
        if !self.is_none() {
            self.log_node(&self.printer.decl_to_node(decl));
        }
    }

    pub fn log_assert(&mut self, named: &Option<Ident>, expr: &Expr) {
        if !self.is_none() {
            self.log_node(&
                if let Some(named) = named {
                    nodes!(assert ({sise::TreeNode::Atom("!".to_string())} {self.printer.expr_to_node(expr)} {sise::TreeNode::Atom(":named".to_string())} {sise::TreeNode::Atom((**named).clone())}))
                } else {
                    nodes!(assert {self.printer.expr_to_node(expr)})
                })
        }
    }

    pub fn log_word(&mut self, s: &str) {
        if !self.is_none() {
            self.log_node(&sise::TreeNode::List(vec![sise::TreeNode::Atom(s.to_string())]));
        }
    }

    pub fn log_query(&mut self, query: &Query) {
        if !self.is_none() {
            self.log_node(&self.printer.query_to_node(query));
        }
    }

    pub fn log_eval(&mut self, expr: sise::TreeNode) {
        if !self.is_none() {
            self.log_node(&nodes!(eval { expr }));
        }
    }
}
