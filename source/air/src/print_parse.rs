use crate::ast::{
    BinaryOp, Const, Declaration, DeclarationX, Expr, ExprX, Ident, LogicalOp, Query, QueryX, Stmt,
    StmtX, Typ, UnaryOp,
};
use sise::{Node, Writer};
use std::io::Write;

pub(crate) fn str_to_node(s: &str) -> Node {
    Node::Atom(s.to_string())
}

pub(crate) fn typ_to_node(typ: &Typ) -> Node {
    match *typ {
        Typ::Bool => str_to_node("Bool"),
        Typ::Int => str_to_node("Int"),
    }
}

fn macro_push_node(nodes: &mut Vec<Node>, node: Node) {
    // turn a - b into a-b
    let len = nodes.len();
    if len != 0 {
        if let Node::Atom(cur) = &node {
            if let Node::Atom(prev) = &nodes[len - 1] {
                if node == "-" || prev.ends_with("-") {
                    nodes[len - 1] = Node::Atom(prev.to_owned() + cur);
                    return;
                }
            }
        }
    }
    nodes.push(node);
}

/*
examples:
  node!(my_atom)
  node!((atom1 atom2 atom-3))
  node!((atom1 (10 20 30) atom-3))
  let x = node!((10 20 30));
  node!((atom1 [x] atom-3))
There's some limited support for atoms containing hyphens, at least for atoms inside a list.
*/
macro_rules! node {
  ( - ) => { Node::Atom("-".to_string()) };
  ( [ $x:expr ] ) => { $x };
  ( $x:literal ) => { Node::Atom($x.to_string()) };
  ( ( $( $x:tt )* ) ) => {
    {
      let mut v = Vec::new();
      $(macro_push_node(&mut v, node!($x));)*
      Node::List(v)
    }
  };
  ( $x:tt ) => { Node::Atom(stringify!($x).to_string()) };
}

pub(crate) fn expr_to_node(expr: &Expr) -> Node {
    match &**expr {
        ExprX::Const(Const::Bool(b)) => Node::Atom(b.to_string()),
        ExprX::Var(x) => Node::Atom(x.to_string()),
        ExprX::Unary(op, expr) => {
            let sop = match op {
                UnaryOp::Not => "not",
            };
            Node::List(vec![str_to_node(sop), expr_to_node(expr)])
        }
        ExprX::Binary(op, lhs, rhs) => {
            let sop = match op {
                BinaryOp::Implies => "=>",
                BinaryOp::Eq => "=",
                BinaryOp::Le => "<=",
                BinaryOp::Ge => ">=",
                BinaryOp::Lt => "<",
                BinaryOp::Gt => ">",
                BinaryOp::Add => "+",
                BinaryOp::Sub => "-",
                BinaryOp::Mul => "*",
                BinaryOp::EuclideanDiv => "div",
                BinaryOp::EuclideanMod => "mod",
            };
            Node::List(vec![str_to_node(sop), expr_to_node(lhs), expr_to_node(rhs)])
        }
        ExprX::Logical(op, exprs) => {
            let sop = match op {
                LogicalOp::And => "and",
                LogicalOp::Or => "or",
            };
            let mut nodes: Vec<Node> = Vec::new();
            nodes.push(str_to_node(sop));
            for expr in exprs.iter() {
                nodes.push(expr_to_node(expr));
            }
            Node::List(nodes)
        }
        ExprX::LabeledAssertion(span, expr) => match &**span {
            None => node!((assert[expr_to_node(expr)])),
            Some(s) => {
                let quoted = format!("\"{}\"", s.as_string);
                node!((location[Node::Atom(quoted)][expr_to_node(expr)]))
            }
        },
    }
}

pub fn const_decl_to_node(x: &Ident, typ: &Typ) -> Node {
    node!((const [str_to_node(x)] [typ_to_node(typ)]))
}

pub fn function_decl_to_node(x: &Ident, typs: &[Typ], typ: &Typ) -> Node {
    let typs_nodes: Vec<Node> = typs.iter().map(typ_to_node).collect();
    let typs_node = Node::List(typs_nodes);
    node!((declare - fun[str_to_node(x)][typs_node][typ_to_node(typ)]))
}

pub fn decl_to_node(decl: &Declaration) -> Node {
    match &**decl {
        DeclarationX::Const(x, typ) => const_decl_to_node(x, typ),
        DeclarationX::Axiom(expr) => node!((axiom[expr_to_node(expr)])),
    }
}

pub fn stmt_to_node(stmt: &Stmt) -> Node {
    match &**stmt {
        StmtX::Assume(expr) => node!((assume[expr_to_node(expr)])),
        StmtX::Assert(span, expr) => match &**span {
            None => node!((assert[expr_to_node(expr)])),
            Some(s) => {
                let quoted = format!("\"{}\"", s.as_string);
                node!((assert[Node::Atom(quoted)][expr_to_node(expr)]))
            }
        },
        StmtX::Block(stmts) => {
            let mut nodes = Vec::new();
            nodes.push(str_to_node("block"));
            for stmt in stmts.iter() {
                nodes.push(stmt_to_node(stmt));
            }
            Node::List(nodes)
        }
    }
}

pub fn query_to_node(query: &Query) -> Node {
    let QueryX { local, assertion } = &**query;
    let mut nodes = Vec::new();
    nodes.push(str_to_node("check-valid"));
    for decl in local.iter() {
        nodes.push(decl_to_node(decl));
    }
    nodes.push(stmt_to_node(assertion));
    Node::List(nodes)
}

pub(crate) fn write_node(
    writer: &mut sise::SpacedStringWriter,
    node: &Node,
    break_len: usize,
    brk: bool,
) {
    let opts =
        sise::SpacedStringWriterNodeOptions { break_line_len: if brk { 0 } else { break_len } };
    match node {
        Node::Atom(a) => {
            writer.write_atom(a, opts).unwrap();
        }
        Node::List(l) => {
            writer.begin_list(opts).unwrap();
            let mut brk = false;
            for n in l {
                write_node(writer, n, break_len + 1, brk);
                match n {
                    Node::Atom(a)
                        if a == "=>"
                            || a == "and"
                            || a == "assume"
                            || a == "assert"
                            || a == "location"
                            || a == "check-valid"
                            || a == "block" =>
                    {
                        brk = true;
                    }
                    _ => {}
                }
            }
            writer.end_list(()).unwrap();
        }
    }
}

pub(crate) struct Logger {
    writer: Option<Box<dyn std::io::Write>>,
    current_indent: String,
}

impl Logger {
    pub fn new(writer: Option<Box<dyn std::io::Write>>) -> Self {
        Logger { writer, current_indent: "".to_string() }
    }

    pub fn indent(&mut self) {
        if let Some(_) = self.writer {
            self.current_indent = self.current_indent.clone() + " ";
        }
    }

    pub fn unindent(&mut self) {
        if let Some(_) = self.writer {
            self.current_indent = self.current_indent[1..].to_string();
        }
    }

    pub fn blank_line(&mut self) {
        if let Some(w) = &mut self.writer {
            writeln!(w, "").unwrap();
            w.flush().unwrap();
        }
    }

    pub fn comment(&mut self, s: &str) {
        if let Some(w) = &mut self.writer {
            writeln!(w, "{};; {}", self.current_indent, s).unwrap();
            w.flush().unwrap();
        }
    }

    pub fn log_node(&mut self, node: &Node) {
        if let Some(w) = &mut self.writer {
            let style = sise::SpacedStringWriterStyle {
                line_break: &("\n".to_string() + &self.current_indent),
                indentation: " ",
            };
            let mut result = String::new();
            let mut string_writer = sise::SpacedStringWriter::new(style, &mut result);
            write_node(&mut string_writer, &node, 80, false);
            string_writer.finish(()).unwrap();
            writeln!(w, "{}{}", self.current_indent, result).unwrap();
            w.flush().unwrap();
        }
    }

    pub fn log_set_option(&mut self, option: &str, value: &str) {
        if let Some(_) = self.writer {
            self.log_node(&node!(
                (set - option[Node::Atom(":".to_owned() + option)][Node::Atom(value.to_string())])
            ));
        }
    }

    pub fn log_push(&mut self) {
        if let Some(_) = self.writer {
            self.log_node(&node!((push)));
            self.indent();
        }
    }

    pub fn log_pop(&mut self) {
        if let Some(_) = self.writer {
            self.unindent();
            self.log_node(&node!((pop)));
        }
    }

    pub fn log_function_decl(&mut self, x: &Ident, typs: &[Typ], typ: &Typ) {
        if let Some(_) = self.writer {
            self.log_node(&function_decl_to_node(x, typs, typ));
        }
    }

    pub fn log_decl(&mut self, decl: &Declaration) {
        if let Some(_) = self.writer {
            self.log_node(&decl_to_node(decl));
        }
    }

    pub fn log_assert(&mut self, expr: &Expr) {
        if let Some(_) = self.writer {
            self.log_node(&node!((assert[expr_to_node(expr)])));
        }
    }

    pub fn log_word(&mut self, s: &str) {
        if let Some(_) = self.writer {
            self.log_node(&Node::List(vec![Node::Atom(s.to_string())]));
        }
    }

    pub fn log_query(&mut self, query: &Query) {
        if let Some(_) = self.writer {
            self.log_node(&query_to_node(query));
        }
    }
}
