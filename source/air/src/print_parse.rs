use crate::ast::{
    BinaryOp, Command, CommandX, Commands, Const, Declaration, DeclarationX, Declarations, Expr,
    ExprX, Exprs, Ident, LogicalOp, Query, QueryX, Stmt, StmtX, Stmts, Typ, TypX, UnaryOp,
};
use sise::{Node, Writer};
use std::io::Write;
use std::rc::Rc;

pub(crate) fn str_to_node(s: &str) -> Node {
    Node::Atom(s.to_string())
}

pub(crate) fn typ_to_node(typ: &Typ) -> Node {
    match &**typ {
        TypX::Bool => str_to_node("Bool"),
        TypX::Int => str_to_node("Int"),
        TypX::Named(name) => str_to_node(&name.clone()),
    }
}

pub(crate) fn macro_push_node(nodes: &mut Vec<Node>, node: Node) {
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
  node!((atom1 {x} atom-3))
There's some limited support for atoms containing hyphens, at least for atoms inside a list.
*/
macro_rules! node {
    ( - ) => { Node::Atom("-".to_string()) };
    ( { $x:expr } ) => { $x };
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
macro_rules! nodes {
   ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           Node::List(v)
       }
   };
}

pub(crate) fn expr_to_node(expr: &Expr) -> Node {
    match &**expr {
        ExprX::Const(Const::Bool(b)) => Node::Atom(b.to_string()),
        ExprX::Const(Const::Nat(n)) => Node::Atom((**n).clone()),
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
            None => nodes!(assert {expr_to_node(expr)}),
            Some(s) => {
                let quoted = format!("\"{}\"", s.as_string);
                nodes!(location {Node::Atom(quoted)} {expr_to_node(expr)})
            }
        },
    }
}

pub fn sort_decl_to_node(x: &Ident) -> Node {
    node!((declare-sort {str_to_node(x)}))
}

pub fn const_decl_to_node(x: &Ident, typ: &Typ) -> Node {
    nodes!(const {str_to_node(x)} {typ_to_node(typ)})
}

pub fn function_decl_to_node(x: &Ident, typs: &[Typ], typ: &Typ) -> Node {
    let typs_nodes: Vec<Node> = typs.iter().map(typ_to_node).collect();
    let typs_node = Node::List(typs_nodes);
    nodes!(declare-fun {str_to_node(x)} {typs_node} {typ_to_node(typ)})
}

pub fn decl_to_node(decl: &Declaration) -> Node {
    match &**decl {
        DeclarationX::Sort(x) => sort_decl_to_node(x),
        DeclarationX::Const(x, typ) => const_decl_to_node(x, typ),
        DeclarationX::Axiom(expr) => nodes!(axiom {expr_to_node(expr)}),
    }
}

pub fn stmt_to_node(stmt: &Stmt) -> Node {
    match &**stmt {
        StmtX::Assume(expr) => nodes!(assume {expr_to_node(expr)}),
        StmtX::Assert(span, expr) => match &**span {
            None => nodes!(assert {expr_to_node(expr)}),
            Some(s) => {
                let quoted = format!("\"{}\"", s.as_string);
                nodes!(assert {Node::Atom(quoted)} {expr_to_node(expr)})
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

pub(crate) fn node_to_string_indent(indent: &String, node: &Node) -> String {
    let style = sise::SpacedStringWriterStyle {
        line_break: &("\n".to_string() + &indent),
        indentation: " ",
    };
    let mut result = String::new();
    let mut string_writer = sise::SpacedStringWriter::new(style, &mut result);
    write_node(&mut string_writer, &node, 80, false);
    string_writer.finish(()).unwrap();
    result
}

pub(crate) fn node_to_string(node: &Node) -> String {
    node_to_string_indent(&"".to_string(), node)
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
            writeln!(
                w,
                "{}{}",
                self.current_indent,
                node_to_string_indent(&self.current_indent, &node)
            )
            .unwrap();
            w.flush().unwrap();
        }
    }

    pub fn log_set_option(&mut self, option: &str, value: &str) {
        if let Some(_) = self.writer {
            self.log_node(&node!(
                (set-option {Node::Atom(":".to_owned() + option)} {Node::Atom(value.to_string())})
            ));
        }
    }

    pub fn log_push(&mut self) {
        if let Some(_) = self.writer {
            self.log_node(&nodes!(push));
            self.indent();
        }
    }

    pub fn log_pop(&mut self) {
        if let Some(_) = self.writer {
            self.unindent();
            self.log_node(&nodes!(pop));
        }
    }

    pub fn log_sort_decl(&mut self, x: &Ident) {
        if let Some(_) = self.writer {
            self.log_node(&sort_decl_to_node(x));
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
            self.log_node(&nodes!(assert {expr_to_node(expr)}));
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

// Following SMT-LIB syntax specification
fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c)
}

fn is_symbol(s: &String) -> bool {
    s.len() > 0 && s.chars().all(is_symbol_char)
}

fn nodes_to_box_slice<A, F: Fn(&Node) -> Result<A, String>>(
    nodes: &[Node],
    f: F,
) -> Result<Rc<Box<[A]>>, String> {
    let mut v: Vec<A> = Vec::new();
    for node in nodes.iter() {
        v.push(f(node)?);
    }
    Ok(Rc::new(v.into_boxed_slice()))
}

pub(crate) fn node_to_typ(node: &Node) -> Result<Typ, String> {
    match node {
        Node::Atom(s) if s.to_string() == "Bool" => Ok(Rc::new(TypX::Bool)),
        Node::Atom(s) if s.to_string() == "Int" => Ok(Rc::new(TypX::Int)),
        Node::Atom(s) if is_symbol(s) => Ok(Rc::new(TypX::Named(Rc::new(s.clone())))),
        _ => Err(format!("expected type, found: {}", node_to_string(node))),
    }
}

pub(crate) fn node_to_expr(node: &Node) -> Result<Expr, String> {
    match node {
        Node::Atom(s) if s.to_string() == "true" => Ok(Rc::new(ExprX::Const(Const::Bool(true)))),
        Node::Atom(s) if s.to_string() == "false" => Ok(Rc::new(ExprX::Const(Const::Bool(false)))),
        Node::Atom(s) if s.len() > 0 && s.chars().all(|c| c.is_ascii_digit()) => {
            Ok(Rc::new(ExprX::Const(Const::Nat(Rc::new(s.clone())))))
        }
        Node::Atom(s) if is_symbol(s) => Ok(Rc::new(ExprX::Var(Rc::new(s.clone())))),
        Node::List(nodes) if nodes.len() > 0 => {
            let args = nodes_to_exprs(&nodes[1..])?;
            let uop = match &nodes[0] {
                Node::Atom(s) if s.to_string() == "not" => Some(UnaryOp::Not),
                _ => None,
            };
            let bop = match &nodes[0] {
                Node::Atom(s) if s.to_string() == "=>" => Some(BinaryOp::Implies),
                Node::Atom(s) if s.to_string() == "=" => Some(BinaryOp::Eq),
                Node::Atom(s) if s.to_string() == "<=" => Some(BinaryOp::Le),
                Node::Atom(s) if s.to_string() == ">=" => Some(BinaryOp::Ge),
                Node::Atom(s) if s.to_string() == "<" => Some(BinaryOp::Lt),
                Node::Atom(s) if s.to_string() == ">" => Some(BinaryOp::Gt),
                Node::Atom(s) if s.to_string() == "+" => Some(BinaryOp::Add),
                Node::Atom(s) if s.to_string() == "-" => Some(BinaryOp::Sub),
                Node::Atom(s) if s.to_string() == "*" => Some(BinaryOp::Mul),
                Node::Atom(s) if s.to_string() == "div" => Some(BinaryOp::EuclideanDiv),
                Node::Atom(s) if s.to_string() == "mod" => Some(BinaryOp::EuclideanMod),
                _ => None,
            };
            let lop = match &nodes[0] {
                Node::Atom(s) if s.to_string() == "and" => Some(LogicalOp::And),
                Node::Atom(s) if s.to_string() == "or" => Some(LogicalOp::Or),
                _ => None,
            };
            match (args.len(), uop, bop, lop) {
                (1, Some(op), _, _) => Ok(Rc::new(ExprX::Unary(op, args[0].clone()))),
                (2, _, Some(op), _) => {
                    Ok(Rc::new(ExprX::Binary(op, args[0].clone(), args[1].clone())))
                }
                (_, _, _, Some(op)) => Ok(Rc::new(ExprX::Logical(op, args))),
                _ => Err(format!("expected expression, found: {}", node_to_string(node))),
            }
        }
        _ => Err(format!("expected expression, found: {}", node_to_string(node))),
    }
}

fn nodes_to_exprs(nodes: &[Node]) -> Result<Exprs, String> {
    nodes_to_box_slice(nodes, node_to_expr)
}

pub(crate) fn node_to_stmt(node: &Node) -> Result<Stmt, String> {
    match node {
        Node::List(nodes) => match &nodes[..] {
            [Node::Atom(s), e] if s.to_string() == "assume" => {
                let expr = node_to_expr(&e)?;
                Ok(Rc::new(StmtX::Assume(expr)))
            }
            [Node::Atom(s), e] if s.to_string() == "assert" => {
                let expr = node_to_expr(&e)?;
                Ok(Rc::new(StmtX::Assert(Rc::new(None), expr)))
            }
            _ => match &nodes[0] {
                Node::Atom(s) if s.to_string() == "block" => {
                    Ok(Rc::new(StmtX::Block(nodes_to_stmts(&nodes[1..])?)))
                }
                _ => Err(format!("expected statement, found: {}", node_to_string(node))),
            },
        },
        _ => Err(format!("expected statement, found: {}", node_to_string(node))),
    }
}

fn nodes_to_stmts(nodes: &[Node]) -> Result<Stmts, String> {
    nodes_to_box_slice(nodes, node_to_stmt)
}

fn node_to_decl(node: &Node) -> Result<Declaration, String> {
    match node {
        Node::List(nodes) => match &nodes[..] {
            [Node::Atom(s), Node::Atom(x)] if s.to_string() == "declare-sort" && is_symbol(x) => {
                Ok(Rc::new(DeclarationX::Sort(Rc::new(x.clone()))))
            }
            [Node::Atom(s), Node::Atom(x), t] if s.to_string() == "const" && is_symbol(x) => {
                let typ = node_to_typ(t)?;
                Ok(Rc::new(DeclarationX::Const(Rc::new(x.clone()), typ)))
            }
            [Node::Atom(s), e] if s.to_string() == "axiom" => {
                let expr = node_to_expr(e)?;
                Ok(Rc::new(DeclarationX::Axiom(expr)))
            }
            _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
        },
        _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
    }
}

fn nodes_to_decls(nodes: &[Node]) -> Result<Declarations, String> {
    nodes_to_box_slice(nodes, node_to_decl)
}

pub(crate) fn node_to_command(node: &Node) -> Result<Command, String> {
    match node {
        Node::List(nodes) if nodes.len() >= 1 => match &nodes[0] {
            Node::Atom(s) if s.to_string() == "push" && nodes.len() == 1 => {
                Ok(Rc::new(CommandX::Push))
            }
            Node::Atom(s) if s.to_string() == "pop" && nodes.len() == 1 => {
                Ok(Rc::new(CommandX::Pop))
            }
            Node::Atom(s) if s.to_string() == "check-valid" && nodes.len() >= 2 => {
                let assertion = node_to_stmt(&nodes[nodes.len() - 1])?;
                let local = nodes_to_decls(&nodes[1..nodes.len() - 1])?;
                let query = Rc::new(QueryX { local, assertion });
                Ok(Rc::new(CommandX::CheckValid(query)))
            }
            _ => {
                let decl = node_to_decl(&node)?;
                Ok(Rc::new(CommandX::Global(decl)))
            }
        },
        _ => Err(format!("expected command, found: {}", node_to_string(node))),
    }
}

pub(crate) fn nodes_to_commands(nodes: &[Node]) -> Result<Commands, String> {
    nodes_to_box_slice(nodes, node_to_command)
}
