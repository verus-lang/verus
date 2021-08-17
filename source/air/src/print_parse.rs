use crate::ast::{
    BinaryOp, BindX, Binder, BinderX, Binders, Command, CommandX, Commands, Constant, Datatypes,
    Decl, DeclX, Decls, Expr, ExprX, Exprs, Ident, MultiOp, Quant, Query, QueryX, Span, Stmt,
    StmtX, Stmts, Trigger, Triggers, Typ, TypX, Typs, UnaryOp,
};
use crate::util::vec_map;
use sise::{Node, Writer};
use std::io::Write;
use std::rc::Rc;

pub fn str_to_node(s: &str) -> Node {
    Node::Atom(s.to_string())
}

pub fn macro_push_node(nodes: &mut Vec<Node>, node: Node) {
    // turn a - b into a-b
    let len = nodes.len();
    if len != 0 {
        if let Node::Atom(cur) = &node {
            if let Node::Atom(prev) = &nodes[len - 1] {
                if node == "-" || prev == ":" || (prev != "-" && prev.ends_with("-")) {
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
#[macro_export]
macro_rules! node {
    ( - ) => { Node::Atom("-".to_string()) };
    ( { $x:expr } ) => { $x };
    ( [ $x:expr ] ) => { $x.clone() };
    ( $x:literal ) => { Node::Atom($x.to_string()) };
    ( ( $( $x:tt )* ) ) => {
        {
            #[allow(unused_mut)]
            let mut v = Vec::new();
            $(macro_push_node(&mut v, node!($x));)*
            Node::List(v)
        }
    };
    ( $x:tt ) => { Node::Atom(stringify!($x).to_string()) };
}
#[macro_export]
macro_rules! nodes {
   ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           Node::List(v)
       }
   };
}
#[macro_export]
macro_rules! nodes_vec {
   ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           v
       }
   };
}

pub(crate) fn typ_to_node(typ: &Typ) -> Node {
    match &**typ {
        TypX::Bool => str_to_node("Bool"),
        TypX::Int => str_to_node("Int"),
        TypX::Named(name) => str_to_node(&name.clone()),
    }
}

pub(crate) fn typs_to_node(typs: &Typs) -> Node {
    Node::List(vec_map(typs, typ_to_node))
}

pub(crate) fn expr_to_node(expr: &Expr) -> Node {
    match &**expr {
        ExprX::Const(Constant::Bool(b)) => Node::Atom(b.to_string()),
        ExprX::Const(Constant::Nat(n)) => Node::Atom((**n).clone()),
        ExprX::Var(x) => Node::Atom(x.to_string()),
        ExprX::Old(snap, x) => {
            nodes!(old {str_to_node(&snap.to_string())} {str_to_node(&x.to_string())})
        }
        ExprX::Apply(x, exprs) => {
            let mut nodes: Vec<Node> = Vec::new();
            nodes.push(str_to_node(x));
            for expr in exprs.iter() {
                nodes.push(expr_to_node(expr));
            }
            Node::List(nodes)
        }
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
                BinaryOp::EuclideanDiv => "div",
                BinaryOp::EuclideanMod => "mod",
            };
            Node::List(vec![str_to_node(sop), expr_to_node(lhs), expr_to_node(rhs)])
        }
        ExprX::Multi(op, exprs) => {
            let sop = match op {
                MultiOp::And => "and",
                MultiOp::Or => "or",
                MultiOp::Add => "+",
                MultiOp::Sub => "-",
                MultiOp::Mul => "*",
                MultiOp::Distinct => "distinct",
            };
            let mut nodes: Vec<Node> = Vec::new();
            nodes.push(str_to_node(sop));
            for expr in exprs.iter() {
                nodes.push(expr_to_node(expr));
            }
            Node::List(nodes)
        }
        ExprX::IfElse(expr1, expr2, expr3) => {
            nodes!(ite {expr_to_node(expr1)} {expr_to_node(expr2)} {expr_to_node(expr3)})
        }
        ExprX::Bind(bind, expr) => match &**bind {
            BindX::Let(binders) => {
                nodes!(let {binders_to_node(binders, &expr_to_node)} {expr_to_node(expr)})
            }
            BindX::Quant(quant, binders, triggers) => {
                let s_quant = match quant {
                    Quant::Forall => "forall",
                    Quant::Exists => "exists",
                };
                let s_binders = binders_to_node(binders, &typ_to_node);
                let body = if triggers.len() == 0 {
                    expr_to_node(expr)
                } else {
                    let mut nodes: Vec<Node> = Vec::new();
                    nodes.push(str_to_node("!"));
                    nodes.push(expr_to_node(expr));
                    for trigger in triggers.iter() {
                        nodes.push(str_to_node(":pattern"));
                        nodes.push(exprs_to_node(trigger));
                    }
                    Node::List(nodes)
                };
                nodes!({str_to_node(s_quant)} {s_binders} {body})
            }
        },
        ExprX::LabeledAssertion(span, expr) => match &**span {
            None => expr_to_node(expr),
            Some(s) => {
                let quoted = format!("\"{}\"", s.as_string);
                nodes!(location {Node::Atom(quoted)} {expr_to_node(expr)})
            }
        },
    }
}

pub(crate) fn exprs_to_node(exprs: &Exprs) -> Node {
    Node::List(vec_map(exprs, expr_to_node))
}

pub(crate) fn binder_to_node<A: Clone, F: Fn(&A) -> Node>(binder: &Binder<A>, f: &F) -> Node {
    Node::List([str_to_node(&binder.name), f(&binder.a)].to_vec())
}

pub(crate) fn binders_to_node<A: Clone, F: Fn(&A) -> Node>(binders: &Binders<A>, f: &F) -> Node {
    Node::List(vec_map(binders, |b| binder_to_node(b, f)))
}

pub(crate) fn multibinder_to_node<A: Clone, F: Fn(&A) -> Node>(
    binder: &Binder<Rc<Vec<A>>>,
    f: &F,
) -> Node {
    let mut nodes: Vec<Node> = Vec::new();
    nodes.push(str_to_node(&binder.name));
    for a in binder.a.iter() {
        nodes.push(f(a));
    }
    Node::List(nodes)
}

pub(crate) fn multibinders_to_node<A: Clone, F: Fn(&A) -> Node>(
    binders: &Binders<Rc<Vec<A>>>,
    f: &F,
) -> Node {
    Node::List(vec_map(binders, |b| multibinder_to_node(b, f)))
}

pub fn sort_decl_to_node(x: &Ident) -> Node {
    node!((declare-sort {str_to_node(x)}))
}

pub fn datatypes_decl_to_node(datatypes: &Datatypes) -> Node {
    let ds = multibinders_to_node(&datatypes, &|variant| {
        multibinder_to_node(&variant, &|field| binder_to_node(&field, &typ_to_node))
    });
    node!((declare-datatypes () {ds}))
}

pub fn const_decl_to_node(x: &Ident, typ: &Typ) -> Node {
    nodes!(declare-const {str_to_node(x)} {typ_to_node(typ)})
}

pub fn fun_decl_to_node(x: &Ident, typs: &Typs, typ: &Typ) -> Node {
    nodes!(declare-fun {str_to_node(x)} {typs_to_node(typs)} {typ_to_node(typ)})
}

pub fn var_decl_to_node(x: &Ident, typ: &Typ) -> Node {
    nodes!(declare-var {str_to_node(x)} {typ_to_node(typ)})
}

pub fn decl_to_node(decl: &Decl) -> Node {
    match &**decl {
        DeclX::Sort(x) => sort_decl_to_node(x),
        DeclX::Datatypes(datatypes) => datatypes_decl_to_node(datatypes),
        DeclX::Const(x, typ) => const_decl_to_node(x, typ),
        DeclX::Fun(x, typs, typ) => fun_decl_to_node(x, typs, typ),
        DeclX::Var(x, typ) => var_decl_to_node(x, typ),
        DeclX::Axiom(expr) => nodes!(axiom {expr_to_node(expr)}),
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
        StmtX::Havoc(x) => nodes!(havoc {str_to_node(x)}),
        StmtX::Assign(x, expr) => nodes!(assign {str_to_node(x)} {expr_to_node(expr)}),
        StmtX::Snapshot(snap) => nodes!(snapshot {str_to_node(snap)}),
        StmtX::Block(stmts) | StmtX::Switch(stmts) => {
            let mut nodes = Vec::new();
            let s = match &**stmt {
                StmtX::Block(_) => "block",
                _ => "switch",
            };
            nodes.push(str_to_node(s));
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
            let mut was_pattern = false;
            for n in l {
                write_node(writer, n, break_len + 1, brk && !was_pattern);
                was_pattern = false;
                match n {
                    Node::Atom(a)
                        if a == "=>"
                            || a == "and"
                            || a == "or"
                            || a == "ite"
                            || a == "let"
                            || a == "assume"
                            || a == "assert"
                            || a == "location"
                            || a == "check-valid"
                            || a == "!"
                            || a == "switch"
                            || a == "block" =>
                    {
                        brk = true;
                    }
                    Node::Atom(a) if a == ":pattern" => {
                        was_pattern = true;
                    }
                    _ => {}
                }
            }
            writer.end_list(()).unwrap();
        }
    }
}

pub(crate) fn node_to_string_indent(indent: &String, node: &Node) -> String {
    let indentation = " ";
    let style =
        sise::SpacedStringWriterStyle { line_break: &("\n".to_string() + &indent), indentation };
    let mut result = String::new();
    let mut string_writer = sise::SpacedStringWriter::new(style, &mut result);
    write_node(&mut string_writer, &node, 80, false);
    string_writer.finish(()).unwrap();
    // Clean up result:
    let lines: Vec<&str> = result.lines().collect();
    let mut result: String = "".to_string();
    let mut i = 0;
    while i < lines.len() {
        let mut line = lines[i].to_owned();
        // Consolidate closing ) lines:
        if line.trim() == ")" {
            while i + 1 < lines.len() && lines[i + 1].trim() == ")" {
                line = lines[i + 1].to_string() + &indentation[1..] + line.trim();
                i += 1;
            }
        }
        result.push_str(&line);
        i += 1;
        if i < lines.len() {
            result.push_str("\n");
        }
    }
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

    /*
    pub fn log_function_decl(&mut self, x: &Ident, typs: &[Typ], typ: &Typ) {
        if let Some(_) = self.writer {
            self.log_node(&function_decl_to_node(x, typs, typ));
        }
    }
    */

    pub fn log_decl(&mut self, decl: &Decl) {
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

fn map_nodes_to_vec<A, F>(nodes: &[Node], f: F) -> Result<Rc<Vec<A>>, String>
where
    F: Fn(&Node) -> Result<A, String>,
{
    let mut v: Vec<A> = Vec::new();
    for node in nodes.iter() {
        v.push(f(node)?);
    }
    Ok(Rc::new(v))
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
        Node::Atom(s) if s.to_string() == "true" => Ok(Rc::new(ExprX::Const(Constant::Bool(true)))),
        Node::Atom(s) if s.to_string() == "false" => {
            Ok(Rc::new(ExprX::Const(Constant::Bool(false))))
        }
        Node::Atom(s) if s.len() > 0 && s.chars().all(|c| c.is_ascii_digit()) => {
            Ok(Rc::new(ExprX::Const(Constant::Nat(Rc::new(s.clone())))))
        }
        Node::Atom(s) if is_symbol(s) => Ok(Rc::new(ExprX::Var(Rc::new(s.clone())))),
        Node::List(nodes) if nodes.len() > 0 => {
            match &nodes[..] {
                [Node::Atom(s), Node::Atom(label), e]
                    if s.to_string() == "location"
                        && label.starts_with("\"")
                        && label.ends_with("\"") =>
                {
                    let raw_span = Rc::new(());
                    let as_string = label[1..label.len() - 1].to_string();
                    // TODO: Update AIR syntax to support file info
                    let span = Rc::new(Some(Span {
                        description: None,
                        raw_span,
                        as_string,
                        filename: "".to_string(),
                        start_row: 0,
                        start_col: 0,
                        end_row: 0,
                        end_col: 0,
                    }));
                    let expr = node_to_expr(e)?;
                    return Ok(Rc::new(ExprX::LabeledAssertion(span, expr)));
                }
                [Node::Atom(s), Node::Atom(snap), Node::Atom(x)]
                    if s.to_string() == "old" && is_symbol(snap) && is_symbol(x) =>
                {
                    return Ok(Rc::new(ExprX::Old(Rc::new(snap.clone()), Rc::new(x.clone()))));
                }
                [Node::Atom(s), Node::List(binders), e] if s.to_string() == "let" => {
                    return node_to_let_expr(binders, e);
                }
                [Node::Atom(s), Node::List(binders), e] if s.to_string() == "forall" => {
                    return node_to_quant_expr(Quant::Forall, binders, e);
                }
                [Node::Atom(s), Node::List(binders), e] if s.to_string() == "exists" => {
                    return node_to_quant_expr(Quant::Exists, binders, e);
                }
                _ => {}
            }
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
                Node::Atom(s) if s.to_string() == "div" => Some(BinaryOp::EuclideanDiv),
                Node::Atom(s) if s.to_string() == "mod" => Some(BinaryOp::EuclideanMod),
                _ => None,
            };
            let lop = match &nodes[0] {
                Node::Atom(s) if s.to_string() == "and" => Some(MultiOp::And),
                Node::Atom(s) if s.to_string() == "or" => Some(MultiOp::Or),
                Node::Atom(s) if s.to_string() == "+" => Some(MultiOp::Add),
                Node::Atom(s) if s.to_string() == "-" => Some(MultiOp::Sub),
                Node::Atom(s) if s.to_string() == "*" => Some(MultiOp::Mul),
                Node::Atom(s) if s.to_string() == "distinct" => Some(MultiOp::Distinct),
                _ => None,
            };
            let ite = match &nodes[0] {
                Node::Atom(s) if s.to_string() == "ite" => true,
                _ => false,
            };
            let fun = match &nodes[0] {
                Node::Atom(s) if is_symbol(s) => Some(s),
                _ => None,
            };
            match (args.len(), uop, bop, lop, ite, fun) {
                (1, Some(op), _, _, _, _) => Ok(Rc::new(ExprX::Unary(op, args[0].clone()))),
                (2, _, Some(op), _, _, _) => {
                    Ok(Rc::new(ExprX::Binary(op, args[0].clone(), args[1].clone())))
                }
                (_, _, _, Some(op), _, _) => Ok(Rc::new(ExprX::Multi(op, args))),
                (_, _, _, _, true, _) => {
                    Ok(Rc::new(ExprX::IfElse(args[0].clone(), args[1].clone(), args[2].clone())))
                }
                (_, _, _, _, _, Some(x)) => Ok(Rc::new(ExprX::Apply(Rc::new(x.clone()), args))),
                _ => Err(format!("expected expression, found: {}", node_to_string(node))),
            }
        }
        _ => Err(format!("expected expression, found: {}", node_to_string(node))),
    }
}

fn nodes_to_exprs(nodes: &[Node]) -> Result<Exprs, String> {
    map_nodes_to_vec(nodes, node_to_expr)
}

fn node_to_binder<A, F>(node: &Node, f: &F) -> Result<Binder<A>, String>
where
    A: Clone,
    F: Fn(&Node) -> Result<A, String>,
{
    match node {
        Node::List(nodes) => match &nodes[..] {
            [Node::Atom(name), node] if is_symbol(name) => {
                let a = f(node)?;
                return Ok(Rc::new(BinderX { name: Rc::new(name.clone()), a }));
            }
            _ => {}
        },
        _ => {}
    }
    Err(format!("expected binder (...), found: {}", node_to_string(node)))
}

fn node_to_multibinder<A, F>(node: &Node, f: &F) -> Result<Binder<Rc<Vec<A>>>, String>
where
    A: Clone,
    F: Fn(&Node) -> Result<A, String>,
{
    match node {
        Node::List(nodes) => match &nodes[0] {
            Node::Atom(name) if is_symbol(name) => {
                let mut tail: Vec<A> = Vec::new();
                for node in &nodes[1..] {
                    tail.push(f(node)?);
                }
                return Ok(Rc::new(BinderX { name: Rc::new(name.clone()), a: Rc::new(tail) }));
            }
            _ => {}
        },
        _ => {}
    }
    Err(format!("expected binder (...), found: {}", node_to_string(node)))
}

fn nodes_to_binders<A, F>(nodes: &[Node], f: &F) -> Result<Binders<A>, String>
where
    A: Clone,
    F: Fn(&Node) -> Result<A, String>,
{
    let mut binders: Vec<Binder<A>> = Vec::new();
    for node in nodes {
        binders.push(node_to_binder(node, f)?);
    }
    Ok(Rc::new(binders))
}

fn nodes_to_multibinders<A, F>(nodes: &[Node], f: &F) -> Result<Binders<Rc<Vec<A>>>, String>
where
    A: Clone,
    F: Fn(&Node) -> Result<A, String>,
{
    let mut binders: Vec<Binder<Rc<Vec<A>>>> = Vec::new();
    for node in nodes {
        binders.push(node_to_multibinder(node, f)?);
    }
    Ok(Rc::new(binders))
}

fn node_to_let_expr(binder_nodes: &[Node], expr: &Node) -> Result<Expr, String> {
    let binders = nodes_to_binders(binder_nodes, &node_to_expr)?;
    let bind = Rc::new(BindX::Let(binders));
    Ok(Rc::new(ExprX::Bind(bind, node_to_expr(expr)?)))
}

fn nodes_to_triggers(nodes: &[Node]) -> Result<Triggers, String> {
    let mut triggers: Vec<Trigger> = Vec::new();
    let mut expect_pattern = true;
    for node in nodes {
        match node {
            Node::Atom(s) if s.to_string() == ":pattern" && expect_pattern => {}
            Node::List(trigger_nodes) if !expect_pattern => {
                triggers.push(nodes_to_exprs(trigger_nodes)?);
            }
            _ => {
                return Err(format!("expected quantifier pattern, found {}", node_to_string(node)));
            }
        }
        expect_pattern = !expect_pattern;
    }
    Ok(Rc::new(triggers))
}

fn node_to_quant_expr(quant: Quant, binder_nodes: &[Node], expr: &Node) -> Result<Expr, String> {
    let binders = nodes_to_binders(binder_nodes, &node_to_typ)?;
    let (body, triggers) = match &expr {
        Node::List(nodes) if nodes.len() >= 2 => match &nodes[0] {
            Node::Atom(s) if s.to_string() == "!" => (&nodes[1], nodes_to_triggers(&nodes[2..])?),
            _ => (expr, Rc::new(vec![])),
        },
        _ => (expr, Rc::new(vec![])),
    };
    let bind = Rc::new(BindX::Quant(quant, binders, triggers));
    Ok(Rc::new(ExprX::Bind(bind, node_to_expr(body)?)))
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
            [Node::Atom(s), Node::Atom(x)] if s.to_string() == "havoc" && is_symbol(x) => {
                Ok(Rc::new(StmtX::Havoc(Rc::new(x.clone()))))
            }
            [Node::Atom(s), Node::Atom(x), e] if s.to_string() == "assign" && is_symbol(x) => {
                let expr = node_to_expr(&e)?;
                Ok(Rc::new(StmtX::Assign(Rc::new(x.clone()), expr)))
            }
            [Node::Atom(s), Node::Atom(snap)] if s.to_string() == "snapshot" && is_symbol(snap) => {
                Ok(Rc::new(StmtX::Snapshot(Rc::new(snap.clone()))))
            }
            [Node::Atom(s), Node::Atom(label), e]
                if s.to_string() == "assert"
                    && label.starts_with("\"")
                    && label.ends_with("\"") =>
            {
                let raw_span = Rc::new(());
                let as_string = label[1..label.len() - 1].to_string();
                // TODO: Update AIR syntax to support file info
                let span = Span {
                    description: None,
                    raw_span,
                    as_string,
                    filename: "".to_string(),
                    start_row: 0,
                    start_col: 0,
                    end_row: 0,
                    end_col: 0,
                };
                let expr = node_to_expr(&e)?;
                Ok(Rc::new(StmtX::Assert(Rc::new(Some(span)), expr)))
            }
            _ => match &nodes[0] {
                Node::Atom(s) if s.to_string() == "block" => {
                    Ok(Rc::new(StmtX::Block(nodes_to_stmts(&nodes[1..])?)))
                }
                Node::Atom(s) if s.to_string() == "switch" => {
                    Ok(Rc::new(StmtX::Switch(nodes_to_stmts(&nodes[1..])?)))
                }
                _ => Err(format!("expected statement, found: {}", node_to_string(node))),
            },
        },
        _ => Err(format!("expected statement, found: {}", node_to_string(node))),
    }
}

fn nodes_to_stmts(nodes: &[Node]) -> Result<Stmts, String> {
    map_nodes_to_vec(nodes, node_to_stmt)
}

fn node_to_decl(node: &Node) -> Result<Decl, String> {
    match node {
        Node::List(nodes) => match &nodes[..] {
            [Node::Atom(s), Node::Atom(x)] if s.to_string() == "declare-sort" && is_symbol(x) => {
                Ok(Rc::new(DeclX::Sort(Rc::new(x.clone()))))
            }
            [Node::Atom(s), Node::List(l), Node::List(datatypes)]
                if s.to_string() == "declare-datatypes" && l.len() == 0 =>
            {
                let ds = nodes_to_multibinders(datatypes, &|variant| {
                    node_to_multibinder(variant, &|field| node_to_binder(field, &node_to_typ))
                })?;
                Ok(Rc::new(DeclX::Datatypes(ds)))
            }
            [Node::Atom(s), Node::Atom(x), t]
                if s.to_string() == "declare-const" && is_symbol(x) =>
            {
                let typ = node_to_typ(t)?;
                Ok(Rc::new(DeclX::Const(Rc::new(x.clone()), typ)))
            }
            [Node::Atom(s), Node::Atom(x), Node::List(ts), t]
                if s.to_string() == "declare-fun" && is_symbol(x) =>
            {
                let mut typs: Vec<Typ> = Vec::new();
                for ta in ts {
                    typs.push(node_to_typ(ta)?);
                }
                let typ = node_to_typ(t)?;
                Ok(Rc::new(DeclX::Fun(Rc::new(x.clone()), Rc::new(typs), typ)))
            }
            [Node::Atom(s), Node::Atom(x), t] if s.to_string() == "declare-var" && is_symbol(x) => {
                let typ = node_to_typ(t)?;
                Ok(Rc::new(DeclX::Var(Rc::new(x.clone()), typ)))
            }
            [Node::Atom(s), e] if s.to_string() == "axiom" => {
                let expr = node_to_expr(e)?;
                Ok(Rc::new(DeclX::Axiom(expr)))
            }
            _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
        },
        _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
    }
}

fn nodes_to_decls(nodes: &[Node]) -> Result<Decls, String> {
    map_nodes_to_vec(nodes, node_to_decl)
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
            Node::Atom(s) if s.to_string() == "set-option" && nodes.len() == 3 => {
                match &nodes[..] {
                    [_, Node::Atom(option), Node::Atom(value)] if option.starts_with(":") => {
                        let opt = Rc::new(option[1..].to_string());
                        let val = Rc::new(value.clone());
                        Ok(Rc::new(CommandX::SetOption(opt, val)))
                    }
                    _ => Err(format!("expected command, found: {}", node_to_string(node))),
                }
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

pub fn nodes_to_commands(nodes: &[Node]) -> Result<Commands, String> {
    map_nodes_to_vec(nodes, node_to_command)
}
