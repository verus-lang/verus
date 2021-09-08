use crate::ast::{
    BinaryOp, BindX, Binder, Binders, Constant, Datatypes, Decl, DeclX, Expr, ExprX, Exprs, Ident,
    MultiOp, Quant, Query, QueryX, Stmt, StmtX, Typ, TypX, Typs, UnaryOp,
};
use crate::util::vec_map;
use sise::{Node, Writer};
use std::sync::Arc;

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
            match op {
                MultiOp::Distinct if exprs.len() == 0 => {
                    // Z3 doesn't like the expression "(distinct)"
                    return Node::Atom("true".to_string());
                }
                _ => {}
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
    binder: &Binder<Arc<Vec<A>>>,
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
    binders: &Binders<Arc<Vec<A>>>,
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
