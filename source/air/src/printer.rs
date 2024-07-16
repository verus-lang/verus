use crate::ast::{
    Axiom, BinaryOp, BindX, Binder, Binders, Constant, Datatypes, Decl, DeclX, Expr, ExprX, Exprs,
    Ident, MultiOp, Qid, Quant, Query, QueryX, Stmt, StmtX, Triggers, Typ, TypX, Typs, UnaryOp,
};
use crate::context::SmtSolver;
use crate::def::mk_skolem_id;
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

pub struct Printer {
    message_interface: Arc<dyn crate::messages::MessageInterface>,
    // print as SMT, not as AIR
    print_as_smt: bool,
    solver: SmtSolver,
}

impl Printer {
    pub fn new(
        message_interface: Arc<dyn crate::messages::MessageInterface>,
        print_as_smt: bool,
        solver: SmtSolver,
    ) -> Self {
        Printer { message_interface, print_as_smt, solver }
    }

    pub(crate) fn typ_to_node(&self, typ: &Typ) -> Node {
        match &**typ {
            TypX::Bool => str_to_node("Bool"),
            TypX::Int => str_to_node("Int"),
            TypX::Fun if self.print_as_smt => str_to_node(crate::def::FUNCTION),
            TypX::Fun => str_to_node("Fun"),
            TypX::Named(name) => str_to_node(&name.clone()),
            TypX::BitVec(size) => Node::List(vec![
                str_to_node("_"),
                str_to_node("BitVec"),
                str_to_node(&size.to_string()),
            ]),
        }
    }

    pub(crate) fn typs_to_node(&self, typs: &Typs) -> Node {
        Node::List(vec_map(typs, |t| self.typ_to_node(t)))
    }

    pub(crate) fn bv_const_expr_to_node(&self, n: &Arc<String>, width: u32) -> Node {
        let bv_node = str_to_node(&format!("bv{}", n));
        let width_node = str_to_node(&width.to_string());
        node!((_ {bv_node} {width_node}))
    }

    pub(crate) fn filter_to_node(&self, filter: &Option<Ident>) -> Node {
        if let Some(filter) = filter { nodes!({ str_to_node(filter) }) } else { Node::List(vec![]) }
    }

    pub fn expr_to_node(&self, expr: &Expr) -> Node {
        match &**expr {
            ExprX::Const(Constant::Bool(b)) => Node::Atom(b.to_string()),
            ExprX::Const(Constant::Nat(n)) => Node::Atom((**n).clone()),
            ExprX::Const(Constant::BitVec(n, width)) => self.bv_const_expr_to_node(n, *width),
            ExprX::Var(x) => Node::Atom(x.to_string()),
            ExprX::Old(snap, x) => {
                nodes!(old {str_to_node(&snap.to_string())} {str_to_node(&x.to_string())})
            }
            ExprX::Apply(x, exprs) => {
                let mut nodes: Vec<Node> = Vec::new();
                nodes.push(str_to_node(x));
                for expr in exprs.iter() {
                    nodes.push(self.expr_to_node(expr));
                }
                Node::List(nodes)
            }
            ExprX::ApplyFun(typ, expr0, exprs) => {
                let mut nodes: Vec<Node> = Vec::new();
                nodes.push(str_to_node("apply"));
                nodes.push(self.typ_to_node(typ));
                nodes.push(self.expr_to_node(expr0));
                for expr in exprs.iter() {
                    nodes.push(self.expr_to_node(expr));
                }
                Node::List(nodes)
            }
            ExprX::Unary(op, expr) => {
                let sop = match op {
                    UnaryOp::Not => "not",
                    UnaryOp::BitNot => "bvnot",
                    UnaryOp::BitExtract(_, _) => "extract",
                    UnaryOp::BitZeroExtend(_) => "zero_extend",
                    UnaryOp::BitSignExtend(_) => "sign_extend",
                };
                // ( (_ extract numeral numeral) BitVec )
                match op {
                    UnaryOp::BitExtract(high, low) => {
                        let mut nodes: Vec<Node> = Vec::new();
                        let mut nodes_in: Vec<Node> = Vec::new();
                        nodes_in.push(str_to_node("_"));
                        nodes_in.push(str_to_node(sop));
                        nodes_in.push(str_to_node(&high.to_string()));
                        nodes_in.push(str_to_node(&low.to_string()));
                        nodes.push(Node::List(nodes_in));
                        nodes.push(self.expr_to_node(expr));
                        Node::List(nodes)
                    }
                    UnaryOp::BitZeroExtend(w) | UnaryOp::BitSignExtend(w) => {
                        let mut nodes: Vec<Node> = Vec::new();
                        let mut nodes_in: Vec<Node> = Vec::new();
                        nodes_in.push(str_to_node("_"));
                        nodes_in.push(str_to_node(sop));
                        nodes_in.push(str_to_node(&w.to_string()));
                        nodes.push(Node::List(nodes_in));
                        nodes.push(self.expr_to_node(expr));
                        Node::List(nodes)
                    }
                    _ => Node::List(vec![str_to_node(sop), self.expr_to_node(expr)]),
                }
            }
            ExprX::Binary(BinaryOp::Relation(relation, n), lhs, rhs) => {
                use crate::ast::Relation;
                let s = match relation {
                    Relation::PartialOrder => "partial-order",
                    Relation::LinearOrder => "linear-order",
                    Relation::TreeOrder => "tree-order",
                    Relation::PiecewiseLinearOrder => "piecewise-linear-order",
                };
                let op =
                    Node::List(vec![str_to_node("_"), str_to_node(s), Node::Atom(n.to_string())]);
                Node::List(vec![op, self.expr_to_node(lhs), self.expr_to_node(rhs)])
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
                    BinaryOp::Relation(..) => unreachable!(),
                    BinaryOp::BitXor => "bvxor",
                    BinaryOp::BitAnd => "bvand",
                    BinaryOp::BitOr => "bvor",
                    BinaryOp::BitAdd => "bvadd",
                    BinaryOp::BitSub => "bvsub",
                    BinaryOp::BitMul => "bvmul",
                    BinaryOp::BitUDiv => "bvudiv",
                    BinaryOp::BitUMod => "bvurem",
                    BinaryOp::BitULt => "bvult",
                    BinaryOp::BitUGt => "bvugt",
                    BinaryOp::BitULe => "bvule",
                    BinaryOp::BitUGe => "bvuge",
                    BinaryOp::BitSLt => "bvslt",
                    BinaryOp::BitSGt => "bvsgt",
                    BinaryOp::BitSLe => "bvsle",
                    BinaryOp::BitSGe => "bvsge",
                    BinaryOp::LShr => "bvlshr",
                    BinaryOp::AShr => "bvashr",
                    BinaryOp::Shl => "bvshl",
                    BinaryOp::BitConcat => "concat",
                };
                Node::List(vec![str_to_node(sop), self.expr_to_node(lhs), self.expr_to_node(rhs)])
            }
            ExprX::Multi(op, exprs) => {
                let sop = match op {
                    MultiOp::And => "and",
                    MultiOp::Or => "or",
                    MultiOp::Xor => "xor",
                    MultiOp::Add => "+",
                    MultiOp::Sub => "-",
                    MultiOp::Mul => "*",
                    MultiOp::Distinct => "distinct",
                };
                let mut nodes: Vec<Node> = Vec::new();
                nodes.push(str_to_node(sop));
                for expr in exprs.iter() {
                    nodes.push(self.expr_to_node(expr));
                }
                match op {
                    MultiOp::Distinct if exprs.len() <= 1 => {
                        // Z3 doesn't like the expression "(distinct)"
                        // cvc5 doesn't like the singleton expression "(distinct expr)"
                        return Node::Atom("true".to_string());
                    }
                    _ => {}
                }
                Node::List(nodes)
            }
            ExprX::IfElse(expr1, expr2, expr3) => {
                nodes!(ite {self.expr_to_node(expr1)} {self.expr_to_node(expr2)} {self.expr_to_node(expr3)})
            }
            ExprX::Array(exprs) => {
                let mut nodes: Vec<Node> = Vec::new();
                nodes.push(str_to_node("array"));
                for expr in exprs.iter() {
                    nodes.push(self.expr_to_node(expr));
                }
                Node::List(nodes)
            }
            ExprX::Bind(bind, expr) => {
                let with_triggers = |expr: &Expr, triggers: &Triggers, qid: &Qid| {
                    if triggers.len() == 0 && qid.is_none() {
                        self.expr_to_node(expr)
                    } else {
                        let mut nodes: Vec<Node> = Vec::new();
                        nodes.push(str_to_node("!"));
                        nodes.push(self.expr_to_node(expr));
                        for trigger in triggers.iter() {
                            nodes.push(str_to_node(":pattern"));
                            nodes.push(self.exprs_to_node(trigger));
                        }
                        if let Some(s) = qid {
                            nodes.push(str_to_node(":qid"));
                            nodes.push(str_to_node(s));
                            if matches!(self.solver, SmtSolver::Z3) {
                                nodes.push(str_to_node(":skolemid"));
                                nodes.push(str_to_node(&mk_skolem_id(s)));
                            }
                        }
                        Node::List(nodes)
                    }
                };
                match &**bind {
                    BindX::Let(binders) => {
                        let s_binders = self.binders_to_node(binders, &|e| self.expr_to_node(e));
                        nodes!(let {s_binders} {self.expr_to_node(expr)})
                    }
                    BindX::Quant(quant, binders, triggers, qid) => {
                        let s_quant = match quant {
                            Quant::Forall => "forall",
                            Quant::Exists => "exists",
                        };
                        let s_binders = self.binders_to_node(binders, &|t| self.typ_to_node(t));
                        let body = with_triggers(expr, triggers, qid);
                        nodes!({str_to_node(s_quant)} {s_binders} {body})
                    }
                    BindX::Lambda(binders, triggers, qid) => {
                        let body = with_triggers(expr, triggers, qid);
                        nodes!(lambda {self.binders_to_node(binders, &|t| self.typ_to_node(t))} {body})
                    }
                    BindX::Choose(binders, triggers, qid, expr_cond) => {
                        let s_binders = self.binders_to_node(binders, &|t| self.typ_to_node(t));
                        let cond = with_triggers(expr_cond, triggers, qid);
                        let body = self.expr_to_node(expr);
                        nodes!(choose {s_binders} {cond} {body})
                    }
                }
            }
            ExprX::LabeledAxiom(labels, filter, expr) => {
                let spans = vec_map(labels, |s| {
                    Node::Atom(format!("\"{}\"", self.message_interface.get_message_label_note(s)))
                });
                if spans.len() == 0 && filter.is_none() {
                    self.expr_to_node(expr)
                } else {
                    let filter_nodes = self.filter_to_node(filter);
                    nodes!(axiom_location {Node::List(spans)} {filter_nodes} {self.expr_to_node(expr)})
                }
            }
            ExprX::LabeledAssertion(_, error, filter, expr) => {
                let spans = vec_map(&self.message_interface.all_msgs(error), |s| {
                    Node::Atom(format!("\"{}\"", s))
                });
                if spans.len() == 0 && filter.is_none() {
                    self.expr_to_node(expr)
                } else {
                    let filter_nodes = self.filter_to_node(filter);
                    nodes!(location {Node::List(spans)} {filter_nodes} {self.expr_to_node(expr)})
                }
            }
        }
    }

    pub fn exprs_to_node(&self, exprs: &Exprs) -> Node {
        Node::List(vec_map(exprs, |e| self.expr_to_node(e)))
    }

    pub(crate) fn binder_to_node<A: Clone, F: Fn(&A) -> Node>(
        &self,
        binder: &Binder<A>,
        f: &F,
    ) -> Node {
        Node::List([str_to_node(&binder.name), f(&binder.a)].to_vec())
    }

    pub(crate) fn binders_to_node<A: Clone, F: Fn(&A) -> Node>(
        &self,
        binders: &Binders<A>,
        f: &F,
    ) -> Node {
        Node::List(vec_map(binders, |b| self.binder_to_node(b, f)))
    }

    pub(crate) fn multibinder_to_node<A: Clone, F: Fn(&A) -> Node>(
        &self,
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

    pub fn sort_decl_to_node(&self, x: &Ident) -> Node {
        node!((declare-sort {str_to_node(x)} 0))
    }

    pub fn datatypes_decl_to_node(&self, datatypes: &Datatypes) -> Node {
        let decls = Node::List(vec_map(datatypes, |d| nodes!({str_to_node(&d.name)} 0)));
        let defns = Node::List(vec_map(datatypes, |d| {
            Node::List(vec_map(&d.a, |variant| {
                self.multibinder_to_node(&variant, &|field| {
                    self.binder_to_node(&field, &|t| self.typ_to_node(t))
                })
            }))
        }));
        if self.print_as_smt && datatypes.len() == 0 {
            // cvc5 doesn't like empty declare-datatypes
            nodes!(assert true)
        } else {
            node!((declare-datatypes {decls} {defns}))
        }
    }

    pub fn const_decl_to_node(&self, x: &Ident, typ: &Typ) -> Node {
        nodes!(declare-const {str_to_node(x)} {self.typ_to_node(typ)})
    }

    pub fn fun_decl_to_node(&self, x: &Ident, typs: &Typs, typ: &Typ) -> Node {
        nodes!(declare-fun {str_to_node(x)} {self.typs_to_node(typs)} {self.typ_to_node(typ)})
    }

    pub fn var_decl_to_node(&self, x: &Ident, typ: &Typ) -> Node {
        nodes!(declare-var {str_to_node(x)} {self.typ_to_node(typ)})
    }

    pub fn axiom_to_node(&self, axiom: &Axiom) -> Node {
        let Axiom { named, expr } = axiom;
        if let Some(named) = named {
            nodes!(axiom ({str_to_node("!")} {self.expr_to_node(expr)} {str_to_node(":named")} {str_to_node(named)}))
        } else {
            nodes!(axiom {self.expr_to_node(expr)})
        }
    }

    pub fn decl_to_node(&self, decl: &Decl) -> Node {
        match &**decl {
            DeclX::Sort(x) => self.sort_decl_to_node(x),
            DeclX::Datatypes(datatypes) => self.datatypes_decl_to_node(datatypes),
            DeclX::Const(x, typ) => self.const_decl_to_node(x, typ),
            DeclX::Fun(x, typs, typ) => self.fun_decl_to_node(x, typs, typ),
            DeclX::Var(x, typ) => self.var_decl_to_node(x, typ),
            DeclX::Axiom(axiom) => self.axiom_to_node(axiom),
        }
    }

    pub fn stmt_to_node(&self, stmt: &Stmt) -> Node {
        match &**stmt {
            StmtX::Assume(expr) => nodes!(assume {self.expr_to_node(expr)}),
            StmtX::Assert(_, labels, filter, expr) => {
                let spans = vec_map(&self.message_interface.all_msgs(labels), |s| {
                    Node::Atom(format!("\"{}\"", s))
                });
                if spans.len() == 0 && filter.is_none() {
                    nodes!(assert {self.expr_to_node(expr)})
                } else {
                    let filter_nodes = self.filter_to_node(filter);
                    nodes!(assert {Node::List(spans)} {filter_nodes} {self.expr_to_node(expr)})
                }
            }
            StmtX::Havoc(x) => nodes!(havoc {str_to_node(x)}),
            StmtX::Assign(x, expr) => nodes!(assign {str_to_node(x)} {self.expr_to_node(expr)}),
            StmtX::Snapshot(snap) => nodes!(snapshot {str_to_node(snap)}),
            StmtX::DeadEnd(s) => nodes!(deadend {self.stmt_to_node(s)}),
            StmtX::Breakable(x, s) => nodes!(breakable {str_to_node(x)} {self.stmt_to_node(s)}),
            StmtX::Break(x) => nodes!(break { str_to_node(x) }),
            StmtX::Block(stmts) | StmtX::Switch(stmts) => {
                let mut nodes = Vec::new();
                let s = match &**stmt {
                    StmtX::Block(_) => "block",
                    _ => "switch",
                };
                nodes.push(str_to_node(s));
                for stmt in stmts.iter() {
                    nodes.push(self.stmt_to_node(stmt));
                }
                Node::List(nodes)
            }
        }
    }

    pub fn query_to_node(&self, query: &Query) -> Node {
        let QueryX { local, assertion } = &**query;
        let mut nodes = Vec::new();
        nodes.push(str_to_node("check-valid"));
        for decl in local.iter() {
            nodes.push(self.decl_to_node(decl));
        }
        nodes.push(self.stmt_to_node(assertion));
        Node::List(nodes)
    }
}

pub struct NodeWriter {}

impl NodeWriter {
    pub fn new() -> Self {
        NodeWriter {}
    }

    pub fn write_node(
        &mut self,
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
                    self.write_node(writer, n, break_len + 1, brk && !was_pattern);
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
                        Node::Atom(a) if a == ":pattern" || a == ":qid" || a == ":skolemid" => {
                            was_pattern = true;
                        }
                        _ => {}
                    }
                }
                writer.end_list(()).unwrap();
            }
        }
    }

    pub fn node_to_string_indent(&mut self, indent: &String, node: &Node) -> String {
        let indentation = " ";
        let style = sise::SpacedStringWriterStyle {
            line_break: &("\n".to_string() + &indent),
            indentation,
        };
        let mut result = String::new();
        let mut string_writer = sise::SpacedStringWriter::new(style, &mut result);
        self.write_node(&mut string_writer, &node, 80, false);
        string_writer.finish(()).unwrap();
        // Clean up result:
        clean_up_lines(result, indentation)
    }
}

pub(crate) fn node_to_string(node: &Node) -> String {
    NodeWriter::new().node_to_string_indent(&"".to_string(), node)
}

pub fn clean_up_lines(input: String, indentation: &str) -> String {
    let lines: Vec<&str> = input.lines().collect();
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
