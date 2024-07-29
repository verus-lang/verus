use crate::ast::{
    Axiom, BinaryOp, BindX, Binder, BinderX, Binders, Command, CommandX, Commands, Constant, Decl,
    DeclX, Decls, Expr, ExprX, Exprs, Ident, MultiOp, Qid, Quant, QueryX, Relation, Stmt, StmtX,
    Stmts, Trigger, Triggers, Typ, TypX, UnaryOp,
};
use crate::def::mk_skolem_id;
use crate::messages::ArcDynMessageLabel;
use crate::model::{ModelDef, ModelDefX, ModelDefs};
use crate::printer::node_to_string;
use sise::Node;
use std::io::Write;
use std::sync::Arc;

// Following SMT-LIB syntax specification
fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c)
}

fn is_symbol(s: &String) -> bool {
    s.len() > 0 && s.chars().all(is_symbol_char)
}

fn is_bitvec(nodes: &Vec<Node>) -> Option<u32> {
    if nodes[0] == Node::Atom("_".to_string())
        && nodes[1] == Node::Atom("BitVec".to_string())
        && nodes.len() == 3
    {
        if let Node::Atom(s) = &nodes[2] {
            match s.parse::<u32>() {
                Ok(n) => return Some(n),
                Err(_) => return None,
            }
        }
    }
    None
}

fn underscore_atom_atom_expr(s1: &str, s2: &str) -> Option<Constant> {
    if s1.starts_with("bv") {
        let value = Arc::new(s1["bv".len()..].to_string());
        if let Ok(width) = s2.parse::<u32>() {
            return Some(Constant::BitVec(value, width));
        }
    }
    None
}

fn relation_binary_op(n1: &Node, n2: &Node) -> Option<BinaryOp> {
    match (n1, n2) {
        (Node::Atom(s1), Node::Atom(s2)) => {
            if let Ok(n) = s2.parse::<u64>() {
                match s1.as_str() {
                    "partial-order" => Some(BinaryOp::Relation(Relation::PartialOrder, n)),
                    "linear-order" => Some(BinaryOp::Relation(Relation::LinearOrder, n)),
                    "tree-order" => Some(BinaryOp::Relation(Relation::TreeOrder, n)),
                    "piecewise-linear-order" => {
                        Some(BinaryOp::Relation(Relation::PiecewiseLinearOrder, n))
                    }
                    _ => None,
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

fn map_nodes_to_vec<A, F>(nodes: &[Node], f: &F) -> Result<Arc<Vec<A>>, String>
where
    F: Fn(&Node) -> Result<A, String>,
{
    let mut v: Vec<A> = Vec::new();
    for node in nodes.iter() {
        v.push(f(node)?);
    }
    Ok(Arc::new(v))
}

fn map_nodes_to_vec_opt<A, F>(nodes: &[Node], f: &F) -> Result<Arc<Vec<A>>, String>
where
    F: Fn(&Node) -> Result<Option<A>, String>,
{
    let mut v: Vec<A> = Vec::new();
    for node in nodes.iter() {
        if let Some(a) = f(node)? {
            v.push(a);
        }
    }
    Ok(Arc::new(v))
}

enum QuantOrChooseOrLambda {
    Quant(Quant),
    Choose(Expr),
    Lambda,
}

pub struct Parser {
    message_interface: Arc<dyn crate::messages::MessageInterface>,
}

impl Parser {
    pub fn new(message_interface: Arc<dyn crate::messages::MessageInterface>) -> Self {
        Parser { message_interface }
    }

    pub(crate) fn node_to_typ(&self, node: &Node) -> Result<Typ, String> {
        match node {
            Node::Atom(s) if s.to_string() == "Bool" => Ok(Arc::new(TypX::Bool)),
            Node::Atom(s) if s.to_string() == "Int" => Ok(Arc::new(TypX::Int)),
            Node::Atom(s) if s.to_string() == "Fun" => Ok(Arc::new(TypX::Fun)),
            Node::Atom(s) if is_symbol(s) => Ok(Arc::new(TypX::Named(Arc::new(s.clone())))),
            Node::List(nodes) if is_bitvec(nodes).is_some() => {
                Ok(Arc::new(TypX::BitVec(is_bitvec(nodes).unwrap())))
            }
            _ => Err(format!("expected type, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_labels(&self, nodes: &Vec<Node>) -> Result<Vec<ArcDynMessageLabel>, String> {
        let mut labels: Vec<ArcDynMessageLabel> = Vec::new();
        for node in nodes {
            match node {
                Node::Atom(label) if label.starts_with("\"") && label.ends_with("\"") => {
                    let as_string = label[1..label.len() - 1].to_string();
                    let label =
                        self.message_interface.message_label_from_air_span(&as_string, &as_string);
                    labels.push(label);
                }
                _ => {
                    return Err(format!("expected quoted string, found: {}", node_to_string(node)));
                }
            }
        }
        Ok(labels)
    }

    fn nodes_to_filter(&self, nodes: &Vec<Node>) -> Result<Option<Ident>, String> {
        if nodes.len() == 0 {
            Ok(None)
        } else {
            assert!(nodes.len() == 1);
            match &nodes[0] {
                Node::Atom(s) if is_symbol(s) => Ok(Some(Arc::new(s.clone()))),
                _ => Err(format!("expected symbol, found: {}", node_to_string(&nodes[0]))),
            }
        }
    }

    pub(crate) fn node_to_expr(&self, node: &Node) -> Result<Expr, String> {
        match node {
            Node::Atom(s) if s.to_string() == "true" => {
                Ok(Arc::new(ExprX::Const(Constant::Bool(true))))
            }
            Node::Atom(s) if s.to_string() == "false" => {
                Ok(Arc::new(ExprX::Const(Constant::Bool(false))))
            }
            Node::Atom(s) if s.len() > 0 && s.chars().all(|c| c.is_ascii_digit()) => {
                Ok(Arc::new(ExprX::Const(Constant::Nat(Arc::new(s.clone())))))
            }
            Node::Atom(s) if is_symbol(s) => Ok(Arc::new(ExprX::Var(Arc::new(s.clone())))),
            Node::List(nodes) if nodes.len() > 0 => {
                match &nodes[..] {
                    [Node::Atom(s), Node::List(nodes), Node::List(filter), e]
                        if s.to_string() == "location" && filter.len() <= 1 =>
                    {
                        let error =
                            self.message_interface.from_labels(&self.nodes_to_labels(nodes)?);
                        let filter = self.nodes_to_filter(filter)?;
                        let expr = self.node_to_expr(e)?;
                        return Ok(Arc::new(ExprX::LabeledAssertion(None, error, filter, expr)));
                    }
                    [Node::Atom(s), Node::List(nodes), Node::List(filter), e]
                        if s.to_string() == "axiom_location" && filter.len() <= 1 =>
                    {
                        let labels = self.nodes_to_labels(nodes)?;
                        let filter = self.nodes_to_filter(filter)?;
                        let expr = self.node_to_expr(e)?;
                        return Ok(Arc::new(ExprX::LabeledAxiom(labels, filter, expr)));
                    }
                    [Node::Atom(s), Node::Atom(snap), Node::Atom(x)]
                        if s.to_string() == "old" && is_symbol(snap) && is_symbol(x) =>
                    {
                        return Ok(Arc::new(ExprX::Old(
                            Arc::new(snap.clone()),
                            Arc::new(x.clone()),
                        )));
                    }
                    [Node::Atom(s), Node::List(binders), e] if s.to_string() == "let" => {
                        return self.node_to_let_expr(binders, e);
                    }
                    [Node::Atom(s), Node::List(binders), e] if s.to_string() == "forall" => {
                        let quantchooselambda = QuantOrChooseOrLambda::Quant(Quant::Forall);
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e);
                    }
                    [Node::Atom(s), Node::List(binders), e] if s.to_string() == "exists" => {
                        let quantchooselambda = QuantOrChooseOrLambda::Quant(Quant::Exists);
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e);
                    }
                    [Node::Atom(s), Node::List(binders), e] if s.to_string() == "lambda" => {
                        let quantchooselambda = QuantOrChooseOrLambda::Lambda;
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e);
                    }
                    [Node::Atom(s), Node::List(binders), e1, e2] if s.to_string() == "choose" => {
                        let quantchooselambda =
                            QuantOrChooseOrLambda::Choose(self.node_to_expr(e2)?);
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e1);
                    }
                    [Node::Atom(s), Node::Atom(s1), Node::Atom(s2)]
                        if s.to_string() == "_" && underscore_atom_atom_expr(s1, s2).is_some() =>
                    {
                        return Ok(Arc::new(ExprX::Const(
                            underscore_atom_atom_expr(s1, s2).unwrap(),
                        )));
                    }
                    _ => {}
                }
                match &nodes[0] {
                    Node::Atom(s) if s.to_string() == "apply" && nodes.len() >= 3 => {
                        let typ = self.node_to_typ(&nodes[1])?;
                        let f = self.node_to_expr(&nodes[2])?;
                        let args = self.nodes_to_exprs(&nodes[3..])?;
                        return Ok(Arc::new(ExprX::ApplyFun(typ, f, args)));
                    }
                    Node::Atom(s) if s.to_string() == "array" && nodes.len() >= 1 => {
                        let args = self.nodes_to_exprs(&nodes[1..])?;
                        return Ok(Arc::new(ExprX::Array(args)));
                    }
                    _ => {}
                }
                let args = self.nodes_to_exprs(&nodes[1..])?;
                let uop = match &nodes[0] {
                    Node::Atom(s) if s.to_string() == "not" => Some(UnaryOp::Not),
                    Node::Atom(s) if s.to_string() == "bvnot" => Some(UnaryOp::BitNot),
                    Node::List(nodes)
                        if nodes.len() == 4
                            && nodes[0] == Node::Atom("_".to_string())
                            && nodes[1] == Node::Atom("extract".to_string()) =>
                    {
                        match (&nodes[2], &nodes[3]) {
                            (Node::Atom(s2), Node::Atom(s3)) => {
                                match (s2.parse::<u32>(), s3.parse::<u32>()) {
                                    (Ok(hi), Ok(lo)) => Some(UnaryOp::BitExtract(hi, lo)),
                                    _ => None,
                                }
                            }
                            _ => None,
                        }
                    }
                    Node::List(nodes)
                        if nodes.len() == 3
                            && nodes[0] == Node::Atom("_".to_string())
                            && (nodes[1] == Node::Atom("zero_extend".to_string())
                                || nodes[1] == Node::Atom("sign_extend".to_string())) =>
                    {
                        match &nodes[2] {
                            Node::Atom(s2) => match s2.parse::<u32>() {
                                Ok(n) => {
                                    if nodes[1] == Node::Atom("zero_extend".to_string()) {
                                        Some(UnaryOp::BitZeroExtend(n))
                                    } else {
                                        Some(UnaryOp::BitSignExtend(n))
                                    }
                                }
                                _ => None,
                            },
                            _ => None,
                        }
                    }
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
                    Node::Atom(s) if s.to_string() == "bvxor" => Some(BinaryOp::BitXor),
                    Node::Atom(s) if s.to_string() == "bvand" => Some(BinaryOp::BitAnd),
                    Node::Atom(s) if s.to_string() == "bvor" => Some(BinaryOp::BitOr),
                    Node::Atom(s) if s.to_string() == "bvadd" => Some(BinaryOp::BitAdd),
                    Node::Atom(s) if s.to_string() == "bvsub" => Some(BinaryOp::BitSub),
                    Node::Atom(s) if s.to_string() == "bvmul" => Some(BinaryOp::BitMul),
                    Node::Atom(s) if s.to_string() == "bvudiv" => Some(BinaryOp::BitUDiv),
                    Node::Atom(s) if s.to_string() == "bvurem" => Some(BinaryOp::BitUMod),
                    Node::Atom(s) if s.to_string() == "bvult" => Some(BinaryOp::BitULt),
                    Node::Atom(s) if s.to_string() == "bvugt" => Some(BinaryOp::BitUGt),
                    Node::Atom(s) if s.to_string() == "bvule" => Some(BinaryOp::BitULe),
                    Node::Atom(s) if s.to_string() == "bvuge" => Some(BinaryOp::BitUGe),
                    Node::Atom(s) if s.to_string() == "bvlshr" => Some(BinaryOp::LShr),
                    Node::Atom(s) if s.to_string() == "bvshl" => Some(BinaryOp::Shl),
                    Node::Atom(s) if s.to_string() == "concat" => Some(BinaryOp::BitConcat),
                    Node::List(nodes)
                        if nodes.len() == 3
                            && nodes[0] == Node::Atom("_".to_string())
                            && relation_binary_op(&nodes[1], &nodes[2]).is_some() =>
                    {
                        relation_binary_op(&nodes[1], &nodes[2])
                    }
                    _ => None,
                };
                let lop = match &nodes[0] {
                    Node::Atom(s) if s.to_string() == "and" => Some(MultiOp::And),
                    Node::Atom(s) if s.to_string() == "or" => Some(MultiOp::Or),
                    Node::Atom(s) if s.to_string() == "xor" => Some(MultiOp::Xor),
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
                    (1, Some(op), _, _, _, _) => Ok(Arc::new(ExprX::Unary(op, args[0].clone()))),
                    (2, _, Some(op), _, _, _) => {
                        Ok(Arc::new(ExprX::Binary(op, args[0].clone(), args[1].clone())))
                    }
                    (_, _, _, Some(op), _, _) => Ok(Arc::new(ExprX::Multi(op, args))),
                    (_, _, _, _, true, _) => Ok(Arc::new(ExprX::IfElse(
                        args[0].clone(),
                        args[1].clone(),
                        args[2].clone(),
                    ))),
                    (_, _, _, _, _, Some(x)) => {
                        Ok(Arc::new(ExprX::Apply(Arc::new(x.clone()), args)))
                    }
                    _ => Err(format!("expected expression, found: {}", node_to_string(node))),
                }
            }
            _ => Err(format!("expected expression, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_exprs(&self, nodes: &[Node]) -> Result<Exprs, String> {
        map_nodes_to_vec(nodes, &|n| self.node_to_expr(n))
    }

    fn node_to_binder<A, F>(&self, node: &Node, f: &F) -> Result<Binder<A>, String>
    where
        A: Clone,
        F: Fn(&Node) -> Result<A, String>,
    {
        match node {
            Node::List(nodes) => match &nodes[..] {
                [Node::Atom(name), node] if is_symbol(name) => {
                    let a = f(node)?;
                    return Ok(Arc::new(BinderX { name: Arc::new(name.clone()), a }));
                }
                _ => {}
            },
            _ => {}
        }
        Err(format!("expected binder (...), found: {}", node_to_string(node)))
    }

    fn node_to_multibinder<A, F>(&self, node: &Node, f: &F) -> Result<Binder<Arc<Vec<A>>>, String>
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
                    return Ok(Arc::new(BinderX {
                        name: Arc::new(name.clone()),
                        a: Arc::new(tail),
                    }));
                }
                _ => {}
            },
            _ => {}
        }
        Err(format!("expected binder (...), found: {}", node_to_string(node)))
    }

    fn nodes_to_binders<A, F>(&self, nodes: &[Node], f: &F) -> Result<Binders<A>, String>
    where
        A: Clone,
        F: Fn(&Node) -> Result<A, String>,
    {
        let mut binders: Vec<Binder<A>> = Vec::new();
        for node in nodes {
            binders.push(self.node_to_binder(node, f)?);
        }
        Ok(Arc::new(binders))
    }

    fn node_to_let_expr(&self, binder_nodes: &[Node], expr: &Node) -> Result<Expr, String> {
        let binders = self.nodes_to_binders(binder_nodes, &|n| self.node_to_expr(n))?;
        Ok(crate::ast_util::mk_let(&binders, &self.node_to_expr(expr)?))
    }

    fn nodes_to_triggers_and_qid(&self, nodes: &[Node]) -> Result<(Triggers, Qid), String> {
        let mut triggers: Vec<Trigger> = Vec::new();
        let mut qid = None;
        // We don't currently use the parsed skolemid, since we emit skolemid = qid,
        // but we still need to account for it, since it will appear in SMTLIB we produce
        let mut skolemid = None;
        let mut consume_pattern = false;
        let mut consume_qid = false;
        let mut consume_skolemid = false;

        for node in nodes {
            match node {
                Node::Atom(s) if s.to_string() == ":pattern" => {
                    consume_pattern = true;
                }
                Node::Atom(s) if s.to_string() == ":qid" => {
                    consume_qid = true;
                }
                Node::Atom(s) if s.to_string() == ":skolemid" => {
                    consume_skolemid = true;
                }
                Node::Atom(s) if consume_qid && qid.is_none() => {
                    qid = Some(Arc::new(s.clone()));
                    consume_qid = false;
                }
                Node::Atom(s) if consume_skolemid && skolemid.is_none() => {
                    skolemid = Some(s.clone());
                    consume_skolemid = false;
                }
                Node::List(trigger_nodes) if consume_pattern => {
                    triggers.push(self.nodes_to_exprs(trigger_nodes)?);
                    consume_pattern = false;
                }
                _ => {
                    return Err(format!(
                        "expected quantifier pattern, qid, or skolemid; found {}",
                        node_to_string(node)
                    ));
                }
            }
        }
        match (qid.clone(), skolemid) {
            (Some(q), Some(skolem)) => {
                let expected_skolemid = mk_skolem_id(&q);
                if skolem == expected_skolemid {
                    Ok((Arc::new(triggers), qid))
                } else {
                    Err(format!(
                        "for qid {}, expected skolemid {}; found {}",
                        q, expected_skolemid, skolem
                    ))
                }
            }
            (Some(q), None) => Err(format!(
                "for qid {}, expected skolemid {} but found no skolemid at all",
                q,
                mk_skolem_id(&q)
            )),
            (None, Some(_)) => Err(format!("skolemid must be accompanied by a qid")),
            (None, None) => Ok((Arc::new(triggers), qid)),
        }
    }

    fn nodes_to_named(&self, nodes: &[Node]) -> Result<Option<Ident>, String> {
        let mut named = None;
        let mut consume_named = false;

        for node in nodes {
            match node {
                Node::Atom(s) if s.to_string() == ":named" => {
                    consume_named = true;
                }
                Node::Atom(s) if consume_named && named.is_none() => {
                    named = Some(Arc::new(s.clone()));
                    consume_named = false;
                }
                _ => {
                    return Err(format!("expected :named; found {}", node_to_string(node)));
                }
            }
        }

        Ok(named)
    }

    fn node_to_quant_or_lambda_expr(
        &self,
        quantchooselambda: QuantOrChooseOrLambda,
        binder_nodes: &[Node],
        expr: &Node,
    ) -> Result<Expr, String> {
        let binders = self.nodes_to_binders(binder_nodes, &|n| self.node_to_typ(n))?;
        let (expr, triggers, qid) = match &expr {
            Node::List(nodes) if nodes.len() >= 2 => match &nodes[0] {
                Node::Atom(s) if s.to_string() == "!" => {
                    let (triggers, qid) = self.nodes_to_triggers_and_qid(&nodes[2..])?;
                    (&nodes[1], triggers, qid)
                }
                _ => (expr, Arc::new(vec![]), None),
            },
            _ => (expr, Arc::new(vec![]), None),
        };
        let expr = self.node_to_expr(expr)?;
        let (body, bind) = match quantchooselambda {
            QuantOrChooseOrLambda::Quant(quant) => {
                (expr, BindX::Quant(quant, binders, triggers, qid))
            }
            QuantOrChooseOrLambda::Choose(body) => {
                (body, BindX::Choose(binders, triggers, qid, expr))
            }
            QuantOrChooseOrLambda::Lambda => (expr, BindX::Lambda(binders, triggers, qid)),
        };
        Ok(Arc::new(ExprX::Bind(Arc::new(bind), body)))
    }

    pub fn node_to_stmt(&self, node: &Node) -> Result<Stmt, String> {
        match node {
            Node::List(nodes) => match &nodes[..] {
                [Node::Atom(s), e] if s.to_string() == "assume" => {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assume(expr)))
                }
                [Node::Atom(s), e] if s.to_string() == "assert" => {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assert(None, self.message_interface.empty(), None, expr)))
                }
                [Node::Atom(s), Node::Atom(x)] if s.to_string() == "havoc" && is_symbol(x) => {
                    Ok(Arc::new(StmtX::Havoc(Arc::new(x.clone()))))
                }
                [Node::Atom(s), Node::Atom(x), e] if s.to_string() == "assign" && is_symbol(x) => {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assign(Arc::new(x.clone()), expr)))
                }
                [Node::Atom(s), Node::Atom(snap)]
                    if s.to_string() == "snapshot" && is_symbol(snap) =>
                {
                    Ok(Arc::new(StmtX::Snapshot(Arc::new(snap.clone()))))
                }
                [Node::Atom(s), Node::List(nodes), Node::List(filter), e]
                    if s.to_string() == "assert" && filter.len() <= 1 =>
                {
                    let labels = self.nodes_to_labels(nodes)?;
                    let error = self.message_interface.from_labels(&labels);
                    let filter = self.nodes_to_filter(filter)?;
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assert(None, error, filter, expr)))
                }
                [Node::Atom(s), e] if s.to_string() == "deadend" => {
                    let stmt = self.node_to_stmt(&e)?;
                    Ok(Arc::new(StmtX::DeadEnd(stmt)))
                }
                [Node::Atom(s), Node::Atom(label), e] if s.to_string() == "breakable" => {
                    let stmt = self.node_to_stmt(&e)?;
                    Ok(Arc::new(StmtX::Breakable(Arc::new(label.clone()), stmt)))
                }
                [Node::Atom(s), Node::Atom(label)] if s.to_string() == "break" => {
                    Ok(Arc::new(StmtX::Break(Arc::new(label.clone()))))
                }
                _ => match &nodes[0] {
                    Node::Atom(s) if s.to_string() == "block" => {
                        Ok(Arc::new(StmtX::Block(self.nodes_to_stmts(&nodes[1..])?)))
                    }
                    Node::Atom(s) if s.to_string() == "switch" => {
                        Ok(Arc::new(StmtX::Switch(self.nodes_to_stmts(&nodes[1..])?)))
                    }
                    _ => Err(format!("expected statement, found: {}", node_to_string(node))),
                },
            },
            _ => Err(format!("expected statement, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_stmts(&self, nodes: &[Node]) -> Result<Stmts, String> {
        map_nodes_to_vec(nodes, &|n| self.node_to_stmt(n))
    }

    fn node_to_decl(&self, node: &Node) -> Result<Decl, String> {
        match node {
            Node::List(nodes) => match &nodes[..] {
                [Node::Atom(s), Node::Atom(x), Node::Atom(p)]
                    if s.to_string() == "declare-sort" && is_symbol(x) && p == "0" =>
                {
                    Ok(Arc::new(DeclX::Sort(Arc::new(x.clone()))))
                }
                [Node::Atom(s), Node::List(decls), Node::List(defns)]
                    if s.to_string() == "declare-datatypes" && decls.len() == defns.len() =>
                {
                    // ((Datatype1 0) (Datatype2 0) ...)
                    let decls = decls
                        .iter()
                        .map(|node| {
                            match node {
                                Node::List(kv) => match &kv[..] {
                                    [Node::Atom(name), Node::Atom(params)] if params == "0" => {
                                        return Ok(name.clone());
                                    }
                                    _ => {}
                                },
                                _ => {}
                            }
                            Err(format!(
                                "expected datatype declaration, found: {}",
                                node_to_string(node)
                            ))
                        })
                        .collect::<Result<Vec<String>, String>>()?;

                    // (
                    //      ( (Datatype1Variant1 <fields>) (Datatype1Variant2 <fields) )
                    //      ( (Datatype2Variant1 <fields>) )
                    //      ...
                    // )
                    let defns = defns
                        .iter()
                        .map(|node| match node {
                            Node::List(variants) => variants
                                .iter()
                                .map(|variant| {
                                    self.node_to_multibinder(variant, &|field| {
                                        self.node_to_binder(field, &|t| self.node_to_typ(t))
                                    })
                                })
                                .collect::<Result<Vec<crate::ast::Variant>, String>>()
                                .map(Arc::new),
                            _ => Err(format!(
                                "expected list of variants, found: {}",
                                node_to_string(node)
                            )),
                        })
                        .collect::<Result<Vec<crate::ast::Variants>, String>>()?;

                    let ds = decls
                        .into_iter()
                        .zip(defns.into_iter())
                        .map(|(name, variants)| {
                            Arc::new(BinderX { name: Arc::new(name), a: variants })
                        })
                        .collect();
                    Ok(Arc::new(DeclX::Datatypes(Arc::new(ds))))
                }
                [Node::Atom(s), Node::Atom(x), t]
                    if s.to_string() == "declare-const" && is_symbol(x) =>
                {
                    let typ = self.node_to_typ(t)?;
                    Ok(Arc::new(DeclX::Const(Arc::new(x.clone()), typ)))
                }
                [Node::Atom(s), Node::Atom(x), Node::List(ts), t]
                    if s.to_string() == "declare-fun" && is_symbol(x) =>
                {
                    let mut typs: Vec<Typ> = Vec::new();
                    for ta in ts {
                        typs.push(self.node_to_typ(ta)?);
                    }
                    let typ = self.node_to_typ(t)?;
                    Ok(Arc::new(DeclX::Fun(Arc::new(x.clone()), Arc::new(typs), typ)))
                }
                [Node::Atom(s), Node::Atom(x), t]
                    if s.to_string() == "declare-var" && is_symbol(x) =>
                {
                    let typ = self.node_to_typ(t)?;
                    Ok(Arc::new(DeclX::Var(Arc::new(x.clone()), typ)))
                }
                [Node::Atom(s), axiom_node] if s.to_string() == "axiom" => {
                    let (e, named) = match &axiom_node {
                        Node::List(nodes) if nodes.len() >= 2 => match &nodes[0] {
                            Node::Atom(s) if s.to_string() == "!" => {
                                let named = self.nodes_to_named(&nodes[2..])?;
                                (&nodes[1], named)
                            }
                            _ => (axiom_node, None),
                        },
                        _ => (axiom_node, None),
                    };
                    let expr = self.node_to_expr(e)?;
                    Ok(Arc::new(DeclX::Axiom(Axiom { named, expr })))
                }
                _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
            },
            _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_decls(&self, nodes: &[Node]) -> Result<Decls, String> {
        map_nodes_to_vec(nodes, &|d| self.node_to_decl(d))
    }

    pub(crate) fn node_to_command(&self, node: &Node) -> Result<Command, String> {
        match node {
            Node::List(nodes) if nodes.len() >= 1 => match &nodes[0] {
                Node::Atom(s) if s.to_string() == "push" && nodes.len() == 1 => {
                    Ok(Arc::new(CommandX::Push))
                }
                Node::Atom(s) if s.to_string() == "pop" && nodes.len() == 1 => {
                    Ok(Arc::new(CommandX::Pop))
                }
                Node::Atom(s) if s.to_string() == "set-option" && nodes.len() == 3 => {
                    match &nodes[..] {
                        [_, Node::Atom(option), Node::Atom(value)] if option.starts_with(":") => {
                            let opt = Arc::new(option[1..].to_string());
                            let val = Arc::new(value.clone());
                            Ok(Arc::new(CommandX::SetOption(opt, val)))
                        }
                        _ => Err(format!("expected command, found: {}", node_to_string(node))),
                    }
                }
                Node::Atom(s) if s.to_string() == "check-valid" && nodes.len() >= 2 => {
                    let assertion = self.node_to_stmt(&nodes[nodes.len() - 1])?;
                    let local = self.nodes_to_decls(&nodes[1..nodes.len() - 1])?;
                    let query = Arc::new(QueryX { local, assertion });
                    Ok(Arc::new(CommandX::CheckValid(query)))
                }
                _ => {
                    let decl = self.node_to_decl(&node)?;
                    Ok(Arc::new(CommandX::Global(decl)))
                }
            },
            _ => Err(format!("expected command, found: {}", node_to_string(node))),
        }
    }

    pub fn nodes_to_commands(&self, nodes: &[Node]) -> Result<Commands, String> {
        map_nodes_to_vec(nodes, &|c| self.node_to_command(c))
    }

    fn node_to_model_def(&self, node: &Node) -> Result<Option<ModelDef>, String> {
        match node {
            Node::List(nodes) => match &nodes[..] {
                [Node::Atom(s), Node::Atom(x), Node::List(param_nodes), t, body]
                    if s.to_string() == "define-fun" && is_symbol(x) =>
                {
                    let name = Arc::new(x.clone());
                    let params = self.nodes_to_binders(param_nodes, &|t| self.node_to_typ(t))?;
                    let ret = self.node_to_typ(t)?;
                    let body = Arc::new(node_to_string(body));
                    Ok(Some(Arc::new(ModelDefX { name, params, ret, body })))
                }
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }

    fn nodes_to_model_defs(&self, nodes: &[Node]) -> Result<ModelDefs, String> {
        map_nodes_to_vec_opt(nodes, &|n| self.node_to_model_def(n))
    }

    pub fn node_to_model(&self, node: &Node) -> Result<ModelDefs, String> {
        match node {
            Node::Atom(_) => Err(format!("expected model, found: {}", node_to_string(node))),
            Node::List(nodes) => self.nodes_to_model_defs(nodes),
        }
    }

    pub fn lines_to_model(&self, lines: &Vec<String>) -> ModelDefs {
        let node = parse_sexpression(lines);
        self.node_to_model(&node).expect("failed to parse SMT model")
    }
}

pub(crate) fn parse_sexpression(lines: &Vec<String>) -> Node {
    let mut model_bytes: Vec<u8> = Vec::new();
    for line in lines {
        writeln!(model_bytes, "{}", line).expect("model_bytes");
    }
    let mut parser = sise::Parser::new(&model_bytes[..]);
    let node = sise::read_into_tree(&mut parser).unwrap();
    node
}
