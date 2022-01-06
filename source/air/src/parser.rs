use crate::ast::{
    BinaryOp, BindX, Binder, BinderX, Binders, Command, CommandX, Commands, Constant, Decl, DeclX,
    Decls, Expr, ExprX, Exprs, MultiOp, Quant, QueryX, Span, Spans, Stmt, StmtX, Stmts, Trigger,
    Triggers, Typ, TypX, UnaryOp,
};
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
    return None;
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

pub struct Parser {}

impl Parser {
    pub fn new() -> Self {
        Parser {}
    }

    pub(crate) fn node_to_typ(&self, node: &Node) -> Result<Typ, String> {
        match node {
            Node::Atom(s) if s.to_string() == "Bool" => Ok(Arc::new(TypX::Bool)),
            Node::Atom(s) if s.to_string() == "Int" => Ok(Arc::new(TypX::Int)),
            Node::Atom(s) if s.to_string() == "Fun" => Ok(Arc::new(TypX::Lambda)),
            Node::Atom(s) if is_symbol(s) => Ok(Arc::new(TypX::Named(Arc::new(s.clone())))),
            Node::List(nodes) if is_bitvec(nodes).is_some() => {
                Ok(Arc::new(TypX::BitVec(is_bitvec(nodes).unwrap())))
            }
            _ => Err(format!("expected type, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_spans(&self, labels: &Vec<Node>) -> Result<Spans, String> {
        let mut spans: Vec<Span> = Vec::new();
        for label in labels {
            match label {
                Node::Atom(label) if label.starts_with("\"") && label.ends_with("\"") => {
                    let raw_span = Arc::new(());
                    let as_string = label[1..label.len() - 1].to_string();
                    spans.push(Span { description: None, raw_span, as_string });
                }
                _ => {
                    return Err(format!(
                        "expected quoted string, found: {}",
                        node_to_string(label)
                    ));
                }
            }
        }
        Ok(Arc::new(spans))
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
                    [Node::Atom(s), Node::List(labels), e] if s.to_string() == "location" => {
                        let spans = self.nodes_to_spans(labels)?;
                        let expr = self.node_to_expr(e)?;
                        return Ok(Arc::new(ExprX::LabeledAssertion(spans, expr)));
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
                        return self.node_to_quant_expr(Some(Quant::Forall), binders, e);
                    }
                    [Node::Atom(s), Node::List(binders), e] if s.to_string() == "exists" => {
                        return self.node_to_quant_expr(Some(Quant::Exists), binders, e);
                    }
                    [Node::Atom(s), Node::List(binders), e] if s.to_string() == "lambda" => {
                        let binders = self.nodes_to_binders(binders, &|n| self.node_to_typ(n))?;
                        let bind = Arc::new(BindX::Lambda(binders));
                        return Ok(Arc::new(ExprX::Bind(bind, self.node_to_expr(e)?)));
                    }
                    [Node::Atom(s), binder, e] if s.to_string() == "choose" => {
                        return self.node_to_quant_expr(None, &[binder.clone()], e);
                    }
                    _ => {}
                }
                match &nodes[0] {
                    Node::Atom(s) if s.to_string() == "apply" && nodes.len() >= 3 => {
                        let typ = self.node_to_typ(&nodes[1])?;
                        let f = self.node_to_expr(&nodes[2])?;
                        let args = self.nodes_to_exprs(&nodes[3..])?;
                        return Ok(Arc::new(ExprX::ApplyLambda(typ, f, args)));
                    }
                    _ => {}
                }
                let args = self.nodes_to_exprs(&nodes[1..])?;
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

    fn nodes_to_multibinders<A, F>(
        &self,
        nodes: &[Node],
        f: &F,
    ) -> Result<Binders<Arc<Vec<A>>>, String>
    where
        A: Clone,
        F: Fn(&Node) -> Result<A, String>,
    {
        let mut binders: Vec<Binder<Arc<Vec<A>>>> = Vec::new();
        for node in nodes {
            binders.push(self.node_to_multibinder(node, f)?);
        }
        Ok(Arc::new(binders))
    }

    fn node_to_let_expr(&self, binder_nodes: &[Node], expr: &Node) -> Result<Expr, String> {
        let binders = self.nodes_to_binders(binder_nodes, &|n| self.node_to_expr(n))?;
        Ok(crate::ast_util::mk_let(&binders, &self.node_to_expr(expr)?))
    }

    fn nodes_to_triggers(&self, nodes: &[Node]) -> Result<Triggers, String> {
        let mut triggers: Vec<Trigger> = Vec::new();
        let mut expect_pattern = true;
        for node in nodes {
            match node {
                Node::Atom(s) if s.to_string() == ":pattern" && expect_pattern => {}
                Node::List(trigger_nodes) if !expect_pattern => {
                    triggers.push(self.nodes_to_exprs(trigger_nodes)?);
                }
                _ => {
                    return Err(format!(
                        "expected quantifier pattern, found {}",
                        node_to_string(node)
                    ));
                }
            }
            expect_pattern = !expect_pattern;
        }
        Ok(Arc::new(triggers))
    }

    // quant = None: Choose
    // quant = Some(Quant): forall/exists
    fn node_to_quant_expr(
        &self,
        quant: Option<Quant>,
        binder_nodes: &[Node],
        expr: &Node,
    ) -> Result<Expr, String> {
        let binders = self.nodes_to_binders(binder_nodes, &|n| self.node_to_typ(n))?;
        let (body, triggers) = match &expr {
            Node::List(nodes) if nodes.len() >= 2 => match &nodes[0] {
                Node::Atom(s) if s.to_string() == "!" => {
                    (&nodes[1], self.nodes_to_triggers(&nodes[2..])?)
                }
                _ => (expr, Arc::new(vec![])),
            },
            _ => (expr, Arc::new(vec![])),
        };
        let bind = match quant {
            None => {
                assert_eq!(binders.len(), 1);
                Arc::new(BindX::Choose(binders[0].clone(), triggers))
            }
            Some(quant) => Arc::new(BindX::Quant(quant, binders, triggers)),
        };
        Ok(Arc::new(ExprX::Bind(bind, self.node_to_expr(body)?)))
    }

    pub(crate) fn node_to_stmt(&self, node: &Node) -> Result<Stmt, String> {
        match node {
            Node::List(nodes) => match &nodes[..] {
                [Node::Atom(s), e] if s.to_string() == "assume" => {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assume(expr)))
                }
                [Node::Atom(s), e] if s.to_string() == "assert" => {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assert(Arc::new(vec![]), expr)))
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
                [Node::Atom(s), Node::List(labels), e] if s.to_string() == "assert" => {
                    let spans = self.nodes_to_spans(labels)?;
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assert(spans, expr)))
                }
                [Node::Atom(s), e] if s.to_string() == "deadend" => {
                    let stmt = self.node_to_stmt(&e)?;
                    Ok(Arc::new(StmtX::DeadEnd(stmt)))
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
                [Node::Atom(s), Node::Atom(x)]
                    if s.to_string() == "declare-sort" && is_symbol(x) =>
                {
                    Ok(Arc::new(DeclX::Sort(Arc::new(x.clone()))))
                }
                [Node::Atom(s), Node::List(l), Node::List(datatypes)]
                    if s.to_string() == "declare-datatypes" && l.len() == 0 =>
                {
                    let ds = self.nodes_to_multibinders(datatypes, &|variant| {
                        self.node_to_multibinder(variant, &|field| {
                            self.node_to_binder(field, &|t| self.node_to_typ(t))
                        })
                    })?;
                    Ok(Arc::new(DeclX::Datatypes(ds)))
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
                [Node::Atom(s), e] if s.to_string() == "axiom" => {
                    let expr = self.node_to_expr(e)?;
                    Ok(Arc::new(DeclX::Axiom(expr)))
                }
                _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
            },
            _ => Err(format!("expected declaration, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_decls(&self, nodes: &[Node]) -> Result<Decls, String> {
        map_nodes_to_vec(nodes, &|d| self.node_to_decl(d))
    }

    pub fn node_to_command(&self, node: &Node) -> Result<Command, String> {
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
        let mut model_bytes: Vec<u8> = Vec::new();
        for line in lines {
            writeln!(model_bytes, "{}", line).expect("model_bytes");
        }
        let mut parser = sise::Parser::new(&model_bytes[..]);
        let node = sise::read_into_tree(&mut parser).unwrap();
        self.node_to_model(&node).expect("failed to parse SMT model")
    }
}
