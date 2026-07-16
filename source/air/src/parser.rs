use crate::ast::{
    Axiom, BinaryOp, BindX, Binder, BinderX, Binders, Command, CommandX, Commands, Constant, Decl,
    DeclX, Decls, Expr, ExprX, Exprs, Ident, MultiOp, Qid, Quant, QueryX, Relation, RoundingMode,
    Stmt, StmtX, Stmts, Trigger, Triggers, Typ, TypX, UnaryOp,
};
use crate::def::mk_skolem_id;
use crate::messages::ArcDynMessageLabel;
use crate::model::{ModelDef, ModelDefX, ModelDefs};
use crate::printer::node_to_string;
use std::sync::Arc;

// Following SMT-LIB syntax specification
fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c)
}

fn is_symbol(s: &String) -> bool {
    s.len() > 0 && s.chars().all(is_symbol_char)
}

fn is_bitvec(nodes: &Vec<sise::TreeNode>) -> Option<u32> {
    if nodes[0] == sise::TreeNode::Atom("_".to_string())
        && nodes[1] == sise::TreeNode::Atom("BitVec".to_string())
        && nodes.len() == 3
    {
        if let sise::TreeNode::Atom(s) = &nodes[2] {
            match s.parse::<u32>() {
                Ok(n) => return Some(n),
                Err(_) => return None,
            }
        }
    }
    None
}

fn is_float_type(nodes: &Vec<sise::TreeNode>) -> Option<Typ> {
    if nodes[0] == sise::TreeNode::Atom("_".to_string())
        && nodes[1] == sise::TreeNode::Atom("FloatingPoint".to_string())
        && nodes.len() == 4
    {
        if let (sise::TreeNode::Atom(s2), sise::TreeNode::Atom(s3)) = (&nodes[2], &nodes[3]) {
            match (s2.parse::<u32>(), s3.parse::<u32>()) {
                (Ok(exp_bits), Ok(sig_bits)) => {
                    return Some(Arc::new(TypX::Float { exp_bits, sig_bits }));
                }
                _ => return None,
            }
        }
    }
    None
}

fn underscore_atom_atom_expr(s1: &str, s2: &str) -> Option<Constant> {
    let value = s1.strip_prefix("bv")?;
    let width = s2.parse::<u32>().ok()?;
    Some(Constant::BitVec(Arc::new(value.to_owned()), width))
}

fn relation_binary_op(n1: &sise::TreeNode, n2: &sise::TreeNode) -> Option<BinaryOp> {
    match (n1, n2) {
        (sise::TreeNode::Atom(s1), sise::TreeNode::Atom(s2)) => {
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

fn field_update_binary_op(n1: &sise::TreeNode, n2: &sise::TreeNode) -> Option<BinaryOp> {
    match (n1, n2) {
        (sise::TreeNode::Atom(s1), sise::TreeNode::Atom(s2)) if s1.as_str() == "update-field" => {
            Some(BinaryOp::FieldUpdate(Arc::new(s2.clone())))
        }
        _ => None,
    }
}

fn map_nodes_to_vec<A, F>(nodes: &[sise::TreeNode], f: &F) -> Result<Arc<Vec<A>>, String>
where
    F: Fn(&sise::TreeNode) -> Result<A, String>,
{
    let mut v: Vec<A> = Vec::new();
    for node in nodes.iter() {
        v.push(f(node)?);
    }
    Ok(Arc::new(v))
}

fn map_nodes_to_vec_opt<A, F>(nodes: &[sise::TreeNode], f: &F) -> Result<Arc<Vec<A>>, String>
where
    F: Fn(&sise::TreeNode) -> Result<Option<A>, String>,
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

    pub(crate) fn node_to_typ(&self, node: &sise::TreeNode) -> Result<Typ, String> {
        match node {
            sise::TreeNode::Atom(s) if s == "Bool" => Ok(Arc::new(TypX::Bool)),
            sise::TreeNode::Atom(s) if s == "Int" => Ok(Arc::new(TypX::Int)),
            sise::TreeNode::Atom(s) if s == "Real" => Ok(Arc::new(TypX::Real)),
            sise::TreeNode::Atom(s) if s == "Fun" => Ok(Arc::new(TypX::Fun)),
            sise::TreeNode::Atom(s) if s == "Float16" => {
                Ok(Arc::new(TypX::Float { exp_bits: 5, sig_bits: 11 }))
            }
            sise::TreeNode::Atom(s) if s == "Float32" => {
                Ok(Arc::new(TypX::Float { exp_bits: 8, sig_bits: 24 }))
            }
            sise::TreeNode::Atom(s) if s == "Float64" => {
                Ok(Arc::new(TypX::Float { exp_bits: 11, sig_bits: 53 }))
            }
            sise::TreeNode::Atom(s) if s == "Float128" => {
                Ok(Arc::new(TypX::Float { exp_bits: 15, sig_bits: 113 }))
            }
            sise::TreeNode::Atom(s) if is_symbol(s) => {
                Ok(Arc::new(TypX::Named(Arc::new(s.clone()))))
            }
            sise::TreeNode::List(nodes) if is_bitvec(nodes).is_some() => {
                Ok(Arc::new(TypX::BitVec(is_bitvec(nodes).unwrap())))
            }
            sise::TreeNode::List(nodes) if is_float_type(nodes).is_some() => {
                Ok(is_float_type(nodes).unwrap())
            }
            _ => Err(format!("expected type, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_labels(
        &self,
        nodes: &Vec<sise::TreeNode>,
    ) -> Result<Vec<ArcDynMessageLabel>, String> {
        let mut labels: Vec<ArcDynMessageLabel> = Vec::new();
        for node in nodes {
            match node {
                sise::TreeNode::Atom(label) if label.starts_with("\"") && label.ends_with("\"") => {
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

    fn nodes_to_filter(&self, nodes: &Vec<sise::TreeNode>) -> Result<Option<Ident>, String> {
        if nodes.len() == 0 {
            Ok(None)
        } else {
            assert!(nodes.len() == 1);
            match &nodes[0] {
                sise::TreeNode::Atom(s) if is_symbol(s) => Ok(Some(Arc::new(s.clone()))),
                _ => Err(format!("expected symbol, found: {}", node_to_string(&nodes[0]))),
            }
        }
    }

    pub(crate) fn node_to_expr(&self, node: &sise::TreeNode) -> Result<Expr, String> {
        match node {
            sise::TreeNode::Atom(s) if s == "true" => {
                Ok(Arc::new(ExprX::Const(Constant::Bool(true))))
            }
            sise::TreeNode::Atom(s) if s == "false" => {
                Ok(Arc::new(ExprX::Const(Constant::Bool(false))))
            }
            sise::TreeNode::Atom(s) if s.len() > 0 && s.chars().all(|c| c.is_ascii_digit()) => {
                Ok(Arc::new(ExprX::Const(Constant::Nat(Arc::new(s.clone())))))
            }
            sise::TreeNode::Atom(s) if crate::ast_util::is_valid_real(s) => {
                Ok(Arc::new(ExprX::Const(Constant::Real(Arc::new(s.clone())))))
            }
            sise::TreeNode::Atom(s) if is_symbol(s) => {
                Ok(Arc::new(ExprX::Var(Arc::new(s.clone()))))
            }
            sise::TreeNode::List(nodes) if nodes.len() > 0 => {
                match &nodes[..] {
                    [
                        sise::TreeNode::Atom(s),
                        sise::TreeNode::List(nodes),
                        sise::TreeNode::List(filter),
                        e,
                    ] if s == "location" && filter.len() <= 1 => {
                        let error =
                            self.message_interface.from_labels(&self.nodes_to_labels(nodes)?);
                        let filter = self.nodes_to_filter(filter)?;
                        let expr = self.node_to_expr(e)?;
                        return Ok(Arc::new(ExprX::LabeledAssertion(None, error, filter, expr)));
                    }
                    [
                        sise::TreeNode::Atom(s),
                        sise::TreeNode::List(nodes),
                        sise::TreeNode::List(filter),
                        e,
                    ] if s == "axiom_location" && filter.len() <= 1 => {
                        let labels = self.nodes_to_labels(nodes)?;
                        let filter = self.nodes_to_filter(filter)?;
                        let expr = self.node_to_expr(e)?;
                        return Ok(Arc::new(ExprX::LabeledAxiom(labels, filter, expr)));
                    }
                    [
                        sise::TreeNode::Atom(s),
                        sise::TreeNode::Atom(snap),
                        sise::TreeNode::Atom(x),
                    ] if s == "old" && is_symbol(snap) && is_symbol(x) => {
                        return Ok(Arc::new(ExprX::Old(
                            Arc::new(snap.clone()),
                            Arc::new(x.clone()),
                        )));
                    }
                    [sise::TreeNode::Atom(s), sise::TreeNode::List(binders), e] if s == "let" => {
                        return self.node_to_let_expr(binders, e);
                    }
                    [sise::TreeNode::Atom(s), sise::TreeNode::List(binders), e]
                        if s == "forall" =>
                    {
                        let quantchooselambda = QuantOrChooseOrLambda::Quant(Quant::Forall);
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e);
                    }
                    [sise::TreeNode::Atom(s), sise::TreeNode::List(binders), e]
                        if s == "exists" =>
                    {
                        let quantchooselambda = QuantOrChooseOrLambda::Quant(Quant::Exists);
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e);
                    }
                    [sise::TreeNode::Atom(s), sise::TreeNode::List(binders), e]
                        if s == "lambda" =>
                    {
                        let quantchooselambda = QuantOrChooseOrLambda::Lambda;
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e);
                    }
                    [sise::TreeNode::Atom(s), sise::TreeNode::List(binders), e1, e2]
                        if s == "choose" =>
                    {
                        let quantchooselambda =
                            QuantOrChooseOrLambda::Choose(self.node_to_expr(e2)?);
                        return self.node_to_quant_or_lambda_expr(quantchooselambda, binders, e1);
                    }
                    [
                        sise::TreeNode::Atom(s),
                        sise::TreeNode::Atom(s1),
                        sise::TreeNode::Atom(s2),
                    ] if s == "_" && underscore_atom_atom_expr(s1, s2).is_some() => {
                        return Ok(Arc::new(ExprX::Const(
                            underscore_atom_atom_expr(s1, s2).unwrap(),
                        )));
                    }
                    _ => {}
                }
                match &nodes[0] {
                    sise::TreeNode::Atom(s) if s == "apply" && nodes.len() >= 3 => {
                        let typ = self.node_to_typ(&nodes[1])?;
                        let f = self.node_to_expr(&nodes[2])?;
                        let args = self.nodes_to_exprs(&nodes[3..])?;
                        return Ok(Arc::new(ExprX::ApplyFun(typ, f, args)));
                    }
                    sise::TreeNode::Atom(s) if s == "array" && nodes.len() >= 1 => {
                        let args = self.nodes_to_exprs(&nodes[1..])?;
                        return Ok(Arc::new(ExprX::Array(args)));
                    }
                    _ => {}
                }
                let round = |args: &mut Exprs| {
                    Arc::make_mut(args).remove(0);
                    match nodes.get(1) {
                        Some(sise::TreeNode::Atom(s)) => match s.as_str() {
                            "RNE" | "roundNearestTiesToEven" => Ok(RoundingMode::RNE),
                            "RNA" | "roundNearestTiesToAway" => Ok(RoundingMode::RNA),
                            "RTP" | "roundTowardPositive" => Ok(RoundingMode::RTP),
                            "RTN" | "roundTowardNegative" => Ok(RoundingMode::RTN),
                            "RTZ" | "roundTowardZero" => Ok(RoundingMode::RTZ),
                            _ => Err("expected rounding mode in fp operation"),
                        },
                        _ => Err("expected rounding mode in fp operation"),
                    }
                };
                let mut args = self.nodes_to_exprs(&nodes[1..])?;
                let uop = match &nodes[0] {
                    sise::TreeNode::Atom(s) if s == "not" => Some(UnaryOp::Not),
                    sise::TreeNode::Atom(s) if s == "bvnot" => Some(UnaryOp::BitNot),
                    sise::TreeNode::Atom(s) if s == "bvneg" => Some(UnaryOp::BitNeg),
                    sise::TreeNode::Atom(s) if s == "fp.neg" => Some(UnaryOp::FloatNeg),
                    sise::TreeNode::Atom(s) if s == "fp.roundToIntegral" => {
                        Some(UnaryOp::FloatRoundToInt(round(&mut args)?))
                    }
                    sise::TreeNode::Atom(s) if s == "fp.isNormal" => Some(UnaryOp::FloatIsNormal),
                    sise::TreeNode::Atom(s) if s == "fp.isSubnormal" => {
                        Some(UnaryOp::FloatIsSubnormal)
                    }
                    sise::TreeNode::Atom(s) if s == "fp.isZero" => Some(UnaryOp::FloatIsZero),
                    sise::TreeNode::Atom(s) if s == "fp.isInfinite" => {
                        Some(UnaryOp::FloatIsInfinite)
                    }
                    sise::TreeNode::Atom(s) if s == "fp.isNaN" => Some(UnaryOp::FloatIsNaN),
                    sise::TreeNode::Atom(s) if s == "fp.isNegative" => {
                        Some(UnaryOp::FloatIsNegative)
                    }
                    sise::TreeNode::Atom(s) if s == "fp.isPositive" => {
                        Some(UnaryOp::FloatIsPositive)
                    }
                    sise::TreeNode::List(nodes)
                        if nodes.len() == 4
                            && nodes[0] == sise::TreeNode::Atom("_".to_string())
                            && (nodes[1] == sise::TreeNode::Atom("to_fp".to_string())
                                || nodes[1]
                                    == sise::TreeNode::Atom("to_fp_unsigned".to_string())) =>
                    {
                        let signed = nodes[1] == sise::TreeNode::Atom("to_fp".to_string());
                        let exp_sig_bits = match (&nodes[2], &nodes[3]) {
                            (sise::TreeNode::Atom(s2), sise::TreeNode::Atom(s3)) => {
                                match (s2.parse::<u32>(), s3.parse::<u32>()) {
                                    (Ok(exp_bits), Ok(sig_bits)) => Some((exp_bits, sig_bits)),
                                    _ => None,
                                }
                            }
                            _ => None,
                        };
                        if let Some((exp_bits, sig_bits)) = exp_sig_bits {
                            if args.len() <= 1 && signed {
                                Some(UnaryOp::FloatFromIeeeBits { exp_bits, sig_bits })
                            } else if args.len() > 1 {
                                let round = round(&mut args)?;
                                Some(UnaryOp::FloatFrom { exp_bits, sig_bits, signed, round })
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    sise::TreeNode::List(nodes)
                        if nodes.len() == 3
                            && nodes[0] == sise::TreeNode::Atom("_".to_string())
                            && (nodes[1] == sise::TreeNode::Atom("fp.to_ubv".to_string())
                                || nodes[1] == sise::TreeNode::Atom("fp.to_sbv".to_string())) =>
                    {
                        let signed = nodes[1] == sise::TreeNode::Atom("fp.to_sbv".to_string());
                        let round = round(&mut args)?;
                        match &nodes[2] {
                            sise::TreeNode::Atom(s2) => match s2.parse::<u32>() {
                                Ok(bits) => Some(UnaryOp::FloatToBitVec { bits, signed, round }),
                                _ => None,
                            },
                            _ => None,
                        }
                    }
                    sise::TreeNode::Atom(s) if s == "fp.to_real" => Some(UnaryOp::FloatToReal),
                    sise::TreeNode::Atom(s) if s == "to_real" => Some(UnaryOp::ToReal),
                    sise::TreeNode::Atom(s) if s == "to_int" => Some(UnaryOp::RealToInt),
                    sise::TreeNode::List(nodes)
                        if nodes.len() == 4
                            && nodes[0] == sise::TreeNode::Atom("_".to_string())
                            && nodes[1] == sise::TreeNode::Atom("extract".to_string()) =>
                    {
                        match (&nodes[2], &nodes[3]) {
                            (sise::TreeNode::Atom(s2), sise::TreeNode::Atom(s3)) => {
                                match (s2.parse::<u32>(), s3.parse::<u32>()) {
                                    (Ok(hi), Ok(lo)) => Some(UnaryOp::BitExtract(hi, lo)),
                                    _ => None,
                                }
                            }
                            _ => None,
                        }
                    }
                    sise::TreeNode::List(nodes)
                        if nodes.len() == 3
                            && nodes[0] == sise::TreeNode::Atom("_".to_string())
                            && (nodes[1] == sise::TreeNode::Atom("zero_extend".to_string())
                                || nodes[1] == sise::TreeNode::Atom("sign_extend".to_string())) =>
                    {
                        match &nodes[2] {
                            sise::TreeNode::Atom(s2) => match s2.parse::<u32>() {
                                Ok(n) => {
                                    if nodes[1] == sise::TreeNode::Atom("zero_extend".to_string()) {
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
                    sise::TreeNode::Atom(s) if s == "=>" => Some(BinaryOp::Implies),
                    sise::TreeNode::Atom(s) if s == "=" => Some(BinaryOp::Eq),
                    sise::TreeNode::Atom(s) if s == "<=" => Some(BinaryOp::Le),
                    sise::TreeNode::Atom(s) if s == ">=" => Some(BinaryOp::Ge),
                    sise::TreeNode::Atom(s) if s == "<" => Some(BinaryOp::Lt),
                    sise::TreeNode::Atom(s) if s == ">" => Some(BinaryOp::Gt),
                    sise::TreeNode::Atom(s) if s == "div" => Some(BinaryOp::EuclideanDiv),
                    sise::TreeNode::Atom(s) if s == "mod" => Some(BinaryOp::EuclideanMod),
                    sise::TreeNode::Atom(s) if s == "/" => Some(BinaryOp::RealDiv),
                    sise::TreeNode::Atom(s) if s == "bvxor" => Some(BinaryOp::BitXor),
                    sise::TreeNode::Atom(s) if s == "bvand" => Some(BinaryOp::BitAnd),
                    sise::TreeNode::Atom(s) if s == "bvor" => Some(BinaryOp::BitOr),
                    sise::TreeNode::Atom(s) if s == "bvadd" => Some(BinaryOp::BitAdd),
                    sise::TreeNode::Atom(s) if s == "bvsub" => Some(BinaryOp::BitSub),
                    sise::TreeNode::Atom(s) if s == "bvmul" => Some(BinaryOp::BitMul),
                    sise::TreeNode::Atom(s) if s == "bvudiv" => Some(BinaryOp::BitUDiv),
                    sise::TreeNode::Atom(s) if s == "bvurem" => Some(BinaryOp::BitURem),
                    sise::TreeNode::Atom(s) if s == "bvult" => Some(BinaryOp::BitULt),
                    sise::TreeNode::Atom(s) if s == "bvugt" => Some(BinaryOp::BitUGt),
                    sise::TreeNode::Atom(s) if s == "bvule" => Some(BinaryOp::BitULe),
                    sise::TreeNode::Atom(s) if s == "bvuge" => Some(BinaryOp::BitUGe),
                    sise::TreeNode::Atom(s) if s == "bvlshr" => Some(BinaryOp::LShr),
                    sise::TreeNode::Atom(s) if s == "bvshl" => Some(BinaryOp::Shl),
                    sise::TreeNode::Atom(s) if s == "concat" => Some(BinaryOp::BitConcat),
                    sise::TreeNode::Atom(s) if s == "fp.add" => {
                        Some(BinaryOp::FloatAdd(round(&mut args)?))
                    }
                    sise::TreeNode::Atom(s) if s == "fp.sub" => {
                        Some(BinaryOp::FloatSub(round(&mut args)?))
                    }
                    sise::TreeNode::Atom(s) if s == "fp.mul" => {
                        Some(BinaryOp::FloatMul(round(&mut args)?))
                    }
                    sise::TreeNode::Atom(s) if s == "fp.div" => {
                        Some(BinaryOp::FloatDiv(round(&mut args)?))
                    }
                    sise::TreeNode::Atom(s) if s == "fp.eq" => Some(BinaryOp::FloatEq),
                    sise::TreeNode::Atom(s) if s == "fp.lt" => Some(BinaryOp::FloatLt),
                    sise::TreeNode::Atom(s) if s == "fp.gt" => Some(BinaryOp::FloatGt),
                    sise::TreeNode::Atom(s) if s == "fp.leq" => Some(BinaryOp::FloatLe),
                    sise::TreeNode::Atom(s) if s == "fp.geq" => Some(BinaryOp::FloatGe),
                    sise::TreeNode::List(nodes)
                        if nodes.len() == 3
                            && nodes[0] == sise::TreeNode::Atom("_".to_string())
                            && relation_binary_op(&nodes[1], &nodes[2]).is_some() =>
                    {
                        relation_binary_op(&nodes[1], &nodes[2])
                    }
                    sise::TreeNode::List(nodes)
                        if nodes.len() == 3
                            && nodes[0] == sise::TreeNode::Atom("_".to_string())
                            && field_update_binary_op(&nodes[1], &nodes[2]).is_some() =>
                    {
                        field_update_binary_op(&nodes[1], &nodes[2])
                    }
                    _ => None,
                };
                let lop = match &nodes[0] {
                    sise::TreeNode::Atom(s) if s == "and" => Some(MultiOp::And),
                    sise::TreeNode::Atom(s) if s == "or" => Some(MultiOp::Or),
                    sise::TreeNode::Atom(s) if s == "xor" => Some(MultiOp::Xor),
                    sise::TreeNode::Atom(s) if s == "+" => Some(MultiOp::Add),
                    sise::TreeNode::Atom(s) if s == "-" => Some(MultiOp::Sub),
                    sise::TreeNode::Atom(s) if s == "*" => Some(MultiOp::Mul),
                    sise::TreeNode::Atom(s) if s == "distinct" => Some(MultiOp::Distinct),
                    sise::TreeNode::Atom(s) if s == "fp" => Some(MultiOp::Float),
                    _ => None,
                };
                let ite = match &nodes[0] {
                    sise::TreeNode::Atom(s) if s == "ite" => true,
                    _ => false,
                };
                let fun = match &nodes[0] {
                    sise::TreeNode::Atom(s) if is_symbol(s) => Some(s),
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

    fn nodes_to_exprs(&self, nodes: &[sise::TreeNode]) -> Result<Exprs, String> {
        map_nodes_to_vec(nodes, &|n| self.node_to_expr(n))
    }

    fn node_to_binder<A, F>(&self, node: &sise::TreeNode, f: &F) -> Result<Binder<A>, String>
    where
        A: Clone,
        F: Fn(&sise::TreeNode) -> Result<A, String>,
    {
        match node {
            sise::TreeNode::List(nodes) => match &nodes[..] {
                [sise::TreeNode::Atom(name), node] if is_symbol(name) => {
                    let a = f(node)?;
                    return Ok(Arc::new(BinderX { name: Arc::new(name.clone()), a }));
                }
                _ => {}
            },
            _ => {}
        }
        Err(format!("expected binder (...), found: {}", node_to_string(node)))
    }

    fn node_to_multibinder<A, F>(
        &self,
        node: &sise::TreeNode,
        f: &F,
    ) -> Result<Binder<Arc<Vec<A>>>, String>
    where
        A: Clone,
        F: Fn(&sise::TreeNode) -> Result<A, String>,
    {
        match node {
            sise::TreeNode::List(nodes) => match &nodes[0] {
                sise::TreeNode::Atom(name) if is_symbol(name) => {
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

    fn nodes_to_binders<A, F>(&self, nodes: &[sise::TreeNode], f: &F) -> Result<Binders<A>, String>
    where
        A: Clone,
        F: Fn(&sise::TreeNode) -> Result<A, String>,
    {
        let mut binders: Vec<Binder<A>> = Vec::new();
        for node in nodes {
            binders.push(self.node_to_binder(node, f)?);
        }
        Ok(Arc::new(binders))
    }

    fn node_to_let_expr(
        &self,
        binder_nodes: &[sise::TreeNode],
        expr: &sise::TreeNode,
    ) -> Result<Expr, String> {
        let binders = self.nodes_to_binders(binder_nodes, &|n| self.node_to_expr(n))?;
        Ok(crate::ast_util::mk_let(&binders, &self.node_to_expr(expr)?))
    }

    fn nodes_to_triggers_and_qid(
        &self,
        nodes: &[sise::TreeNode],
    ) -> Result<(Triggers, Qid), String> {
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
                sise::TreeNode::Atom(s) if s == ":pattern" => {
                    consume_pattern = true;
                }
                sise::TreeNode::Atom(s) if s == ":qid" => {
                    consume_qid = true;
                }
                sise::TreeNode::Atom(s) if s == ":skolemid" => {
                    consume_skolemid = true;
                }
                sise::TreeNode::Atom(s) if consume_qid && qid.is_none() => {
                    qid = Some(Arc::new(s.clone()));
                    consume_qid = false;
                }
                sise::TreeNode::Atom(s) if consume_skolemid && skolemid.is_none() => {
                    skolemid = Some(s.clone());
                    consume_skolemid = false;
                }
                sise::TreeNode::List(trigger_nodes) if consume_pattern => {
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
                let expected_skolemid = mk_skolem_id(q.as_str());
                if skolem == expected_skolemid {
                    Ok((Arc::new(triggers), qid))
                } else {
                    Err(format!(
                        "for qid {}, expected skolemid {}; found {}",
                        q.as_str(),
                        expected_skolemid,
                        skolem
                    ))
                }
            }
            (Some(q), None) => Err(format!(
                "for qid {}, expected skolemid {} but found no skolemid at all",
                q.as_str(),
                mk_skolem_id(&q)
            )),
            (None, Some(_)) => Err(format!("skolemid must be accompanied by a qid")),
            (None, None) => Ok((Arc::new(triggers), qid)),
        }
    }

    fn nodes_to_named(&self, nodes: &[sise::TreeNode]) -> Result<Option<Ident>, String> {
        let mut named = None;
        let mut consume_named = false;

        for node in nodes {
            match node {
                sise::TreeNode::Atom(s) if s == ":named" => {
                    consume_named = true;
                }
                sise::TreeNode::Atom(s) if consume_named && named.is_none() => {
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
        binder_nodes: &[sise::TreeNode],
        expr: &sise::TreeNode,
    ) -> Result<Expr, String> {
        let binders = self.nodes_to_binders(binder_nodes, &|n| self.node_to_typ(n))?;
        let (expr, triggers, qid) = match &expr {
            sise::TreeNode::List(nodes) if nodes.len() >= 2 => match &nodes[0] {
                sise::TreeNode::Atom(s) if s == "!" => {
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

    pub fn node_to_stmt(&self, node: &sise::TreeNode) -> Result<Stmt, String> {
        match node {
            sise::TreeNode::List(nodes) => match &nodes[..] {
                [sise::TreeNode::Atom(s), e] if s == "assume" => {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assume(expr)))
                }
                [sise::TreeNode::Atom(s), e] if s == "assert" => {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assert(None, self.message_interface.empty(), None, expr)))
                }
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(x)]
                    if s == "havoc" && is_symbol(x) =>
                {
                    Ok(Arc::new(StmtX::Havoc(Arc::new(x.clone()))))
                }
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(x), e]
                    if s == "assign" && is_symbol(x) =>
                {
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assign(Arc::new(x.clone()), expr)))
                }
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(snap)]
                    if s == "snapshot" && is_symbol(snap) =>
                {
                    Ok(Arc::new(StmtX::Snapshot(Arc::new(snap.clone()))))
                }
                [
                    sise::TreeNode::Atom(s),
                    sise::TreeNode::List(nodes),
                    sise::TreeNode::List(filter),
                    e,
                ] if s == "assert" && filter.len() <= 1 => {
                    let labels = self.nodes_to_labels(nodes)?;
                    let error = self.message_interface.from_labels(&labels);
                    let filter = self.nodes_to_filter(filter)?;
                    let expr = self.node_to_expr(&e)?;
                    Ok(Arc::new(StmtX::Assert(None, error, filter, expr)))
                }
                [sise::TreeNode::Atom(s), e] if s == "deadend" => {
                    let stmt = self.node_to_stmt(&e)?;
                    Ok(Arc::new(StmtX::DeadEnd(stmt)))
                }
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(label), e] if s == "breakable" => {
                    let stmt = self.node_to_stmt(&e)?;
                    Ok(Arc::new(StmtX::Breakable(Arc::new(label.clone()), stmt)))
                }
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(label)] if s == "break" => {
                    Ok(Arc::new(StmtX::Break(Arc::new(label.clone()))))
                }
                _ => match &nodes[0] {
                    sise::TreeNode::Atom(s) if s == "block" => {
                        Ok(Arc::new(StmtX::Block(self.nodes_to_stmts(&nodes[1..])?)))
                    }
                    sise::TreeNode::Atom(s) if s == "switch" => {
                        Ok(Arc::new(StmtX::Switch(self.nodes_to_stmts(&nodes[1..])?)))
                    }
                    _ => Err(format!("expected statement, found: {}", node_to_string(node))),
                },
            },
            _ => Err(format!("expected statement, found: {}", node_to_string(node))),
        }
    }

    fn nodes_to_stmts(&self, nodes: &[sise::TreeNode]) -> Result<Stmts, String> {
        map_nodes_to_vec(nodes, &|n| self.node_to_stmt(n))
    }

    fn node_to_decl(&self, node: &sise::TreeNode) -> Result<Decl, String> {
        match node {
            sise::TreeNode::List(nodes) => match &nodes[..] {
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(x), sise::TreeNode::Atom(p)]
                    if s == "declare-sort" && is_symbol(x) && p == "0" =>
                {
                    Ok(Arc::new(DeclX::Sort(Arc::new(x.clone()))))
                }
                [
                    sise::TreeNode::Atom(s),
                    sise::TreeNode::List(decls),
                    sise::TreeNode::List(defns),
                ] if s == "declare-datatypes" && decls.len() == defns.len() => {
                    // ((Datatype1 0) (Datatype2 0) ...)
                    let decls = decls
                        .iter()
                        .map(|node| {
                            match node {
                                sise::TreeNode::List(kv) => match &kv[..] {
                                    [sise::TreeNode::Atom(name), sise::TreeNode::Atom(params)]
                                        if params == "0" =>
                                    {
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
                            sise::TreeNode::List(variants) => variants
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
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(x), t]
                    if s == "declare-const" && is_symbol(x) =>
                {
                    let typ = self.node_to_typ(t)?;
                    Ok(Arc::new(DeclX::Const(Arc::new(x.clone()), typ)))
                }
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(x), sise::TreeNode::List(ts), t]
                    if s == "declare-fun" && is_symbol(x) =>
                {
                    let mut typs: Vec<Typ> = Vec::new();
                    for ta in ts {
                        typs.push(self.node_to_typ(ta)?);
                    }
                    let typ = self.node_to_typ(t)?;
                    Ok(Arc::new(DeclX::Fun(Arc::new(x.clone()), Arc::new(typs), typ)))
                }
                [sise::TreeNode::Atom(s), sise::TreeNode::Atom(x), t]
                    if s == "declare-var" && is_symbol(x) =>
                {
                    let typ = self.node_to_typ(t)?;
                    Ok(Arc::new(DeclX::Var(Arc::new(x.clone()), typ)))
                }
                [sise::TreeNode::Atom(s), axiom_node] if s == "axiom" => {
                    let (e, named) = match &axiom_node {
                        sise::TreeNode::List(nodes) if nodes.len() >= 2 => match &nodes[0] {
                            sise::TreeNode::Atom(s) if s == "!" => {
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

    fn nodes_to_decls(&self, nodes: &[sise::TreeNode]) -> Result<Decls, String> {
        map_nodes_to_vec(nodes, &|d| self.node_to_decl(d))
    }

    pub(crate) fn node_to_command(&self, node: &sise::TreeNode) -> Result<Command, String> {
        match node {
            sise::TreeNode::List(nodes) if nodes.len() >= 1 => match &nodes[0] {
                sise::TreeNode::Atom(s) if s == "push" && nodes.len() == 1 => {
                    Ok(Arc::new(CommandX::Push))
                }
                sise::TreeNode::Atom(s) if s == "pop" && nodes.len() == 1 => {
                    Ok(Arc::new(CommandX::Pop))
                }
                sise::TreeNode::Atom(s) if s == "set-option" && nodes.len() == 3 => {
                    match &nodes[..] {
                        [_, sise::TreeNode::Atom(option), sise::TreeNode::Atom(value)]
                            if option.starts_with(":") =>
                        {
                            let opt = Arc::new(option[1..].to_string());
                            let val = Arc::new(value.clone());
                            Ok(Arc::new(CommandX::SetOption(opt, val)))
                        }
                        _ => Err(format!("expected command, found: {}", node_to_string(node))),
                    }
                }
                sise::TreeNode::Atom(s) if s == "check-valid" && nodes.len() >= 2 => {
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

    pub fn nodes_to_commands(&self, nodes: &[sise::TreeNode]) -> Result<Commands, String> {
        map_nodes_to_vec(nodes, &|c| self.node_to_command(c))
    }

    fn node_to_model_def(&self, node: &sise::TreeNode) -> Result<Option<ModelDef>, String> {
        match node {
            sise::TreeNode::List(nodes) => match &nodes[..] {
                [
                    sise::TreeNode::Atom(s),
                    sise::TreeNode::Atom(x),
                    sise::TreeNode::List(param_nodes),
                    t,
                    body,
                ] if s == "define-fun" && is_symbol(x) => {
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

    fn nodes_to_model_defs(&self, nodes: &[sise::TreeNode]) -> Result<ModelDefs, String> {
        map_nodes_to_vec_opt(nodes, &|n| self.node_to_model_def(n))
    }

    pub fn node_to_model(&self, node: &sise::TreeNode) -> Result<ModelDefs, String> {
        match node {
            sise::TreeNode::Atom(_) => {
                Err(format!("expected model, found: {}", node_to_string(node)))
            }
            sise::TreeNode::List(nodes) => self.nodes_to_model_defs(nodes),
        }
    }

    pub fn lines_to_model(&self, lines: &Vec<String>) -> ModelDefs {
        let node = parse_sexpression(lines);
        self.node_to_model(&node).expect("failed to parse SMT model")
    }
}

pub(crate) fn parse_sexpression(lines: &Vec<String>) -> sise::TreeNode {
    let expr = lines.join("\n");
    let mut parser = sise::Parser::new(expr.as_str());
    let node = sise::parse_tree(&mut parser).unwrap();
    node
}
