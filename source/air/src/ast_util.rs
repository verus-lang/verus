use crate::ast::{
    Axiom, BinaryOp, Bind, BindX, Binder, BinderX, Command, CommandX, Constant, Decl, DeclX, Expr,
    ExprX, Exprs, Ident, MultiOp, Qid, Quant, Trigger, Typ, TypX, Typs, UnaryOp,
};
use crate::context::SmtSolver;
use std::fmt::Debug;
use std::sync::Arc;

impl Debug for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Nat(n) => write!(f, "{}", n),
            Constant::BitVec(n, width) => write!(f, "{}(bv{})", n, width),
        }
    }
}

impl<A: Clone> BinderX<A> {
    pub fn new_a<B: Clone>(&self, a: B) -> Binder<B> {
        Arc::new(BinderX { name: self.name.clone(), a })
    }

    pub fn map_a<B: Clone>(&self, f: impl FnOnce(&A) -> B) -> Binder<B> {
        Arc::new(BinderX { name: self.name.clone(), a: f(&self.a) })
    }

    pub fn map_result<B: Clone, E>(
        &self,
        f: impl FnOnce(&A) -> Result<B, E>,
    ) -> Result<Binder<B>, E> {
        Ok(Arc::new(BinderX { name: self.name.clone(), a: f(&self.a)? }))
    }
}

impl<A: Clone + Debug> std::fmt::Debug for BinderX<A> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.name.fmt(fmt)?;
        fmt.write_str(" -> ")?;
        self.a.fmt(fmt)?;
        Ok(())
    }
}

impl ExprX {
    pub fn apply_or_var(x: Ident, args: Exprs) -> ExprX {
        if args.len() == 0 { ExprX::Var(x) } else { ExprX::Apply(x, args) }
    }
}

impl DeclX {
    pub fn fun_or_const(x: Ident, typs: Typs, typ: Typ) -> DeclX {
        if typs.len() == 0 { DeclX::Const(x, typ) } else { DeclX::Fun(x, typs, typ) }
    }
}

pub fn str_ident(x: &str) -> Ident {
    Arc::new(x.to_string())
}

pub fn ident_var(x: &Ident) -> Expr {
    Arc::new(ExprX::Var(x.clone()))
}

pub fn string_var(x: &String) -> Expr {
    Arc::new(ExprX::Var(Arc::new(x.clone())))
}

pub fn str_var(x: &str) -> Expr {
    Arc::new(ExprX::Var(Arc::new(x.to_string())))
}

pub fn ident_apply(x: &Ident, args: &Vec<Expr>) -> Expr {
    Arc::new(ExprX::Apply(x.clone(), Arc::new(args.clone())))
}

pub fn ident_apply_or_var(x: &Ident, args: &Vec<Expr>) -> Expr {
    Arc::new(ExprX::apply_or_var(x.clone(), Arc::new(args.clone())))
}

pub fn string_apply(x: &String, args: &Vec<Expr>) -> Expr {
    Arc::new(ExprX::Apply(Arc::new(x.clone()), Arc::new(args.clone())))
}

pub fn str_apply(x: &str, args: &Vec<Expr>) -> Expr {
    Arc::new(ExprX::Apply(Arc::new(x.to_string()), Arc::new(args.clone())))
}

pub fn int_typ() -> Typ {
    Arc::new(TypX::Int)
}

pub fn bool_typ() -> Typ {
    Arc::new(TypX::Bool)
}

pub fn ident_typ(x: &Ident) -> Typ {
    Arc::new(TypX::Named(x.clone()))
}

pub fn string_typ(x: &String) -> Typ {
    Arc::new(TypX::Named(Arc::new(x.clone())))
}

pub fn str_typ(x: &str) -> Typ {
    Arc::new(TypX::Named(Arc::new(x.to_string())))
}

pub fn bv_typ(width: u32) -> Typ {
    Arc::new(TypX::BitVec(width))
}

pub fn ident_binder<A: Clone>(x: &Ident, a: &A) -> Binder<A> {
    Arc::new(BinderX { name: x.clone(), a: a.clone() })
}

pub fn mk_bind_expr(bind: &Bind, body: &Expr) -> Expr {
    let n = match &**bind {
        BindX::Let(bs) => bs.len(),
        BindX::Quant(_, bs, _, _) => bs.len(),
        BindX::Lambda(..) | BindX::Choose(..) => 1,
    };
    if n == 0 { body.clone() } else { Arc::new(ExprX::Bind(bind.clone(), body.clone())) }
}

pub fn mk_let(binders: &Vec<Binder<Expr>>, body: &Expr) -> Expr {
    if binders.len() == 0 {
        body.clone()
    } else {
        Arc::new(ExprX::Bind(Arc::new(BindX::Let(Arc::new(binders.clone()))), body.clone()))
    }
}

pub fn mk_quantifier(
    quant: Quant,
    binders: &Vec<Binder<Typ>>,
    triggers: &Vec<Trigger>,
    qid: Qid,
    body: &Expr,
) -> Expr {
    if binders.len() == 0 {
        body.clone()
    } else {
        Arc::new(ExprX::Bind(
            Arc::new(BindX::Quant(
                quant,
                Arc::new(binders.clone()),
                Arc::new(triggers.clone()),
                qid,
            )),
            body.clone(),
        ))
    }
}

pub fn mk_forall(
    binders: &Vec<Binder<Typ>>,
    triggers: &Vec<Trigger>,
    qid: Qid,
    body: &Expr,
) -> Expr {
    mk_quantifier(Quant::Forall, binders, triggers, qid, body)
}

pub fn mk_exists(
    binders: &Vec<Binder<Typ>>,
    triggers: &Vec<Trigger>,
    qid: Qid,
    body: &Expr,
) -> Expr {
    mk_quantifier(Quant::Exists, binders, triggers, qid, body)
}

pub fn mk_lambda(
    binders: &Vec<Binder<Typ>>,
    triggers: &Vec<Trigger>,
    qid: Qid,
    body: &Expr,
) -> Expr {
    Arc::new(ExprX::Bind(
        Arc::new(BindX::Lambda(Arc::new(binders.clone()), Arc::new(triggers.clone()), qid)),
        body.clone(),
    ))
}

pub fn mk_true() -> Expr {
    Arc::new(ExprX::Const(Constant::Bool(true)))
}

pub fn mk_false() -> Expr {
    Arc::new(ExprX::Const(Constant::Bool(false)))
}

pub fn mk_and(exprs: &Vec<Expr>) -> Expr {
    if exprs.iter().any(|expr| matches!(**expr, ExprX::Const(Constant::Bool(false)))) {
        return mk_false();
    }
    let exprs: Vec<Expr> = exprs
        .iter()
        .filter(|expr| !matches!(***expr, ExprX::Const(Constant::Bool(true))))
        .cloned()
        .collect();
    if exprs.len() == 0 {
        mk_true()
    } else if exprs.len() == 1 {
        exprs[0].clone()
    } else {
        Arc::new(ExprX::Multi(MultiOp::And, Arc::new(exprs)))
    }
}

pub fn mk_or(exprs: &Vec<Expr>) -> Expr {
    if exprs.iter().any(|expr| matches!(**expr, ExprX::Const(Constant::Bool(true)))) {
        return mk_true();
    }
    let exprs: Vec<Expr> = exprs
        .iter()
        .filter(|expr| !matches!(***expr, ExprX::Const(Constant::Bool(false))))
        .cloned()
        .collect();
    if exprs.len() == 0 {
        mk_false()
    } else if exprs.len() == 1 {
        exprs[0].clone()
    } else {
        Arc::new(ExprX::Multi(MultiOp::Or, Arc::new(exprs)))
    }
}

pub fn mk_not(e1: &Expr) -> Expr {
    match &**e1 {
        ExprX::Const(Constant::Bool(false)) => mk_true(),
        ExprX::Const(Constant::Bool(true)) => mk_false(),
        ExprX::Unary(UnaryOp::Not, e) => e.clone(),
        _ => Arc::new(ExprX::Unary(UnaryOp::Not, e1.clone())),
    }
}

pub fn mk_implies(e1: &Expr, e2: &Expr) -> Expr {
    match (&**e1, &**e2) {
        (ExprX::Const(Constant::Bool(false)), _) => mk_true(),
        (ExprX::Const(Constant::Bool(true)), _) => e2.clone(),
        (_, ExprX::Const(Constant::Bool(false))) => mk_not(e1),
        (_, ExprX::Const(Constant::Bool(true))) => mk_true(),
        _ => Arc::new(ExprX::Binary(BinaryOp::Implies, e1.clone(), e2.clone())),
    }
}

pub fn mk_xor(e1: &Expr, e2: &Expr) -> Expr {
    match (&**e1, &**e2) {
        (ExprX::Const(Constant::Bool(false)), _) => e2.clone(),
        (ExprX::Const(Constant::Bool(true)), _) => mk_not(e2),
        (_, ExprX::Const(Constant::Bool(false))) => e1.clone(),
        (_, ExprX::Const(Constant::Bool(true))) => mk_not(e1),
        _ => Arc::new(ExprX::Multi(MultiOp::Xor, Arc::new(vec![e1.clone(), e2.clone()]))),
    }
}

pub fn mk_ite(e1: &Expr, e2: &Expr, e3: &Expr) -> Expr {
    match (&**e1, &**e2, &**e3) {
        (ExprX::Const(Constant::Bool(true)), _, _) => e2.clone(),
        (ExprX::Const(Constant::Bool(false)), _, _) => e3.clone(),
        (_, _, ExprX::Const(Constant::Bool(true))) => mk_implies(e1, e2),
        (_, _, ExprX::Const(Constant::Bool(false))) => mk_and(&vec![e1.clone(), e2.clone()]),
        (_, ExprX::Const(Constant::Bool(true)), _) => mk_implies(&mk_not(e1), e3),
        (_, ExprX::Const(Constant::Bool(false)), _) => mk_and(&vec![mk_not(e1), e3.clone()]),
        _ => Arc::new(ExprX::IfElse(e1.clone(), e2.clone(), e3.clone())),
    }
}

pub fn mk_eq(e1: &Expr, e2: &Expr) -> Expr {
    Arc::new(ExprX::Binary(BinaryOp::Eq, e1.clone(), e2.clone()))
}

pub fn mk_option_command(s1: &str, s2: &str) -> Command {
    Arc::new(CommandX::SetOption(Arc::new(String::from(s1)), Arc::new(String::from(s2))))
}

pub fn mk_bitvector_option(solver: &SmtSolver) -> Vec<Command> {
    match solver {
        SmtSolver::Z3 => vec![
            mk_option_command("sat.euf", "true"),
            mk_option_command("tactic.default_tactic", "sat"),
            mk_option_command("smt.ematching", "false"),
            mk_option_command("smt.case_split", "0"),
        ],
        SmtSolver::Cvc5 =>
        // TODO: What options are best for cvc5 here?
        {
            vec![]
        }
    }
}

pub fn mk_nat<S: ToString>(n: S) -> Expr {
    Arc::new(ExprX::Const(Constant::Nat(Arc::new(n.to_string()))))
}

pub fn mk_neg(e: &Expr) -> Expr {
    Arc::new(ExprX::Multi(MultiOp::Sub, Arc::new(vec![e.clone()])))
}

pub fn mk_sub(e1: &Expr, e2: &Expr) -> Expr {
    Arc::new(ExprX::Multi(MultiOp::Sub, Arc::new(vec![e1.clone(), e2.clone()])))
}

pub fn mk_unnamed_axiom(expr: Expr) -> Decl {
    Arc::new(DeclX::Axiom(Axiom { named: None, expr: expr.clone() }))
}
