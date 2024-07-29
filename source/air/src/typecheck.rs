// A simple type checker for better diagnostics.
// (Z3 and the Z3 crate will also type-check, but their type errors are uninformative panics)

use crate::ast::{
    Axiom, BinaryOp, BindX, Binder, BinderX, Binders, Constant, Decl, DeclX, Expr, ExprX, Ident,
    MultiOp, Query, QueryX, Stmt, StmtX, Typ, TypX, TypeError, Typs, UnaryOp,
};
use crate::context::{Context, SmtSolver};
use crate::messages::MessageInterface;
use crate::printer::{node_to_string, Printer};
use crate::scope_map::ScopeMap;
use crate::util::vec_map;
use std::collections::HashSet;
use std::sync::Arc;

pub(crate) type Declared = Arc<DeclaredX>;
#[derive(Clone)]
pub(crate) enum DeclaredX {
    Type,
    Var { typ: Typ, mutable: bool },
    Fun(Typs, Typ),
}

pub struct Typing {
    pub(crate) message_interface: Arc<dyn MessageInterface>,
    // For simplicity, global and local names must be unique (bound variables can have the same name)
    pub(crate) decls: ScopeMap<Ident, Declared>,
    pub(crate) snapshots: HashSet<Ident>,
    pub(crate) break_labels_local: HashSet<Ident>,
    pub(crate) break_labels_in_scope: ScopeMap<Ident, ()>,
    pub(crate) solver: SmtSolver,
}

impl Typing {
    pub(crate) fn get(&self, x: &Ident) -> Option<&DeclaredX> {
        match self.decls.get(x) {
            None => None,
            Some(declared) => Some(&**declared),
        }
    }

    pub(crate) fn insert(&mut self, x: &Ident, d: Declared) -> Result<(), TypeError> {
        self.decls.insert(x.clone(), d).map_err(|_| format!("name {} is already in scope", x))
    }
}

pub fn bt() -> Typ {
    Arc::new(TypX::Bool)
}

pub fn it() -> Typ {
    Arc::new(TypX::Int)
}

fn typ_name(typ: &Typ) -> String {
    match &**typ {
        TypX::Bool => "Bool".to_string(),
        TypX::Int => "Int".to_string(),
        TypX::Fun => "Fun".to_string(),
        TypX::Named(x) => x.to_string(),
        TypX::BitVec(n) => format!("BitVec{}", n),
    }
}

pub fn typ_eq(typ1: &Typ, typ2: &Typ) -> bool {
    typ1 == typ2
}

fn expect_typ(typ1: &Typ, typ2: &Typ, msg: &str) -> Result<(), TypeError> {
    if typ_eq(typ1, typ2) { Ok(()) } else { Err(msg.to_string()) }
}

fn check_typ(typing: &Typing, typ: &Typ) -> Result<(), TypeError> {
    match &**typ {
        TypX::Bool => Ok(()),
        TypX::Int => Ok(()),
        TypX::Fun => Ok(()),
        TypX::Named(x) => match typing.get(x) {
            Some(DeclaredX::Type) => Ok(()),
            _ => Err(format!("use of undeclared type {}", x)),
        },
        TypX::BitVec(_) => Ok(()),
    }
}

fn check_typs(typing: &Typing, typs: &[Typ]) -> Result<(), TypeError> {
    for typ in typs {
        let result = check_typ(typing, typ);
        if let Err(_) = result {
            return result;
        }
    }
    Ok(())
}

fn check_exprs(
    typing: &mut Typing,
    f_name: &str,
    f_typs: &[Typ],
    f_typ: &Typ,
    exprs: &[Expr],
) -> Result<Typ, TypeError> {
    if f_typs.len() != exprs.len() {
        return Err(format!(
            "in call to {}, expected {} arguments, found {} arguments",
            f_name,
            f_typs.len(),
            exprs.len()
        ));
    }
    for i in 0..f_typs.len() {
        let et = check_expr(typing, &exprs[i])?;
        if !typ_eq(&et, &f_typs[i]) {
            return Err(format!(
                "in call to {}, argument #{} has type {:?} when it should have type {:?}",
                f_name,
                (i + 1),
                typ_name(&et),
                typ_name(&f_typs[i])
            ));
        }
    }
    Ok(f_typ.clone())
}

fn get_bv_width(et: &Typ) -> Result<u32, TypeError> {
    if let TypX::BitVec(size) = &**et {
        return Ok(*size);
    }
    Err("not a bit vector type".to_string())
}

fn check_bv_unary_exprs(
    typing: &mut Typing,
    op: UnaryOp,
    f_name: &str,
    expr: &Expr,
) -> Result<Typ, TypeError> {
    match op {
        UnaryOp::BitExtract(high, lo) => {
            let t0 = check_expr(typing, expr)?;
            let w_old = get_bv_width(&t0)?;
            if w_old < high + 1 {
                Err(format!(
                    "Interner Error: bit-vec extract to a longer size. {} to {} ",
                    w_old, high
                ))
            } else if lo > high {
                Err(format!("Interner Error: bit-vec extract has lo > high. {} to {} ", lo, high))
            } else {
                Ok(Arc::new(TypX::BitVec(high + 1 - lo)))
            }
        }
        UnaryOp::BitNot => {
            let t0 = check_expr(typing, expr)?;
            match get_bv_width(&t0) {
                Ok(_) => Ok(t0.clone()),
                Err(..) => Err("Interner Error: not a bv type inside a bvnot".to_string()),
            }
        }
        UnaryOp::BitZeroExtend(n) | UnaryOp::BitSignExtend(n) => {
            let t0 = check_expr(typing, expr)?;
            match get_bv_width(&t0) {
                Ok(m) => Ok(Arc::new(TypX::BitVec(n + m))),
                Err(..) => Err(format!("Interner Error: not a bv type inside a {}", f_name)),
            }
        }
        _ => Err(format!("Interner Error: not a bv unary op, got {}", f_name)),
    }
}

fn check_bv_exprs(
    typing: &mut Typing,
    bop: BinaryOp,
    f_name: &str,
    exprs: &[Expr],
) -> Result<Typ, TypeError> {
    let t0 = check_expr(typing, &exprs[0])?;
    let t1 = check_expr(typing, &exprs[1])?;
    let w0 = get_bv_width(&t0)?;
    let w1 = get_bv_width(&t1)?;

    if BinaryOp::BitConcat == bop {
        return Ok(Arc::new(TypX::BitVec(w0 + w1)));
    }

    if w0 != w1 {
        return Err(format!(
            "in call to {}, arguments should have the same width, but got {} and {}",
            f_name, w0, w1
        ));
    }

    // return bool type if it is comparision op
    match bop {
        BinaryOp::BitUGe | BinaryOp::BitULe | BinaryOp::BitUGt | BinaryOp::BitULt => Ok(bt()),
        BinaryOp::BitSGe | BinaryOp::BitSLe | BinaryOp::BitSGt | BinaryOp::BitSLt => Ok(bt()),
        _ => Ok(t0.clone()),
    }
}

fn check_expr(typing: &mut Typing, expr: &Expr) -> Result<Typ, TypeError> {
    let result = match &**expr {
        ExprX::Const(Constant::Bool(_)) => Ok(Arc::new(TypX::Bool)),
        ExprX::Const(Constant::Nat(_)) => Ok(Arc::new(TypX::Int)),
        ExprX::Const(Constant::BitVec(_, width)) => Ok(Arc::new(TypX::BitVec(*width))),
        ExprX::Var(x) => match typing.get(x) {
            Some(DeclaredX::Var { typ, .. }) => Ok(typ.clone()),
            _ => Err(format!("use of undeclared variable {}", x)),
        },
        ExprX::Old(snap, x) => match (typing.snapshots.contains(snap), typing.get(x)) {
            (false, _) => Err(format!("use of undeclared snapshot {}", snap)),
            (true, Some(DeclaredX::Var { typ, .. })) => Ok(typ.clone()),
            (true, _) => Err(format!("use of undeclared variable {}", x)),
        },
        ExprX::Apply(x, es) => match typing.get(x).cloned() {
            Some(DeclaredX::Fun(f_typs, f_typ)) => check_exprs(typing, x, &f_typs, &f_typ, es),
            _ => Err(format!("use of undeclared function {}", x)),
        },
        ExprX::ApplyFun(t, e0, es) => {
            let t0 = check_expr(typing, e0)?;
            match &*t0 {
                TypX::Fun => {
                    for e in es.iter() {
                        check_expr(typing, e)?;
                    }
                    Ok(t.clone())
                }
                _ => Err("expected function type".to_string()),
            }
        }
        ExprX::Unary(UnaryOp::Not, e1) => check_exprs(typing, "not", &[bt()], &bt(), &[e1.clone()]),
        ExprX::Unary(UnaryOp::BitNot, e1) => {
            check_bv_unary_exprs(typing, UnaryOp::BitNot, "bvnot", &e1.clone())
        }
        ExprX::Unary(UnaryOp::BitExtract(high, low), e1) => {
            check_bv_unary_exprs(typing, UnaryOp::BitExtract(*high, *low), "extract", &e1.clone())
        }
        ExprX::Unary(UnaryOp::BitZeroExtend(n), e1) => {
            check_bv_unary_exprs(typing, UnaryOp::BitZeroExtend(*n), "zero_extend", &e1.clone())
        }
        ExprX::Unary(UnaryOp::BitSignExtend(n), e1) => {
            check_bv_unary_exprs(typing, UnaryOp::BitSignExtend(*n), "sign_extend", &e1.clone())
        }
        ExprX::Binary(BinaryOp::Implies, e1, e2) => {
            check_exprs(typing, "=>", &[bt(), bt()], &bt(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(op @ (BinaryOp::Eq | BinaryOp::Relation(..)), e1, e2) => {
            let t1 = check_expr(typing, e1)?;
            let t2 = check_expr(typing, e2)?;
            if typ_eq(&t1, &t2) {
                Ok(bt())
            } else {
                Err(format!(
                    "in {}, left expression has type {} and right expression has different type {}",
                    match op {
                        BinaryOp::Eq => "equality",
                        _ => "relation",
                    },
                    typ_name(&t1),
                    typ_name(&t2)
                ))
            }
        }
        ExprX::Binary(BinaryOp::Le, e1, e2) => {
            check_exprs(typing, "<=", &[it(), it()], &bt(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::Ge, e1, e2) => {
            check_exprs(typing, ">=", &[it(), it()], &bt(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::Lt, e1, e2) => {
            check_exprs(typing, "<", &[it(), it()], &bt(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::Gt, e1, e2) => {
            check_exprs(typing, ">", &[it(), it()], &bt(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::EuclideanDiv, e1, e2) => {
            check_exprs(typing, "div", &[it(), it()], &it(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::EuclideanMod, e1, e2) => {
            check_exprs(typing, "mod", &[it(), it()], &it(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitULt, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitULt, "bvlt", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitUGt, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitUGt, "bvgt", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitULe, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitULe, "bvle", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitUGe, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitUGe, "bvge", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitSLt, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitSLt, "bvslt", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitSGt, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitSGt, "bvsgt", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitSLe, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitSLe, "bvsle", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitSGe, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitSGe, "bvsge", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitXor, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitXor, "^", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitUMod, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitUMod, "bvmod", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitAnd, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitAnd, "&", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitOr, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitOr, "|", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitAdd, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitAdd, "bvadd", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitSub, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitSub, "bvsub", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitMul, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitMul, "bvmul", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitUDiv, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitUDiv, "bvdiv", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::LShr, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::LShr, ">> (lshr)", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::AShr, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::AShr, ">> (ashr)", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::Shl, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::Shl, "<<", &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::BitConcat, e1, e2) => {
            check_bv_exprs(typing, BinaryOp::BitConcat, "concat", &[e1.clone(), e2.clone()])
        }

        ExprX::Multi(op, exprs) => {
            let (x, t) = match op {
                MultiOp::And => ("and", bt()),
                MultiOp::Or => ("or", bt()),
                MultiOp::Xor => ("xor", bt()),
                MultiOp::Add => ("+", it()),
                MultiOp::Sub => ("-", it()),
                MultiOp::Mul => ("*", it()),
                MultiOp::Distinct => ("distinct", it()),
            };
            let f_typs = vec_map(exprs, |_| t.clone());
            match op {
                MultiOp::Distinct => {
                    if exprs.len() > 0 {
                        let t0 = check_expr(typing, &exprs[0])?;
                        for e in &exprs[1..] {
                            let tk = check_expr(typing, e)?;
                            expect_typ(&tk, &t0, "arguments to distinct must all have same type")?;
                        }
                    }
                    Ok(bt())
                }
                _ => check_exprs(typing, x, &f_typs, &t, exprs),
            }
        }
        ExprX::IfElse(e1, e2, e3) => {
            let t1 = check_expr(typing, e1)?;
            let t2 = check_expr(typing, e2)?;
            let t3 = check_expr(typing, e3)?;
            if !typ_eq(&t1, &bt()) {
                Err(format!(
                    "in if/then/else, condition has type {} instead of Bool",
                    typ_name(&t1)
                ))
            } else if !typ_eq(&t2, &t3) {
                Err(format!(
                    "in if/then/else, left expression has type {} and right expression has different type {}",
                    typ_name(&t2),
                    typ_name(&t3)
                ))
            } else {
                Ok(t2)
            }
        }
        ExprX::Array(exprs) => {
            if exprs.len() > 0 {
                let t0 = check_expr(typing, &exprs[0])?;
                for e in &exprs[1..] {
                    let tk = check_expr(typing, e)?;
                    expect_typ(&tk, &t0, "arguments to array must all have same type")?;
                }
            }
            Ok(Arc::new(TypX::Fun))
        }
        ExprX::Bind(bind, e1) => {
            // For Let, get types of binder expressions
            let binders: Binders<Typ> = match &**bind {
                BindX::Let(bs) => {
                    let mut binders: Vec<Binder<Typ>> = Vec::new();
                    for b in bs.iter() {
                        let typ = check_expr(typing, &b.a)?;
                        binders.push(Arc::new(BinderX { name: b.name.clone(), a: typ }));
                    }
                    Arc::new(binders)
                }
                BindX::Quant(_, binders, _, _) => binders.clone(),
                BindX::Lambda(binders, _, _) => binders.clone(),
                BindX::Choose(binders, _, _, _) => binders.clone(),
            };
            // Collect all binder names, make sure they are unique
            typing.decls.push_scope(true);
            for binder in binders.iter() {
                let x = &binder.name;
                let var = DeclaredX::Var { typ: binder.a.clone(), mutable: false };
                typing.insert(x, Arc::new(var))?;
            }
            // Type-check triggers
            match &**bind {
                BindX::Let(_) => {}
                BindX::Quant(_, _, triggers, _)
                | BindX::Choose(_, triggers, _, _)
                | BindX::Lambda(_, triggers, _) => {
                    for trigger in triggers.iter() {
                        for expr in trigger.iter() {
                            check_expr(typing, expr)?;
                        }
                    }
                }
            }
            // Type-check inner expressions
            if let BindX::Choose(_, _, _, e2) = &**bind {
                let t2 = check_expr(typing, e2)?;
                if !typ_eq(&t2, &bt()) {
                    return Err(format!(
                        "in choose, condition has type {} instead of Bool",
                        typ_name(&t2)
                    ));
                }
            }
            // Type-check expr
            let t1 = check_expr(typing, e1)?;
            let tb = match &**bind {
                BindX::Let(_) => t1,
                BindX::Quant(_, _, _, _) => {
                    expect_typ(&t1, &bt(), "forall/exists body must have type bool")?;
                    t1
                }
                BindX::Lambda(_, _, _) => Arc::new(TypX::Fun),
                BindX::Choose(..) => t1,
            };
            // Done
            typing.decls.pop_scope();
            Ok(tb)
        }
        ExprX::LabeledAssertion(_, _, _, expr) => check_expr(typing, expr),
        ExprX::LabeledAxiom(_, _, expr) => check_expr(typing, expr),
    };
    match result {
        Ok(t) => Ok(t),
        Err(err) => {
            let node_str = node_to_string(
                &Printer::new(typing.message_interface.clone(), false, typing.solver.clone())
                    .expr_to_node(expr),
            );
            Err(format!("error '{}' in expression '{}'", err, node_str))
        }
    }
}

fn check_stmt(typing: &mut Typing, stmt: &Stmt) -> Result<(), TypeError> {
    let result = match &**stmt {
        StmtX::Assume(expr) => expect_typ(
            &check_expr(typing, expr)?,
            &bt(),
            "assume statement expects expression of type bool",
        ),
        StmtX::Assert(_, _, _, expr) => expect_typ(
            &check_expr(typing, expr)?,
            &bt(),
            "assert statement expects expression of type bool",
        ),
        StmtX::Havoc(x) => match typing.get(x).cloned() {
            Some(DeclaredX::Var { mutable, .. }) => {
                if !mutable {
                    Err(format!("cannot assign to const variable {}", x))
                } else {
                    Ok(())
                }
            }
            _ => Err(format!("assignment to undeclared variable {}", x)),
        },
        StmtX::Assign(x, expr) => match typing.get(x).cloned() {
            Some(DeclaredX::Var { typ, mutable }) => {
                if !mutable {
                    Err(format!("cannot assign to const variable {}", x))
                } else {
                    let t_expr = check_expr(typing, expr)?;
                    if !typ_eq(&t_expr, &typ) {
                        Err(format!(
                            "in assignment, {} has type {}, while expression has type {}",
                            x,
                            typ_name(&typ),
                            typ_name(&t_expr)
                        ))
                    } else {
                        Ok(())
                    }
                }
            }
            _ => Err(format!("assignment to undeclared variable {}", x)),
        },
        StmtX::Snapshot(snap) => {
            typing.snapshots.insert(snap.clone());
            Ok(())
        }
        StmtX::DeadEnd(s) => check_stmt(typing, s),
        StmtX::Block(stmts) => {
            for s in stmts.iter() {
                check_stmt(typing, s)?;
            }
            Ok(())
        }
        StmtX::Breakable(label, s) => {
            if typing.break_labels_local.contains(label) {
                Err(format!("break label '{label}' declared more than once in same query"))
            } else {
                typing.break_labels_local.insert(label.clone());
                typing.break_labels_in_scope.push_scope(false);
                typing.break_labels_in_scope.insert(label.clone(), ()).expect("push break");
                check_stmt(typing, s)?;
                typing.break_labels_in_scope.pop_scope();
                Ok(())
            }
        }
        StmtX::Break(label) => {
            if typing.break_labels_in_scope.contains_key(label) {
                Ok(())
            } else {
                Err(format!("break label '{label}' not in scope"))
            }
        }
        StmtX::Switch(stmts) => {
            let snapshots = typing.snapshots.clone(); // snapshots from branches are not retained
            for s in stmts.iter() {
                check_stmt(typing, s)?;
                typing.snapshots = snapshots.clone(); // reset to pre-branch snapshots
            }
            Ok(())
        }
    };
    match result {
        Ok(()) => Ok(()),
        Err(err) => {
            let node_str = node_to_string(
                &Printer::new(typing.message_interface.clone(), false, typing.solver.clone())
                    .stmt_to_node(stmt),
            );
            Err(format!("error '{}' in statement '{}'", err, node_str))
        }
    }
}

pub(crate) fn check_decl(
    context: &mut Context,
    decl: &Decl,
) -> Result<(Vec<Decl>, Decl), TypeError> {
    let typing = &mut context.typing;
    let result = match &**decl {
        DeclX::Sort(_) => Ok(()),
        DeclX::Datatypes(_) => Ok(()), // it's easier to do the checking in add_decl
        DeclX::Const(_, typ) => check_typ(typing, typ),
        DeclX::Fun(_, typs, typ) => {
            let mut typs_vec = typs.to_vec();
            typs_vec.push(typ.clone());
            check_typs(typing, &typs_vec)
        }
        DeclX::Var(_, typ) => check_typ(typing, typ),
        DeclX::Axiom(Axiom { named: _, expr }) => {
            expect_typ(&check_expr(typing, expr)?, &bt(), "axiom expects expression of type bool")
        }
    };
    match result {
        Ok(()) => Ok(crate::closure::simplify_decl(context, decl)),
        Err(err) => {
            let node_str = node_to_string(
                &Printer::new(context.message_interface.clone(), false, context.solver.clone())
                    .decl_to_node(decl),
            );
            Err(format!("error '{}' in declaration '{}'", err, node_str))
        }
    }
}

pub(crate) fn add_decl<'ctx>(
    context: &mut Context,
    decl: &Decl,
    is_global: bool,
) -> Result<(), TypeError> {
    let num_scopes = context.typing.decls.num_scopes();
    match &**decl {
        DeclX::Sort(x) => {
            context.typing.insert(x, Arc::new(DeclaredX::Type))?;
        }
        DeclX::Datatypes(datatypes) => {
            for datatype in datatypes.iter() {
                context.typing.insert(&datatype.name, Arc::new(DeclaredX::Type))?;
            }
            for datatype in datatypes.iter() {
                for variant in datatype.a.iter() {
                    let typ = Arc::new(TypX::Named(datatype.name.clone()));
                    let typs = vec_map(&variant.a, |field| field.a.clone());
                    let fun = DeclaredX::Fun(Arc::new(typs), typ.clone());
                    context.typing.insert(&variant.name, Arc::new(fun))?;
                    let is_variant = Arc::new("is-".to_string() + &variant.name.to_string());
                    let fun = DeclaredX::Fun(Arc::new(vec![typ.clone()]), bt());
                    context.typing.insert(&is_variant, Arc::new(fun))?;
                    for field in variant.a.iter() {
                        check_typ(&context.typing, &field.a)?;
                        let typs: Typs = Arc::new(vec![typ.clone()]);
                        let fun = DeclaredX::Fun(typs, field.a.clone());
                        context.typing.insert(&field.name, Arc::new(fun))?;
                    }
                }
            }
        }
        DeclX::Const(x, typ) => {
            let var = Arc::new(DeclaredX::Var { typ: typ.clone(), mutable: false });
            context.typing.insert(x, var)?;
        }
        DeclX::Fun(x, typs, typ) => {
            let fun = DeclaredX::Fun(typs.clone(), typ.clone());
            context.typing.insert(x, Arc::new(fun))?;
        }
        DeclX::Var(x, typ) => {
            if is_global {
                return Err(format!("declare-var {} not allowed in global scope", x));
            }
            let var = Arc::new(DeclaredX::Var { typ: typ.clone(), mutable: true });
            context.typing.insert(x, var)?;
        }
        DeclX::Axiom(_) => {}
    }
    assert_eq!(context.typing.decls.num_scopes(), num_scopes);
    Ok(())
}

pub(crate) fn check_query(context: &mut Context, query: &Query) -> Result<Query, TypeError> {
    let num_scopes = context.typing.decls.num_scopes();
    context.push_name_scope();
    let mut locals: Vec<Decl> = Vec::new();
    for decl in query.local.iter() {
        let (mut gen_decls, decl) = check_decl(context, decl)?;
        add_decl(context, &decl, false)?;
        locals.append(&mut gen_decls);
        locals.push(decl);
    }
    context.typing.snapshots = HashSet::new();
    context.typing.break_labels_local = HashSet::new();
    check_stmt(&mut context.typing, &query.assertion)?;

    // Call crate::closure to rewrite query
    assert_eq!(context.apply_map.num_scopes(), context.typing.decls.num_scopes());
    let (mut gen_decls, assertion) = crate::closure::simplify_stmt(context, &query.assertion);
    assert_eq!(context.apply_map.num_scopes(), context.typing.decls.num_scopes());
    locals.append(&mut gen_decls);
    let query = Arc::new(QueryX { local: Arc::new(locals), assertion });

    context.pop_name_scope();
    assert_eq!(context.typing.decls.num_scopes(), num_scopes);
    Ok(query)
}
