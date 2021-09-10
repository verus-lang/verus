// A simple type checker for better diagnostics.
// (Z3 and the Z3 crate will also type-check, but their type errors are uninformative panics)

use crate::ast::{
    BinaryOp, BindX, Binder, BinderX, Binders, Constant, Decl, DeclX, Expr, ExprX, Ident, MultiOp,
    Query, Stmt, StmtX, Typ, TypX, TypeError, Typs, UnaryOp,
};
use crate::context::Context;
use crate::printer::{decl_to_node, expr_to_node, node_to_string, stmt_to_node};
use crate::scope_map::ScopeMap;
use crate::util::vec_map;
use std::collections::HashSet;
use std::sync::Arc;

#[derive(Clone)]
pub(crate) enum DeclaredX {
    Type,
    Var { typ: Typ, mutable: bool },
    Fun(Typs, Typ),
}
pub(crate) type Declared = Arc<DeclaredX>;

#[derive(Clone)]
pub(crate) struct Var {
    pub(crate) typ: Typ,
    pub(crate) mutable: bool,
}

#[derive(Clone)]
pub(crate) struct Fun {
    pub(crate) typs: Typs,
    pub(crate) typ: Typ,
}

pub struct Typing {
    // For simplicity, global and local names must be unique (bound variables can have the same name)
    pub(crate) decls: ScopeMap<Ident, Declared>,
    pub(crate) snapshots: HashSet<Ident>,
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
        TypX::Named(x) => x.to_string(),
    }
}

fn typ_eq(typ1: &Typ, typ2: &Typ) -> bool {
    match (&**typ1, &**typ2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int, TypX::Int) => true,
        (TypX::Named(x1), TypX::Named(x2)) => x1 == x2,
        _ => false,
    }
}

fn expect_typ(typ1: &Typ, typ2: &Typ, msg: &str) -> Result<(), TypeError> {
    if typ_eq(typ1, typ2) { Ok(()) } else { Err(msg.to_string()) }
}

pub(crate) fn check_typ(typing: &Typing, typ: &Typ) -> Result<(), TypeError> {
    match &**typ {
        TypX::Bool => Ok(()),
        TypX::Int => Ok(()),
        TypX::Named(x) => match typing.get(x) {
            Some(DeclaredX::Type) => Ok(()),
            _ => Err(format!("use of undeclared type {}", x)),
        },
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

pub(crate) fn check_expr(typing: &mut Typing, expr: &Expr) -> Result<Typ, TypeError> {
    let result = match &**expr {
        ExprX::Const(Constant::Bool(_)) => Ok(Arc::new(TypX::Bool)),
        ExprX::Const(Constant::Nat(_)) => Ok(Arc::new(TypX::Int)),
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
        ExprX::Unary(UnaryOp::Not, e1) => check_exprs(typing, "not", &[bt()], &bt(), &[e1.clone()]),
        ExprX::Binary(BinaryOp::Implies, e1, e2) => {
            check_exprs(typing, "=>", &[bt(), bt()], &bt(), &[e1.clone(), e2.clone()])
        }
        ExprX::Binary(BinaryOp::Eq, e1, e2) => {
            let t1 = check_expr(typing, e1)?;
            let t2 = check_expr(typing, e2)?;
            if typ_eq(&t1, &t2) {
                Ok(bt())
            } else {
                Err(format!(
                    "in equality, left expression has type {} and right expression has different type {}",
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
        ExprX::Multi(op, exprs) => {
            let (x, t) = match op {
                MultiOp::And => ("and", bt()),
                MultiOp::Or => ("or", bt()),
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
                BindX::Quant(_, binders, _) => binders.clone(),
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
                BindX::Quant(_, _, triggers) => {
                    for trigger in triggers.iter() {
                        for expr in trigger.iter() {
                            check_expr(typing, expr)?;
                        }
                    }
                }
            }
            // Type-check expr
            let t1 = check_expr(typing, e1)?;
            match &**bind {
                BindX::Let(_) => {}
                BindX::Quant(_, _, _) => {
                    expect_typ(&t1, &bt(), "forall/exists body must have type bool")?;
                }
            }
            // Done
            typing.decls.pop_scope();
            Ok(t1)
        }
        ExprX::LabeledAssertion(_, expr) => check_expr(typing, expr),
    };
    match result {
        Ok(t) => Ok(t),
        Err(err) => {
            let node_str = node_to_string(&expr_to_node(expr));
            Err(format!("error '{}' in expression '{}'", err, node_str))
        }
    }
}

pub(crate) fn check_stmt(typing: &mut Typing, stmt: &Stmt) -> Result<(), TypeError> {
    let result = match &**stmt {
        StmtX::Assume(expr) => expect_typ(
            &check_expr(typing, expr)?,
            &bt(),
            "assert statement expects expression of type bool",
        ),
        StmtX::Assert(_, expr) => expect_typ(
            &check_expr(typing, expr)?,
            &bt(),
            "assume statement expects expression of type bool",
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
        StmtX::Block(stmts) => {
            for s in stmts.iter() {
                check_stmt(typing, s)?;
            }
            Ok(())
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
            let node_str = node_to_string(&stmt_to_node(stmt));
            Err(format!("error '{}' in statement '{}'", err, node_str))
        }
    }
}

pub(crate) fn check_decl(typing: &mut Typing, decl: &Decl) -> Result<(), TypeError> {
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
        DeclX::Axiom(expr) => {
            expect_typ(&check_expr(typing, expr)?, &bt(), "axiom expects expression of type bool")
        }
    };
    match result {
        Ok(()) => Ok(()),
        Err(err) => {
            let node_str = node_to_string(&decl_to_node(decl));
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

pub(crate) fn check_query(context: &mut Context, query: &Query) -> Result<(), TypeError> {
    let num_scopes = context.typing.decls.num_scopes();
    context.push_name_scope();
    for decl in query.local.iter() {
        check_decl(&mut context.typing, decl)?;
        add_decl(context, decl, false)?;
    }
    check_stmt(&mut context.typing, &query.assertion)?;
    context.pop_name_scope();
    assert_eq!(context.typing.decls.num_scopes(), num_scopes);
    Ok(())
}
