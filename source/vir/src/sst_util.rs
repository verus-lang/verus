use crate::ast::{SpannedTyped, Typ, TypX};
use crate::def::{unique_bound, Spanned};
use crate::sst::{BndX, Exp, ExpX, Stm, Trig, Trigs, UniqueIdent};
use air::ast::{Binder, BinderX, Binders, Ident, Span};
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) fn free_vars_exp(exp: &Exp) -> HashMap<UniqueIdent, Typ> {
    free_vars_exp_scope(exp, &mut crate::sst_visitor::VisitorScopeMap::new())
}

fn free_vars_exp_scope(
    exp: &Exp,
    scope_map: &mut crate::sst_visitor::VisitorScopeMap,
) -> HashMap<UniqueIdent, Typ> {
    let mut vars: HashMap<UniqueIdent, Typ> = HashMap::new();
    crate::sst_visitor::exp_visitor_dfs::<(), _>(exp, scope_map, &mut |e, scope_map| {
        match &e.x {
            ExpX::Var(x) | ExpX::VarLoc(x) if !scope_map.contains_key(&x.name) => {
                vars.insert(x.clone(), e.typ.clone());
            }
            _ => (),
        }
        crate::sst_visitor::VisitorControlFlow::Recurse
    });
    vars
}

pub(crate) fn free_vars_stm(stm: &Stm) -> HashMap<UniqueIdent, Typ> {
    let mut vars: HashMap<UniqueIdent, Typ> = HashMap::new();
    crate::sst_visitor::stm_exp_visitor_dfs::<(), _>(stm, &mut |exp, scope_map| {
        vars.extend(free_vars_exp_scope(exp, scope_map).into_iter());
        crate::sst_visitor::VisitorControlFlow::Recurse
    });
    vars
}

fn subst_typ(typ_substs: &HashMap<Ident, Typ>, typ: &Typ) -> Typ {
    crate::ast_visitor::map_typ_visitor(typ, &|t: &Typ| match &**t {
        TypX::TypParam(x) => match typ_substs.get(x) {
            Some(t) => Ok(t.clone()),
            None => Ok(t.clone()),
        },
        _ => Ok(t.clone()),
    })
    .expect("subst_typ")
}

fn subst_rename_binders<A: Clone, FA: Fn(&A) -> A, FT: Fn(&A) -> Typ>(
    span: &Span,
    substs: &mut ScopeMap<UniqueIdent, Exp>,
    free_vars: &mut ScopeMap<UniqueIdent, ()>,
    bs: &Binders<A>,
    fa: FA,
    f_typ: FT,
) -> Binders<A> {
    substs.push_scope(false);
    free_vars.push_scope(false);
    let mut binders: Vec<Binder<A>> = Vec::new();
    for b in bs.iter() {
        let unique = unique_bound(&b.name);
        let name = if free_vars.contains_key(&unique) {
            // capture-avoiding substitution:
            // rename bound variable to avoid capturing free variable
            let mut n: u64 = 0;
            loop {
                let name = crate::def::subst_rename_ident(&b.name, n);
                let rename = unique_bound(&name);
                if !free_vars.contains_key(&rename) {
                    free_vars.insert(rename.clone(), ()).expect("subst_rename_binders free_vars");
                    let typ = f_typ(&b.a);
                    let var = SpannedTyped::new(span, &typ, ExpX::Var(rename.clone()));
                    substs.insert(unique, var).expect("subst_rename_binders substs");
                    break name;
                }
                n += 1;
            }
        } else {
            b.name.clone()
        };
        binders.push(Arc::new(BinderX { name, a: fa(&b.a) }));
    }
    Arc::new(binders)
}

fn subst_exp_rec(
    typ_substs: &HashMap<Ident, Typ>,
    substs: &mut ScopeMap<UniqueIdent, Exp>,
    free_vars: &mut ScopeMap<UniqueIdent, ()>,
    exp: &Exp,
) -> Exp {
    let typ = subst_typ(typ_substs, &exp.typ);
    let mk_exp = |e: ExpX| SpannedTyped::new(&exp.span, &typ, e);
    let ft = |t: &Typ| subst_typ(typ_substs, t);
    match &exp.x {
        ExpX::Const(..)
        | ExpX::Loc(..)
        | ExpX::Old(..)
        | ExpX::Call(..)
        | ExpX::CallLambda(..)
        | ExpX::Ctor(..)
        | ExpX::Unary(..)
        | ExpX::UnaryOpr(..)
        | ExpX::Binary(..)
        | ExpX::If(..)
        | ExpX::WithTriggers(..) => crate::sst_visitor::map_shallow_exp(
            exp,
            &mut (substs, free_vars),
            &|_, t| Ok(subst_typ(typ_substs, t)),
            &|(substs, free_vars), e| Ok(subst_exp_rec(typ_substs, substs, free_vars, e)),
        )
        .expect("map_shallow_exp for subst_exp_rec"),
        ExpX::Var(x) | ExpX::VarLoc(x) => match substs.get(x) {
            None => mk_exp(ExpX::Var(x.clone())),
            Some(e) => e.clone(),
        },
        ExpX::VarAt(x, a) => match substs.get(x) {
            None => mk_exp(ExpX::VarAt(x.clone(), *a)),
            Some(_) => panic!("cannot substitute for VarAt"),
        },
        ExpX::Bind(bnd, e1) => {
            let ftrigs = |substs: &mut ScopeMap<UniqueIdent, Exp>,
                          free_vars: &mut ScopeMap<UniqueIdent, ()>,
                          triggers: &Trigs|
             -> Trigs {
                let mut trigs: Vec<Trig> = Vec::new();
                for trigger in triggers.iter() {
                    let mut trig: Vec<Exp> = Vec::new();
                    for t in trigger.iter() {
                        trig.push(subst_exp_rec(typ_substs, substs, free_vars, t));
                    }
                    trigs.push(Arc::new(trig));
                }
                Arc::new(trigs)
            };
            let bndx = match &bnd.x {
                BndX::Let(bs) => {
                    let mut binders: Vec<Binder<Exp>> = Vec::new();
                    for b in bs.iter() {
                        binders.push(b.new_a(subst_exp_rec(typ_substs, substs, free_vars, &b.a)));
                    }
                    let binders = subst_rename_binders(
                        &bnd.span,
                        substs,
                        free_vars,
                        &Arc::new(binders),
                        |e: &Exp| e.clone(),
                        |e: &Exp| e.typ.clone(),
                    );
                    BndX::Let(binders)
                }
                BndX::Quant(quant, binders, ts) => {
                    let binders =
                        subst_rename_binders(&bnd.span, substs, free_vars, binders, ft, ft);
                    BndX::Quant(*quant, binders, ftrigs(substs, free_vars, ts))
                }
                BndX::Lambda(binders) => {
                    let binders =
                        subst_rename_binders(&bnd.span, substs, free_vars, binders, ft, ft);
                    BndX::Lambda(binders)
                }
                BndX::Choose(binders, ts, cond) => {
                    let binders =
                        subst_rename_binders(&bnd.span, substs, free_vars, binders, ft, ft);
                    let cond = subst_exp_rec(typ_substs, substs, free_vars, cond);
                    BndX::Choose(binders, ftrigs(substs, free_vars, ts), cond)
                }
            };
            let bnd = Spanned::new(bnd.span.clone(), bndx);
            let e1 = subst_exp_rec(typ_substs, substs, free_vars, e1);
            substs.pop_scope();
            free_vars.pop_scope();
            SpannedTyped::new(&exp.span, &typ, ExpX::Bind(bnd, e1))
        }
    }
}

pub(crate) fn subst_exp(
    typ_substs: HashMap<Ident, Typ>,
    substs: HashMap<UniqueIdent, Exp>,
    exp: &Exp,
) -> Exp {
    let mut scope_substs: ScopeMap<UniqueIdent, Exp> = ScopeMap::new();
    let mut free_vars: ScopeMap<UniqueIdent, ()> = ScopeMap::new();
    scope_substs.push_scope(false);
    free_vars.push_scope(false);
    for (x, v) in &substs {
        scope_substs.insert(x.clone(), v.clone()).expect("subst_exp scope_substs.insert");
        for (y, _) in free_vars_exp(v) {
            let _ = free_vars.insert(y.clone(), ());
        }
    }
    let e = subst_exp_rec(&typ_substs, &mut scope_substs, &mut free_vars, exp);
    scope_substs.pop_scope();
    free_vars.pop_scope();
    assert_eq!(scope_substs.num_scopes(), 0);
    assert_eq!(free_vars.num_scopes(), 0);
    e
}
