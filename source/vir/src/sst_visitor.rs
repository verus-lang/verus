use crate::ast::{
    BinaryOpr, GenericBound, GenericBoundX, NullaryOpr, SpannedTyped, Typ, UnaryOpr, VarBinder,
    VarIdent, VirErr,
};
use crate::def::Spanned;
use crate::sst::{
    Bnd, BndX, Dest, Exp, ExpX, FuncAxiomsSst, FuncCheckSst, FuncDeclSst, FuncSpecBodySst,
    FunctionSst, FunctionSstX, LocalDecl, LocalDeclX, LoopInv, Par, ParX, PostConditionSst, Stm,
    StmX, Trigs, UniqueIdent, UnwindSst,
};
pub(crate) use crate::visitor::{Returner, Rewrite, VisitorControlFlow, Walk};
use air::ast::Binder;
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) trait Scoper {
    fn push_scope(&mut self) {}
    fn pop_scope(&mut self) {}
    fn insert_binding_typ(&mut self, _binder: &VarBinder<Typ>, _bnd_source: &Bnd) {}
    fn insert_binding_exp(&mut self, _binder: &VarBinder<Exp>, _bnd_source: &Bnd) {}
}

pub(crate) struct NoScoper;
impl Scoper for NoScoper {}

pub type VisitorScopeMap = ScopeMap<VarIdent, bool>;

impl Scoper for ScopeMap<VarIdent, bool> {
    fn push_scope(&mut self) {
        self.push_scope(true);
    }

    fn pop_scope(&mut self) {
        self.pop_scope();
    }

    fn insert_binding_typ(&mut self, binder: &VarBinder<Typ>, bnd_source: &Bnd) {
        let is_triggered = match bnd_source.x {
            BndX::Quant(..) | BndX::Choose(..) => true,
            BndX::Lambda(..) => false,
            BndX::Let(..) => unreachable!(),
        };
        let _ = self.insert(binder.name.clone(), is_triggered);
    }

    fn insert_binding_exp(&mut self, binder: &VarBinder<Exp>, bnd_source: &Bnd) {
        assert!(matches!(bnd_source.x, BndX::Let(..)));
        let _ = self.insert(binder.name.clone(), true);
    }
}

/*
The central general-purpose SST visitor trait is `vir::sst_visitor::Visitor`.
A specific visitor specializes `Visitor` by providing the following:
- An error type `Err` that is returned when a visit exits early
- A normal return type, specified by instantiating `R: Returner`
  with either `R = Walk` or `R = Rewrite`:
  - `Walk` defines the return type `R::Ret<A> = ()`, so that `visit_typ`, `visit_exp`,
    and `visit_stm` return type `()`.
  - `Rewrite` defines the return type `R::Ret<A> = A`, so that `visit_typ` returns `Typ`,
    `visit_exp` returns `Exp`, and `visit_stm` returns `Stm`.
- An optional scoped variable tracker specified by type `Scope` and data supplied by `scoper`.
  This could be anything, but the current visitors either use `Scope = NoScoper`
  or `Scope = VisitorScopeMap`.
- Overridden `visit_typ`, `visit_exp`, and `visit_stm` methods.
  (For convenience, these have no-op default implementations,
  so if you don't override these you get a visitor that returns immediately without recursing.)

The `visit_typ`, `visit_exp`, and `visit_stm` methods could do anything they want, but typically
at least one of them will call the built-in recursive traversal methods provided by `visit_exp_rec`
and `visit_stm_rec`.  These built-in recursive traversal methods recursively call back into the
user-supplied `visit_typ`, `visit_exp`, and `visit_stm`.
Typically, the user-supplied `visit_typ`, `visit_exp`, and `visit_stm`
will do some preprocessing before recursing, and/or postprocessing after recursing,
and/or filtering to decide whether to recurse or not.
*/
pub(crate) trait Visitor<R: Returner, Err, Scope: Scoper> {
    // These methods are often overridden to make a specific sort of visit

    fn visit_typ(&mut self, typ: &Typ) -> Result<R::Ret<Typ>, Err> {
        R::ret(|| typ.clone())
    }

    fn visit_exp(&mut self, exp: &Exp) -> Result<R::Ret<Exp>, Err> {
        R::ret(|| exp.clone())
    }

    fn visit_stm(&mut self, stm: &Stm) -> Result<R::Ret<Stm>, Err> {
        R::ret(|| stm.clone())
    }

    fn scoper(&mut self) -> Option<&mut Scope> {
        None
    }

    // These methods are usually left unchanged

    fn push_scope(&mut self) {
        if let Some(scoper) = self.scoper() {
            scoper.push_scope();
        }
    }

    fn pop_scope(&mut self) {
        if let Some(scoper) = self.scoper() {
            scoper.pop_scope();
        }
    }

    fn insert_binding_typ(&mut self, binder: &VarBinder<Typ>, bnd_source: &Bnd) {
        if let Some(scoper) = self.scoper() {
            scoper.insert_binding_typ(binder, bnd_source);
        }
    }

    fn insert_binding_exp(&mut self, binder: &VarBinder<Exp>, bnd_source: &Bnd) {
        if let Some(scoper) = self.scoper() {
            scoper.insert_binding_exp(binder, bnd_source);
        }
    }

    fn visit_typs(&mut self, typs: &Vec<Typ>) -> Result<R::Vec<Typ>, Err> {
        R::map_vec(typs, &mut |t| self.visit_typ(t))
    }

    fn visit_exps(&mut self, exps: &Vec<Exp>) -> Result<R::Vec<Exp>, Err> {
        R::map_vec(exps, &mut |e| self.visit_exp(e))
    }

    fn visit_stms(&mut self, stms: &Vec<Stm>) -> Result<R::Vec<Stm>, Err> {
        R::map_vec(stms, &mut |s| self.visit_stm(s))
    }

    fn visit_triggers(&mut self, trigs: &Trigs) -> Result<R::Ret<Trigs>, Err> {
        let mut triggers = R::vec();
        for trigger in trigs.iter() {
            let trigger = self.visit_exps(trigger)?;
            R::push(&mut triggers, R::ret(|| R::get_vec_a(trigger))?);
        }
        R::ret(|| R::get_vec_a(triggers))
    }

    fn visit_binder_exp(&mut self, binder: &Binder<Exp>) -> Result<R::Ret<Binder<Exp>>, Err> {
        let a = self.visit_exp(&binder.a)?;
        R::ret(|| binder.new_a(R::get(a)))
    }

    fn visit_var_binder_typ(
        &mut self,
        binder: &VarBinder<Typ>,
    ) -> Result<R::Ret<VarBinder<Typ>>, Err> {
        let a = self.visit_typ(&binder.a)?;
        R::ret(|| binder.new_a(R::get(a)))
    }

    fn visit_var_binder_exp(
        &mut self,
        binder: &VarBinder<Exp>,
    ) -> Result<R::Ret<VarBinder<Exp>>, Err> {
        let a = self.visit_exp(&binder.a)?;
        R::ret(|| binder.new_a(R::get(a)))
    }

    fn visit_dest(&mut self, dest: &Dest) -> Result<R::Ret<Dest>, Err> {
        let e = self.visit_exp(&dest.dest)?;
        R::ret(|| Dest { dest: R::get(e), is_init: dest.is_init })
    }

    fn visit_loop_inv(&mut self, inv: &LoopInv) -> Result<R::Ret<LoopInv>, Err> {
        let e = self.visit_exp(&inv.inv)?;
        R::ret(|| LoopInv { at_entry: inv.at_entry, at_exit: inv.at_exit, inv: R::get(e) })
    }

    fn visit_typ_inv_vars(
        &mut self,
        typ_inv_vars: &Vec<(UniqueIdent, Typ)>,
    ) -> Result<R::Vec<(UniqueIdent, Typ)>, Err> {
        let mut typ_inv_vars2 = R::vec();
        for (uid, typ) in typ_inv_vars.iter() {
            let typ = self.visit_typ(typ)?;
            R::push(&mut typ_inv_vars2, R::ret(|| (uid.clone(), R::get(typ)))?);
        }
        Ok(typ_inv_vars2)
    }

    fn visit_exp_rec(&mut self, exp: &Exp) -> Result<R::Ret<Exp>, Err> {
        let typ = self.visit_typ(&exp.typ)?;
        let exp_new = |e: ExpX| SpannedTyped::new(&exp.span, &R::get(typ), e);
        match &exp.x {
            ExpX::Const(_) => R::ret(|| exp.clone()),
            ExpX::Var(..) => R::ret(|| exp.clone()),
            ExpX::VarAt(..) => R::ret(|| exp.clone()),
            ExpX::VarLoc(..) => R::ret(|| exp.clone()),
            ExpX::StaticVar(..) => R::ret(|| exp.clone()),
            ExpX::ExecFnByName(_) => R::ret(|| exp.clone()),
            ExpX::FuelConst(_) => R::ret(|| exp.clone()),
            ExpX::Loc(e1) => {
                let e1 = self.visit_exp(e1)?;
                R::ret(|| exp_new(ExpX::Loc(R::get(e1))))
            }
            ExpX::Old(..) => R::ret(|| exp.clone()),
            ExpX::Call(fun, ts, es) => {
                use crate::sst::CallFun;
                let fun = match fun {
                    CallFun::Fun(_, None) => R::ret(|| fun.clone()),
                    CallFun::Fun(f, Some((r, ts))) => {
                        let ts = self.visit_typs(ts)?;
                        R::ret(|| CallFun::Fun(f.clone(), Some((r.clone(), R::get_vec_a(ts)))))
                    }
                    CallFun::Recursive(..) | CallFun::InternalFun(..) => R::ret(|| fun.clone()),
                }?;
                let ts = self.visit_typs(ts)?;
                let es = self.visit_exps(es)?;
                R::ret(|| exp_new(ExpX::Call(R::get(fun), R::get_vec_a(ts), R::get_vec_a(es))))
            }
            ExpX::CallLambda(e0, es) => {
                let e0 = self.visit_exp(e0)?;
                let es = self.visit_exps(es)?;
                R::ret(|| exp_new(ExpX::CallLambda(R::get(e0), R::get_vec_a(es))))
            }
            ExpX::Ctor(path, ident, binders) => {
                let binders = R::map_vec(binders, &mut |b| self.visit_binder_exp(b))?;
                R::ret(|| exp_new(ExpX::Ctor(path.clone(), ident.clone(), R::get_vec_a(binders))))
            }
            ExpX::NullaryOpr(NullaryOpr::ConstGeneric(t)) => {
                let t = self.visit_typ(t)?;
                R::ret(|| exp_new(ExpX::NullaryOpr(NullaryOpr::ConstGeneric(R::get(t)))))
            }
            ExpX::NullaryOpr(NullaryOpr::TraitBound(p, ts)) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| {
                    exp_new(ExpX::NullaryOpr(NullaryOpr::TraitBound(p.clone(), R::get_vec_a(ts))))
                })
            }
            ExpX::NullaryOpr(NullaryOpr::TypEqualityBound(p, ts, x, t)) => {
                let ts = self.visit_typs(ts)?;
                let t = self.visit_typ(t)?;
                R::ret(|| {
                    exp_new(ExpX::NullaryOpr(NullaryOpr::TypEqualityBound(
                        p.clone(),
                        R::get_vec_a(ts),
                        x.clone(),
                        R::get(t),
                    )))
                })
            }
            ExpX::NullaryOpr(NullaryOpr::ConstTypBound(t1, t2)) => {
                let t1 = self.visit_typ(t1)?;
                let t2 = self.visit_typ(t2)?;
                R::ret(|| {
                    exp_new(ExpX::NullaryOpr(NullaryOpr::ConstTypBound(R::get(t1), R::get(t2))))
                })
            }
            ExpX::NullaryOpr(NullaryOpr::NoInferSpecForLoopIter) => R::ret(|| exp.clone()),
            ExpX::Unary(op, e1) => {
                let e1 = self.visit_exp(e1)?;
                R::ret(|| exp_new(ExpX::Unary(*op, R::get(e1))))
            }
            ExpX::UnaryOpr(op, e1) => {
                let e1 = self.visit_exp(e1)?;
                let op = match op {
                    UnaryOpr::Box(t) => {
                        let t = self.visit_typ(t)?;
                        R::ret(|| UnaryOpr::Box(R::get(t)))
                    }
                    UnaryOpr::Unbox(t) => {
                        let t = self.visit_typ(t)?;
                        R::ret(|| UnaryOpr::Unbox(R::get(t)))
                    }
                    UnaryOpr::HasType(t) => {
                        let t = self.visit_typ(t)?;
                        R::ret(|| UnaryOpr::HasType(R::get(t)))
                    }
                    UnaryOpr::IsVariant { .. }
                    | UnaryOpr::TupleField { .. }
                    | UnaryOpr::Field { .. }
                    | UnaryOpr::IntegerTypeBound(..)
                    | UnaryOpr::CustomErr(..) => R::ret(|| op.clone()),
                }?;
                R::ret(|| exp_new(ExpX::UnaryOpr(R::get(op), R::get(e1))))
            }
            ExpX::Binary(op, e1, e2) => {
                let e1 = self.visit_exp(e1)?;
                let e2 = self.visit_exp(e2)?;
                R::ret(|| exp_new(ExpX::Binary(*op, R::get(e1), R::get(e2))))
            }
            ExpX::BinaryOpr(BinaryOpr::ExtEq(deep, t), e1, e2) => {
                let t = self.visit_typ(t)?;
                let e1 = self.visit_exp(e1)?;
                let e2 = self.visit_exp(e2)?;
                R::ret(|| {
                    exp_new(ExpX::BinaryOpr(
                        BinaryOpr::ExtEq(*deep, R::get(t)),
                        R::get(e1),
                        R::get(e2),
                    ))
                })
            }
            ExpX::If(e1, e2, e3) => {
                let e1 = self.visit_exp(e1)?;
                let e2 = self.visit_exp(e2)?;
                let e3 = self.visit_exp(e3)?;
                R::ret(|| exp_new(ExpX::If(R::get(e1), R::get(e2), R::get(e3))))
            }
            ExpX::WithTriggers(triggers, body) => {
                let triggers = self.visit_triggers(triggers)?;
                let body = self.visit_exp(body)?;
                R::ret(|| exp_new(ExpX::WithTriggers(R::get(triggers), R::get(body))))
            }
            ExpX::Bind(bnd, e1) => {
                let bndx = match &bnd.x {
                    BndX::Let(bs) => {
                        let binders = R::map_vec(bs, &mut |b| self.visit_var_binder_exp(b))?;
                        self.push_scope();
                        for b in R::get_vec_or(&binders, &bs).iter() {
                            self.insert_binding_exp(b, bnd);
                        }
                        R::ret(|| BndX::Let(R::get_vec_a(binders)))?
                    }
                    BndX::Quant(quant, bs, ts) => {
                        let binders = R::map_vec(bs, &mut |b| self.visit_var_binder_typ(b))?;
                        self.push_scope();
                        for b in R::get_vec_or(&binders, &bs).iter() {
                            self.insert_binding_typ(b, bnd);
                        }
                        let ts = self.visit_triggers(ts)?;
                        R::ret(|| BndX::Quant(*quant, R::get_vec_a(binders), R::get(ts)))?
                    }
                    BndX::Lambda(bs, ts) => {
                        let binders = R::map_vec(bs, &mut |b| self.visit_var_binder_typ(b))?;
                        self.push_scope();
                        for b in R::get_vec_or(&binders, &bs).iter() {
                            self.insert_binding_typ(b, bnd);
                        }
                        let ts = self.visit_triggers(ts)?;
                        R::ret(|| BndX::Lambda(R::get_vec_a(binders), R::get(ts)))?
                    }
                    BndX::Choose(bs, ts, cond) => {
                        let binders = R::map_vec(bs, &mut |b| self.visit_var_binder_typ(b))?;
                        self.push_scope();
                        for b in R::get_vec_or(&binders, &bs).iter() {
                            self.insert_binding_typ(b, bnd);
                        }
                        let ts = self.visit_triggers(ts)?;
                        let cond = self.visit_exp(cond)?;
                        R::ret(|| BndX::Choose(R::get_vec_a(binders), R::get(ts), R::get(cond)))?
                    }
                };
                let e1 = self.visit_exp(e1)?;
                self.pop_scope();
                R::ret(|| {
                    exp_new(ExpX::Bind(Spanned::new(bnd.span.clone(), R::get(bndx)), R::get(e1)))
                })
            }
            ExpX::ArrayLiteral(es) => {
                let es = self.visit_exps(es)?;
                R::ret(|| exp_new(ExpX::ArrayLiteral(R::get_vec_a(es))))
            }
            ExpX::Interp(_) => R::ret(|| exp.clone()),
        }
    }

    fn visit_stm_rec(&mut self, stm: &Stm) -> Result<R::Ret<Stm>, Err> {
        let stm_new = |s: StmX| Spanned::new(stm.span.clone(), s);
        match &stm.x {
            StmX::Call { fun, resolved_method, mode, typ_args, args, split, dest, assert_id } => {
                let resolved_method = if let Some((f, ts)) = resolved_method {
                    let ts = self.visit_typs(ts)?;
                    R::ret(|| Some((f.clone(), R::get_vec_a(ts))))
                } else {
                    R::ret(|| None)
                }?;
                let typ_args = self.visit_typs(typ_args)?;
                let args = self.visit_exps(args)?;
                let dest = R::map_opt(dest, &mut |d| self.visit_dest(d))?;
                R::ret(|| {
                    stm_new(StmX::Call {
                        fun: fun.clone(),
                        resolved_method: R::get(resolved_method),
                        mode: *mode,
                        typ_args: R::get_vec_a(typ_args),
                        args: R::get_vec_a(args),
                        split: split.clone(),
                        dest: R::get_opt(dest),
                        assert_id: assert_id.clone(),
                    })
                })
            }
            StmX::Assert(assert_id, span2, exp) => {
                let exp = self.visit_exp(exp)?;
                R::ret(|| stm_new(StmX::Assert(assert_id.clone(), span2.clone(), R::get(exp))))
            }
            StmX::AssertBitVector { requires, ensures } => {
                let requires = self.visit_exps(requires)?;
                let ensures = self.visit_exps(ensures)?;
                R::ret(|| {
                    stm_new(StmX::AssertBitVector {
                        requires: R::get_vec_a(requires),
                        ensures: R::get_vec_a(ensures),
                    })
                })
            }
            StmX::AssertCompute(assert_id, exp, compute) => {
                let exp = self.visit_exp(exp)?;
                R::ret(|| stm_new(StmX::AssertCompute(assert_id.clone(), R::get(exp), *compute)))
            }
            StmX::Assume(exp) => {
                let exp = self.visit_exp(exp)?;
                R::ret(|| stm_new(StmX::Assume(R::get(exp))))
            }
            StmX::Assign { lhs, rhs } => {
                let lhs = self.visit_dest(lhs)?;
                let rhs = self.visit_exp(rhs)?;
                R::ret(|| stm_new(StmX::Assign { lhs: R::get(lhs), rhs: R::get(rhs) }))
            }
            StmX::Fuel(..) => R::ret(|| stm.clone()),
            StmX::RevealString(_) => R::ret(|| stm.clone()),
            StmX::DeadEnd(stm) => {
                let s = self.visit_stm(&stm)?;
                R::ret(|| stm_new(StmX::DeadEnd(R::get(s))))
            }
            StmX::Return { base_error, ret_exp, inside_body, assert_id } => {
                let ret_exp = R::map_opt(ret_exp, &mut |e| self.visit_exp(e))?;
                R::ret(|| {
                    stm_new(StmX::Return {
                        base_error: base_error.clone(),
                        ret_exp: R::get_opt(ret_exp),
                        inside_body: *inside_body,
                        assert_id: assert_id.clone(),
                    })
                })
            }
            StmX::BreakOrContinue { label: _, is_break: _ } => R::ret(|| stm.clone()),
            StmX::If(exp, s1, s2) => {
                let exp = self.visit_exp(exp)?;
                let s1 = self.visit_stm(s1)?;
                let s2 = R::map_opt(s2, &mut |s| self.visit_stm(s))?;
                R::ret(|| stm_new(StmX::If(R::get(exp), R::get(s1), R::get_opt(s2))))
            }
            StmX::Loop {
                loop_isolation,
                is_for_loop,
                id,
                label,
                cond,
                body,
                invs,
                decrease,
                typ_inv_vars,
                modified_vars,
            } => {
                let cond = R::map_opt(cond, &mut |(cond_stm, cond_exp)| {
                    let cond_stm = self.visit_stm(cond_stm)?;
                    let cond_exp = self.visit_exp(cond_exp)?;
                    R::ret(|| (R::get(cond_stm), R::get(cond_exp)))
                })?;
                let body = self.visit_stm(body)?;
                let invs = R::map_vec(invs, &mut |inv| self.visit_loop_inv(inv))?;
                let decrease = self.visit_exps(decrease)?;
                let typ_inv_vars = self.visit_typ_inv_vars(typ_inv_vars)?;
                R::ret(|| {
                    stm_new(StmX::Loop {
                        loop_isolation: *loop_isolation,
                        is_for_loop: *is_for_loop,
                        id: *id,
                        label: label.clone(),
                        cond: R::get_opt(cond),
                        body: R::get(body),
                        invs: R::get_vec_a(invs),
                        decrease: R::get_vec_a(decrease),
                        typ_inv_vars: R::get_vec_a(typ_inv_vars),
                        modified_vars: modified_vars.clone(),
                    })
                })
            }
            StmX::OpenInvariant(ns_exp, body) => {
                let ns_exp = self.visit_exp(ns_exp)?;
                let body = self.visit_stm(body)?;
                R::ret(|| stm_new(StmX::OpenInvariant(R::get(ns_exp), R::get(body))))
            }
            StmX::Block(stms) => {
                let stms = self.visit_stms(stms)?;
                R::ret(|| stm_new(StmX::Block(R::get_vec_a(stms))))
            }
            StmX::ClosureInner { body, typ_inv_vars } => {
                let body = self.visit_stm(body)?;
                let typ_inv_vars = self.visit_typ_inv_vars(typ_inv_vars)?;
                R::ret(|| {
                    stm_new(StmX::ClosureInner {
                        body: R::get(body),
                        typ_inv_vars: R::get_vec_a(typ_inv_vars),
                    })
                })
            }
            StmX::AssertQuery { mode, typ_inv_exps, typ_inv_vars, body } => {
                let typ_inv_exps = self.visit_exps(typ_inv_exps)?;
                let typ_inv_vars = self.visit_typ_inv_vars(typ_inv_vars)?;
                let body = self.visit_stm(body)?;
                R::ret(|| {
                    stm_new(StmX::AssertQuery {
                        mode: *mode,
                        typ_inv_exps: R::get_vec_a(typ_inv_exps),
                        typ_inv_vars: R::get_vec_a(typ_inv_vars),
                        body: R::get(body),
                    })
                })
            }
            StmX::Air(_) => R::ret(|| stm.clone()),
        }
    }

    fn visit_par(&mut self, par: &Par) -> Result<R::Ret<Par>, Err> {
        let t = self.visit_typ(&par.x.typ)?;
        R::ret(|| {
            Spanned::new(
                par.span.clone(),
                ParX {
                    name: par.x.name.clone(),
                    typ: R::get(t),
                    mode: par.x.mode,
                    is_mut: par.x.is_mut,
                    purpose: par.x.purpose,
                },
            )
        })
    }

    fn visit_pars(&mut self, exps: &Vec<Par>) -> Result<R::Vec<Par>, Err> {
        R::map_vec(exps, &mut |p| self.visit_par(p))
    }

    fn visit_local_decl(&mut self, local_decl: &LocalDecl) -> Result<R::Ret<LocalDecl>, Err> {
        let typ = self.visit_typ(&local_decl.typ)?;
        R::ret(|| {
            Arc::new(LocalDeclX {
                ident: local_decl.ident.clone(),
                typ: R::get(typ),
                mutable: local_decl.mutable,
            })
        })
    }

    fn visit_generic_bound(&mut self, bound: &GenericBound) -> Result<R::Ret<GenericBound>, Err> {
        match &**bound {
            GenericBoundX::Trait(p, ts) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| Arc::new(GenericBoundX::Trait(p.clone(), R::get_vec_a(ts))))
            }
            GenericBoundX::TypEquality(p, ts, x, t) => {
                let ts = self.visit_typs(ts)?;
                let t = self.visit_typ(t)?;
                R::ret(|| {
                    Arc::new(GenericBoundX::TypEquality(
                        p.clone(),
                        R::get_vec_a(ts),
                        x.clone(),
                        R::get(t),
                    ))
                })
            }
            GenericBoundX::ConstTyp(t1, t2) => {
                let t1 = self.visit_typ(t1)?;
                let t2 = self.visit_typ(t2)?;
                R::ret(|| Arc::new(GenericBoundX::ConstTyp(R::get(t1), R::get(t2))))
            }
        }
    }

    fn visit_generic_bounds(
        &mut self,
        bounds: &Vec<GenericBound>,
    ) -> Result<R::Vec<GenericBound>, Err> {
        R::map_vec(bounds, &mut |b| self.visit_generic_bound(b))
    }

    fn visit_postcondition(
        &mut self,
        post: &PostConditionSst,
    ) -> Result<R::Ret<PostConditionSst>, Err> {
        let ens_exps = self.visit_exps(&post.ens_exps)?;
        let ens_spec_precondition_stms = self.visit_stms(&post.ens_spec_precondition_stms)?;
        R::ret(|| PostConditionSst {
            dest: post.dest.clone(),
            ens_exps: R::get_vec_a(ens_exps),
            ens_spec_precondition_stms: R::get_vec_a(ens_spec_precondition_stms),
            kind: post.kind,
        })
    }

    fn visit_func_decl(&mut self, func_decl: &FuncDeclSst) -> Result<R::Ret<FuncDeclSst>, Err> {
        let req_inv_pars = self.visit_pars(&func_decl.req_inv_pars)?;
        let ens_pars = self.visit_pars(&func_decl.ens_pars)?;
        let post_pars = self.visit_pars(&func_decl.post_pars)?;
        let reqs = self.visit_exps(&func_decl.reqs)?;
        let enss = self.visit_exps(&func_decl.enss)?;
        let fndef_axioms = self.visit_exps(&func_decl.fndef_axioms)?;
        let mut inv_masks = R::vec();
        for es in func_decl.inv_masks.iter() {
            let es = self.visit_exps(es)?;
            R::push(&mut inv_masks, R::ret(|| R::get_vec_a(es))?);
        }
        let unwind_condition =
            R::map_opt(&func_decl.unwind_condition, &mut |exp| self.visit_exp(exp))?;
        R::ret(|| FuncDeclSst {
            req_inv_pars: R::get_vec_a(req_inv_pars),
            ens_pars: R::get_vec_a(ens_pars),
            post_pars: R::get_vec_a(post_pars),
            reqs: R::get_vec_a(reqs),
            enss: R::get_vec_a(enss),
            inv_masks: R::get_vec_a(inv_masks),
            unwind_condition: R::get_opt(unwind_condition),
            fndef_axioms: R::get_vec_a(fndef_axioms),
        })
    }

    fn visit_func_check(&mut self, def: &FuncCheckSst) -> Result<R::Ret<FuncCheckSst>, Err> {
        let reqs = self.visit_exps(&def.reqs)?;
        let post_condition = self.visit_postcondition(&def.post_condition)?;
        let body = self.visit_stm(&def.body)?;
        let local_decls = R::map_vec(&def.local_decls, &mut |decl| self.visit_local_decl(decl))?;
        let unwind = self.visit_unwind(&def.unwind)?;

        R::ret(|| FuncCheckSst {
            reqs: R::get_vec_a(reqs),
            post_condition: Arc::new(R::get(post_condition)),
            mask_set: def.mask_set.clone(),
            unwind: R::get(unwind),
            body: R::get(body),
            local_decls: R::get_vec_a(local_decls),
            statics: def.statics.clone(),
        })
    }

    fn visit_unwind(&mut self, unwind: &UnwindSst) -> Result<R::Ret<UnwindSst>, Err> {
        match unwind {
            UnwindSst::MayUnwind | UnwindSst::NoUnwind => R::ret(|| unwind.clone()),
            UnwindSst::NoUnwindWhen(exp) => {
                let exp = self.visit_exp(exp)?;
                R::ret(|| UnwindSst::NoUnwindWhen(R::get(exp)))
            }
        }
    }

    fn visit_func_body(&mut self, spec: &FuncSpecBodySst) -> Result<R::Ret<FuncSpecBodySst>, Err> {
        let decrease_when = R::map_opt(&spec.decrease_when, &mut |e| self.visit_exp(e))?;
        let termination_check =
            R::map_opt(&spec.termination_check, &mut |c| self.visit_func_check(c))?;
        let body_exp = self.visit_exp(&spec.body_exp)?;
        R::ret(|| FuncSpecBodySst {
            decrease_when: R::get_opt(decrease_when),
            termination_check: R::get_opt(termination_check),
            body_exp: R::get(body_exp),
        })
    }

    fn visit_func_axioms(&mut self, axioms: &FuncAxiomsSst) -> Result<R::Ret<FuncAxiomsSst>, Err> {
        let spec_axioms = R::map_opt(&axioms.spec_axioms, &mut |f| self.visit_func_body(f))?;
        let proof_exec_axioms =
            R::map_opt(&axioms.proof_exec_axioms, &mut |(pars, exp, trigs)| {
                let pars = self.visit_pars(&pars)?;
                let exp = self.visit_exp(&exp)?;
                let trigs = self.visit_triggers(&trigs)?;
                R::ret(|| (R::get_vec_a(pars), R::get(exp), R::get(trigs)))
            })?;
        R::ret(|| FuncAxiomsSst {
            spec_axioms: R::get_opt(spec_axioms),
            proof_exec_axioms: R::get_opt(proof_exec_axioms),
        })
    }

    fn visit_function(&mut self, f: &FunctionSst) -> Result<R::Ret<FunctionSst>, Err> {
        let typ_bounds = self.visit_generic_bounds(&f.x.typ_bounds)?;
        let pars = self.visit_pars(&f.x.pars)?;
        let ret = self.visit_par(&f.x.ret)?;
        let decl = self.visit_func_decl(&f.x.decl)?;
        let axioms = self.visit_func_axioms(&f.x.axioms)?;
        let exec_proof_check =
            R::map_opt(&f.x.exec_proof_check, &mut |c| self.visit_func_check(c))?;
        let recommends_check =
            R::map_opt(&f.x.recommends_check, &mut |c| self.visit_func_check(c))?;
        R::ret(|| {
            Spanned::new(
                f.span.clone(),
                FunctionSstX {
                    name: f.x.name.clone(),
                    kind: f.x.kind.clone(),
                    vis_abs: f.x.vis_abs.clone(),
                    owning_module: f.x.owning_module.clone(),
                    mode: f.x.mode,
                    fuel: f.x.fuel,
                    typ_params: f.x.typ_params.clone(),
                    typ_bounds: R::get_vec_a(typ_bounds),
                    pars: R::get_vec_a(pars),
                    ret: R::get(ret),
                    item_kind: f.x.item_kind,
                    publish: f.x.publish,
                    attrs: f.x.attrs.clone(),
                    has: f.x.has.clone(),
                    decl: Arc::new(R::get(decl)),
                    axioms: Arc::new(R::get(axioms)),
                    exec_proof_check: R::get_opt(exec_proof_check).map(|c| Arc::new(c)),
                    recommends_check: R::get_opt(recommends_check).map(|c| Arc::new(c)),
                },
            )
        })
    }
}

pub(crate) fn exp_visitor_check<E, MF>(
    expr: &Exp,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> Result<(), E>
where
    MF: FnMut(&Exp, &mut VisitorScopeMap) -> Result<(), E>,
{
    match exp_visitor_dfs(expr, map, &mut |expr, map| match mf(expr, map) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

struct ExpVisitorDfs<'a, F> {
    map: &'a mut VisitorScopeMap,
    f: &'a mut F,
}

impl<'a, T, F> Visitor<Walk, T, VisitorScopeMap> for ExpVisitorDfs<'a, F>
where
    F: FnMut(&Exp, &mut VisitorScopeMap) -> VisitorControlFlow<T>,
{
    fn visit_exp(&mut self, exp: &Exp) -> Result<(), T> {
        match (self.f)(exp, &mut self.map) {
            VisitorControlFlow::Stop(val) => Err(val),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Recurse => self.visit_exp_rec(exp),
        }
    }

    fn scoper(&mut self) -> Option<&mut VisitorScopeMap> {
        Some(&mut self.map)
    }
}

pub(crate) fn exp_visitor_dfs<T, F>(
    exp: &Exp,
    map: &mut VisitorScopeMap,
    f: &mut F,
) -> VisitorControlFlow<T>
where
    F: FnMut(&Exp, &mut VisitorScopeMap) -> VisitorControlFlow<T>,
{
    let mut visitor = ExpVisitorDfs { map, f };
    match visitor.visit_exp(exp) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(val) => VisitorControlFlow::Stop(val),
    }
}

struct StmVisitorDfs<'a, F> {
    f: &'a mut F,
}

impl<'a, T, F> Visitor<Walk, T, NoScoper> for StmVisitorDfs<'a, F>
where
    F: FnMut(&Stm) -> VisitorControlFlow<T>,
{
    fn visit_stm(&mut self, stm: &Stm) -> Result<(), T> {
        match (self.f)(stm) {
            VisitorControlFlow::Stop(val) => Err(val),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Recurse => self.visit_stm_rec(stm),
        }
    }
}

#[allow(dead_code)]
pub(crate) fn stm_visitor_dfs<T, F>(stm: &Stm, f: &mut F) -> VisitorControlFlow<T>
where
    F: FnMut(&Stm) -> VisitorControlFlow<T>,
{
    let mut visitor = StmVisitorDfs { f };
    match visitor.visit_stm(stm) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(val) => VisitorControlFlow::Stop(val),
    }
}

struct MapExpVisitorBind<'a, F> {
    map: &'a mut VisitorScopeMap,
    f: &'a mut F,
}

impl<'a, F> Visitor<Rewrite, VirErr, VisitorScopeMap> for MapExpVisitorBind<'a, F>
where
    F: FnMut(&Exp, &mut VisitorScopeMap) -> Result<Exp, VirErr>,
{
    fn visit_exp(&mut self, exp: &Exp) -> Result<Exp, VirErr> {
        let exp = self.visit_exp_rec(exp)?;
        (self.f)(&exp, &mut self.map)
    }

    fn scoper(&mut self) -> Option<&mut VisitorScopeMap> {
        Some(&mut self.map)
    }
}

pub(crate) fn map_exp_visitor_bind<F>(
    exp: &Exp,
    map: &mut VisitorScopeMap,
    f: &mut F,
) -> Result<Exp, VirErr>
where
    F: FnMut(&Exp, &mut VisitorScopeMap) -> Result<Exp, VirErr>,
{
    let mut visitor = MapExpVisitorBind { map, f };
    visitor.visit_exp(exp)
}

pub(crate) fn map_exp_visitor_result<F>(exp: &Exp, f: &mut F) -> Result<Exp, VirErr>
where
    F: FnMut(&Exp) -> Result<Exp, VirErr>,
{
    let mut map: VisitorScopeMap = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut map, &mut |e, _| f(e))
}

pub(crate) fn map_exp_visitor<F>(exp: &Exp, f: &mut F) -> Exp
where
    F: FnMut(&Exp) -> Exp,
{
    let mut map: VisitorScopeMap = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut map, &mut |e, _| Ok(f(e))).unwrap()
}

pub(crate) fn exp_rename_vars(exp: &Exp, map: &HashMap<UniqueIdent, UniqueIdent>) -> Exp {
    map_exp_visitor(exp, &mut |exp| match &exp.x {
        ExpX::VarAt(x, crate::ast::VarAt::Pre) if map.contains_key(x) => {
            SpannedTyped::new(&exp.span, &exp.typ, ExpX::Var(map[x].clone()))
        }
        ExpX::Var(x) if map.contains_key(x) => {
            SpannedTyped::new(&exp.span, &exp.typ, ExpX::Var(map[x].clone()))
        }
        _ => exp.clone(),
    })
}

struct MapShallowExp<'a, E, FT, FE> {
    env: &'a mut E,
    ft: &'a FT,
    fe: &'a FE,
}

impl<'a, E, FT, FE> Visitor<Rewrite, VirErr, NoScoper> for MapShallowExp<'a, E, FT, FE>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
    FE: Fn(&mut E, &Exp) -> Result<Exp, VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        (self.ft)(&mut self.env, typ)
    }

    fn visit_exp(&mut self, exp: &Exp) -> Result<Exp, VirErr> {
        (self.fe)(&mut self.env, exp)
    }
}

// non-recursive visitor
pub(crate) fn map_shallow_exp<E, FT, FE>(
    exp: &Exp,
    env: &mut E,
    ft: &FT,
    fe: &FE,
) -> Result<Exp, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
    FE: Fn(&mut E, &Exp) -> Result<Exp, VirErr>,
{
    let mut visitor = MapShallowExp { env, ft, fe };
    visitor.visit_exp_rec(exp)
}

struct MapStmVisitor<'a, F> {
    fs: &'a mut F,
}

impl<'a, F> Visitor<Rewrite, VirErr, NoScoper> for MapStmVisitor<'a, F>
where
    F: FnMut(&Stm) -> Result<Stm, VirErr>,
{
    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        let stm = self.visit_stm_rec(stm)?;
        (self.fs)(&stm)
    }
}

pub(crate) fn map_stm_visitor<F>(stm: &Stm, fs: &mut F) -> Result<Stm, VirErr>
where
    F: FnMut(&Stm) -> Result<Stm, VirErr>,
{
    let mut visitor = MapStmVisitor { fs };
    visitor.visit_stm(stm)
}

struct MapShallowStm<'a, F> {
    fs: &'a mut F,
}

impl<'a, F> Visitor<Rewrite, VirErr, NoScoper> for MapShallowStm<'a, F>
where
    F: FnMut(&Stm) -> Result<Stm, VirErr>,
{
    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        (self.fs)(stm)
    }
}

// non-recursive visitor
#[allow(unused)]
pub(crate) fn map_shallow_stm<F>(stm: &Stm, fs: &mut F) -> Result<Stm, VirErr>
where
    F: FnMut(&Stm) -> Result<Stm, VirErr>,
{
    let mut visitor = MapShallowStm { fs };
    visitor.visit_stm_rec(stm)
}

struct MapShallowStmTyp<'a, F> {
    ft: &'a F,
}

impl<'a, F> Visitor<Rewrite, VirErr, NoScoper> for MapShallowStmTyp<'a, F>
where
    F: Fn(&Typ) -> Result<Typ, VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        (self.ft)(typ)
    }

    // keep no-op visit_exp, visit_stm; we don't recurse into expressions and statements
}

/// Maps all the Typs in the Stm, doesn't recurse into any Stms
pub(crate) fn map_shallow_stm_typ<F>(stm: &Stm, ft: &F) -> Result<Stm, VirErr>
where
    F: Fn(&Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapShallowStmTyp { ft };
    visitor.visit_stm_rec(stm)
}

struct MapStmExpVisitor<'a, F> {
    fe: &'a F,
}

impl<'a, F> Visitor<Rewrite, VirErr, NoScoper> for MapStmExpVisitor<'a, F>
where
    F: Fn(&Exp) -> Result<Exp, VirErr>,
{
    fn visit_exp(&mut self, exp: &Exp) -> Result<Exp, VirErr> {
        (self.fe)(&exp)
    }

    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        self.visit_stm_rec(stm)
    }
}

// Apply fe to all subexpressions; does not recurse into expressions
pub(crate) fn map_stm_exp_visitor<F>(stm: &Stm, fe: &F) -> Result<Stm, VirErr>
where
    F: Fn(&Exp) -> Result<Exp, VirErr>,
{
    let mut visitor = MapStmExpVisitor { fe };
    visitor.visit_stm(stm)
}

struct MapStmPrevVisitor<'a, F> {
    fs: &'a mut F,
}

impl<'a, F> MapStmPrevVisitor<'a, F>
where
    F: FnMut(&Stm, Option<&Stm>) -> Result<Stm, VirErr>,
{
    fn visit_stm_prev(&mut self, stm: &Stm, prev: Option<&Stm>) -> Result<Stm, VirErr> {
        let stm = if let StmX::Block(ss) = &stm.x {
            let mut stms: Vec<Stm> = Vec::new();
            for (i, s) in ss.iter().enumerate() {
                let prev = if i == 0 { None } else { Some(&ss[i - 1]) };
                stms.push(self.visit_stm_prev(s, prev)?);
            }
            Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stms)))
        } else {
            self.visit_stm_rec(stm)?
        };
        (self.fs)(&stm, prev)
    }
}

impl<'a, F> Visitor<Rewrite, VirErr, NoScoper> for MapStmPrevVisitor<'a, F>
where
    F: FnMut(&Stm, Option<&Stm>) -> Result<Stm, VirErr>,
{
    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        self.visit_stm_prev(stm, None)
    }
}

/// F: FnMut(stm: &Stm, previous_stm: Option<&Stm>) -> Result<Stm, VirErr>
/// The second argument, previous_stm, is the directly previous Stm in the block, if it exists
pub(crate) fn map_stm_prev_visitor<F>(stm: &Stm, fs: &mut F) -> Result<Stm, VirErr>
where
    F: FnMut(&Stm, Option<&Stm>) -> Result<Stm, VirErr>,
{
    let mut visitor = MapStmPrevVisitor { fs };
    visitor.visit_stm(stm)
}
