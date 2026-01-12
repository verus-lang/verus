use crate::ast::{
    Arm, ArmX, Arms, AssocTypeImpl, AssocTypeImplX, BinaryOpr, CallTarget, CallTargetKind,
    CtorUpdateTail, Datatype, DatatypeX, Expr, ExprX, Exprs, Field, Function, FunctionKind,
    FunctionX, GenericBound, GenericBoundX, Krate, KrateX, LoopInvariant, LoopInvariants, MaskSpec,
    NullaryOpr, Param, ParamX, Params, Pattern, PatternBinding, PatternX, Place, PlaceX,
    SpannedTyped, Stmt, StmtX, Trait, TraitImpl, TraitImplX, TraitX, Typ, TypDecorationArg, TypX,
    Typs, UnaryOpr, UnwindSpec, VarBinder, VarBinderX, VarBinders, VarIdent, Variant, VirErr,
};
use crate::def::Spanned;
use crate::messages::Span;
use crate::util::vec_map_result;
pub(crate) use crate::visitor::{Returner, Rewrite, VisitorControlFlow, Walk};
use air::scope_map::ScopeMap;
use std::sync::Arc;

pub(crate) trait Scoper {
    fn push_scope(&mut self) {}
    fn pop_scope(&mut self) {}
    fn insert_binding(&mut self, _ident: &VarIdent, _entry: ScopeEntry) {}
    fn insert_pattern_bindings(&mut self, _pattern: &Pattern, _init: bool) {}
}

pub(crate) struct NoScoper;
impl Scoper for NoScoper {}

pub struct ScopeEntry {
    #[allow(dead_code)]
    pub typ: Typ,
    pub is_mut: bool,
    pub init: bool,
    pub is_outer_param_or_ret: bool,
}

impl ScopeEntry {
    pub(crate) fn new(typ: &Typ, is_mut: bool, init: bool) -> Self {
        ScopeEntry { typ: typ.clone(), is_mut, init, is_outer_param_or_ret: false }
    }
    fn new_outer_param_ret(typ: &Typ, is_mut: bool, init: bool) -> Self {
        ScopeEntry { typ: typ.clone(), is_mut, init, is_outer_param_or_ret: true }
    }
}

pub type VisitorScopeMap = ScopeMap<VarIdent, ScopeEntry>;

impl Scoper for ScopeMap<VarIdent, ScopeEntry> {
    fn push_scope(&mut self) {
        self.push_scope(true);
    }

    fn pop_scope(&mut self) {
        self.pop_scope();
    }

    fn insert_binding(&mut self, ident: &VarIdent, entry: ScopeEntry) {
        let _ = self.insert(ident.clone(), entry);
    }

    fn insert_pattern_bindings(&mut self, pattern: &Pattern, init: bool) {
        insert_pattern_vars(self, pattern, init);
    }
}

pub(crate) trait AstVisitor<R: Returner, Err, Scope: Scoper> {
    // These methods are often overridden to make a specific sort of visit

    fn visit_typ(&mut self, _typ: &Typ) -> Result<R::Ret<Typ>, Err> {
        unreachable!()
    }

    fn visit_expr(&mut self, _expr: &Expr) -> Result<R::Ret<Expr>, Err> {
        unreachable!()
    }

    fn visit_stmt(&mut self, _stmt: &Stmt) -> Result<R::Vec<Stmt>, Err> {
        unreachable!()
    }

    fn visit_pattern(&mut self, _pattern: &Pattern) -> Result<R::Ret<Pattern>, Err> {
        unreachable!()
    }

    fn visit_place(&mut self, _place: &Place) -> Result<R::Ret<Place>, Err> {
        unreachable!()
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

    fn insert_binding(&mut self, ident: &VarIdent, entry: ScopeEntry) {
        if let Some(scoper) = self.scoper() {
            scoper.insert_binding(ident, entry);
        }
    }

    fn insert_pattern_bindings(&mut self, pattern: &Pattern, init: bool) {
        if let Some(scoper) = self.scoper() {
            scoper.insert_pattern_bindings(pattern, init);
        }
    }

    fn visit_exprs(&mut self, exprs: &Vec<Expr>) -> Result<R::Vec<Expr>, Err> {
        R::map_vec(exprs, &mut |e| self.visit_expr(e))
    }

    fn visit_exprs_vec(&mut self, exprs: &Vec<Exprs>) -> Result<R::Vec<Exprs>, Err> {
        R::map_vec(exprs, &mut |es| {
            let es = self.visit_exprs(es)?;
            R::ret(|| R::get_vec_a(es))
        })
    }

    fn visit_opt_typ(&mut self, typ_opt: &Option<Typ>) -> Result<R::Opt<Typ>, Err> {
        R::map_opt(typ_opt, &mut |t| self.visit_typ(t))
    }

    fn visit_opt_expr(&mut self, expr_opt: &Option<Expr>) -> Result<R::Opt<Expr>, Err> {
        R::map_opt(expr_opt, &mut |e| self.visit_expr(e))
    }

    fn visit_opt_exprs(&mut self, exprs_opt: &Option<Exprs>) -> Result<R::Opt<Exprs>, Err> {
        R::map_opt(exprs_opt, &mut |es| {
            let es = self.visit_exprs(es)?;
            R::ret(|| R::get_vec_a(es))
        })
    }

    fn visit_opt_place(&mut self, place_opt: &Option<Place>) -> Result<R::Opt<Place>, Err> {
        R::map_opt(place_opt, &mut |p| self.visit_place(p))
    }

    fn visit_binders_expr(
        &mut self,
        binders: &air::ast::Binders<Expr>,
    ) -> Result<R::Vec<air::ast::Binder<Expr>>, Err> {
        R::map_vec(binders, &mut |b| {
            let air::ast::BinderX { name, a } = &**b;
            let a = self.visit_expr(a)?;
            R::ret(|| Arc::new(air::ast::BinderX { name: name.clone(), a: R::get(a) }))
        })
    }

    fn visit_binders_pattern(
        &mut self,
        binders: &air::ast::Binders<Pattern>,
    ) -> Result<R::Vec<air::ast::Binder<Pattern>>, Err> {
        R::map_vec(binders, &mut |b| {
            let air::ast::BinderX { name, a } = &**b;
            let a = self.visit_pattern(a)?;
            R::ret(|| Arc::new(air::ast::BinderX { name: name.clone(), a: R::get(a) }))
        })
    }

    fn visit_binder_typ(&mut self, b: &VarBinder<Typ>) -> Result<R::Ret<VarBinder<Typ>>, Err> {
        let VarBinderX { name, a } = &**b;
        let a = self.visit_typ(a)?;
        R::ret(|| Arc::new(VarBinderX { name: name.clone(), a: R::get(a) }))
    }

    fn visit_binders_typ(
        &mut self,
        binders: &VarBinders<Typ>,
    ) -> Result<R::Vec<VarBinder<Typ>>, Err> {
        R::map_vec(binders, &mut |b| self.visit_binder_typ(b))
    }

    fn visit_call_target_kind(
        &mut self,
        call_target_kind: &CallTargetKind,
    ) -> Result<R::Ret<CallTargetKind>, Err> {
        match call_target_kind {
            CallTargetKind::Static => R::ret(|| call_target_kind.clone()),
            CallTargetKind::ProofFn(_modes, _mode) => R::ret(|| call_target_kind.clone()),
            CallTargetKind::Dynamic => R::ret(|| call_target_kind.clone()),
            CallTargetKind::DynamicResolved { resolved, typs, impl_paths, is_trait_default } => {
                let typs = self.visit_typs(typs)?;
                R::ret(|| CallTargetKind::DynamicResolved {
                    resolved: resolved.clone(),
                    typs: R::get_vec_a(typs),
                    impl_paths: impl_paths.clone(),
                    is_trait_default: *is_trait_default,
                })
            }
            CallTargetKind::ExternalTraitDefault => R::ret(|| call_target_kind.clone()),
        }
    }

    fn visit_call_target(&mut self, call_target: &CallTarget) -> Result<R::Ret<CallTarget>, Err> {
        match call_target {
            CallTarget::Fun(kind, fun, typs, impl_paths, au) => {
                let kind = self.visit_call_target_kind(kind)?;
                let typs = self.visit_typs(typs)?;
                R::ret(|| {
                    CallTarget::Fun(
                        R::get(kind),
                        fun.clone(),
                        R::get_vec_a(typs),
                        impl_paths.clone(),
                        au.clone(),
                    )
                })
            }
            CallTarget::FnSpec(expr) => {
                let e = self.visit_expr(expr)?;
                R::ret(|| CallTarget::FnSpec(R::get(e)))
            }
            CallTarget::BuiltinSpecFun(bsf, typs, impl_paths) => {
                let typs = self.visit_typs(typs)?;
                R::ret(|| {
                    CallTarget::BuiltinSpecFun(bsf.clone(), R::get_vec_a(typs), impl_paths.clone())
                })
            }
        }
    }

    // TODO: NullaryOpr, UnaryOpr, BinaryOpr are all redundant with the SST visitor.
    fn visit_nullary_opr(&mut self, nopr: &NullaryOpr) -> Result<R::Ret<NullaryOpr>, Err> {
        match nopr {
            NullaryOpr::ConstGeneric(typ) => {
                let t = self.visit_typ(typ)?;
                R::ret(|| NullaryOpr::ConstGeneric(R::get(t)))
            }
            NullaryOpr::TraitBound(trait_id, typs) => {
                let ts = self.visit_typs(typs)?;
                R::ret(|| NullaryOpr::TraitBound(trait_id.clone(), R::get_vec_a(ts)))
            }
            NullaryOpr::TypEqualityBound(path, typs, id, typ) => {
                let ts = self.visit_typs(typs)?;
                let t = self.visit_typ(typ)?;
                R::ret(|| {
                    NullaryOpr::TypEqualityBound(
                        path.clone(),
                        R::get_vec_a(ts),
                        id.clone(),
                        R::get(t),
                    )
                })
            }
            NullaryOpr::ConstTypBound(t1, t2) => {
                let t1 = self.visit_typ(t1)?;
                let t2 = self.visit_typ(t2)?;
                R::ret(|| NullaryOpr::ConstTypBound(R::get(t1), R::get(t2)))
            }
            NullaryOpr::NoInferSpecForLoopIter => R::ret(|| nopr.clone()),
        }
    }

    fn visit_unary_opr(&mut self, uopr: &UnaryOpr) -> Result<R::Ret<UnaryOpr>, Err> {
        match uopr {
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
            UnaryOpr::HasResolved(t) => {
                let t = self.visit_typ(t)?;
                R::ret(|| UnaryOpr::HasResolved(R::get(t)))
            }
            UnaryOpr::IsVariant { .. }
            | UnaryOpr::Field { .. }
            | UnaryOpr::IntegerTypeBound(..)
            | UnaryOpr::CustomErr(..) => R::ret(|| uopr.clone()),
        }
    }

    fn visit_binary_opr(&mut self, bopr: &BinaryOpr) -> Result<R::Ret<BinaryOpr>, Err> {
        match bopr {
            BinaryOpr::ExtEq(deep, t) => {
                let t = self.visit_typ(t)?;
                R::ret(|| BinaryOpr::ExtEq(*deep, R::get(t)))
            }
        }
    }

    fn visit_expr_rec(&mut self, expr: &Expr) -> Result<R::Ret<Expr>, Err> {
        let typ = self.visit_typ(&expr.typ)?;
        let expr_new = |e: ExprX| SpannedTyped::new(&expr.span, &R::get(typ), e);
        match &expr.x {
            ExprX::Const(_) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::Var(_) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::VarLoc(_) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::VarAt(_, _) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::ConstVar(_, _) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::StaticVar(_) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::ExecFnByName(_fun) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::Fuel(_fun, _fuel, _is_broadcast_use) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::RevealString(_s) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::BreakOrContinue { label: _, is_break: _ } => R::ret(|| expr_new(expr.x.clone())),
            ExprX::AirStmt(_) => R::ret(|| expr_new(expr.x.clone())),
            ExprX::Nondeterministic => R::ret(|| expr_new(expr.x.clone())),
            ExprX::Loc(e) => {
                let e1 = self.visit_expr(e)?;
                R::ret(|| expr_new(ExprX::Loc(R::get(e1))))
            }
            ExprX::Call(call_target, exprs, opt_e) => {
                let ct = self.visit_call_target(call_target)?;
                let es = self.visit_exprs(exprs)?;
                let oe = self.visit_opt_expr(opt_e)?;
                R::ret(|| expr_new(ExprX::Call(R::get(ct), R::get_vec_a(es), R::get_opt(oe))))
            }
            ExprX::Ctor(dt, id, binders, opt_tail) => {
                let bs = self.visit_binders_expr(binders)?;
                let oe = R::map_opt(opt_tail, &mut |p| self.visit_ctor_update_tail(p))?;
                R::ret(|| {
                    expr_new(ExprX::Ctor(dt.clone(), id.clone(), R::get_vec_a(bs), R::get_opt(oe)))
                })
            }
            ExprX::NullaryOpr(nullary_opr) => {
                let no = self.visit_nullary_opr(nullary_opr)?;
                R::ret(|| expr_new(ExprX::NullaryOpr(R::get(no))))
            }
            ExprX::Unary(op, e) => {
                let e1 = self.visit_expr(e)?;
                R::ret(|| expr_new(ExprX::Unary(*op, R::get(e1))))
            }
            ExprX::UnaryOpr(opr, e) => {
                let uo = self.visit_unary_opr(opr)?;
                let e1 = self.visit_expr(e)?;
                R::ret(|| expr_new(ExprX::UnaryOpr(R::get(uo), R::get(e1))))
            }
            ExprX::Binary(op, e1, e2) => {
                let e1 = self.visit_expr(e1)?;
                let e2 = self.visit_expr(e2)?;
                R::ret(|| expr_new(ExprX::Binary(*op, R::get(e1), R::get(e2))))
            }
            ExprX::BinaryOpr(opr, e1, e2) => {
                let bo = self.visit_binary_opr(opr)?;
                let e1 = self.visit_expr(e1)?;
                let e2 = self.visit_expr(e2)?;
                R::ret(|| expr_new(ExprX::BinaryOpr(R::get(bo), R::get(e1), R::get(e2))))
            }
            ExprX::Multi(multi_op, es) => {
                let es = self.visit_exprs(es)?;
                R::ret(|| expr_new(ExprX::Multi(multi_op.clone(), R::get_vec_a(es))))
            }
            ExprX::Quant(quant, bs, e) => {
                let binders = self.visit_binders_typ(bs)?;
                self.push_scope();
                for b in R::get_vec_or(&binders, bs).iter() {
                    self.insert_binding(&b.name, ScopeEntry::new(&b.a, false, true));
                }
                let e = self.visit_expr(e)?;
                self.pop_scope();
                R::ret(|| expr_new(ExprX::Quant(quant.clone(), R::get_vec_a(binders), R::get(e))))
            }
            ExprX::Closure(bs, e) => {
                let binders = self.visit_binders_typ(bs)?;
                self.push_scope();
                for b in R::get_vec_or(&binders, bs).iter() {
                    self.insert_binding(&b.name, ScopeEntry::new(&b.a, false, true));
                }
                let e = self.visit_expr(e)?;
                self.pop_scope();
                R::ret(|| expr_new(ExprX::Closure(R::get_vec_a(binders), R::get(e))))
            }
            ExprX::NonSpecClosure {
                params: p,
                proof_fn_modes,
                body,
                requires,
                ensures,
                ret: r,
                external_spec,
            } => {
                let params = self.visit_binders_typ(p)?;
                let ret = self.visit_binder_typ(r)?;

                self.push_scope();
                for b in R::get_vec_or(&params, p).iter() {
                    self.insert_binding(&b.name, ScopeEntry::new(&b.a, false, true));
                }

                let requires = self.visit_exprs(requires)?;

                self.push_scope();
                let b = R::get_or(&ret, r);
                self.insert_binding(&b.name, ScopeEntry::new(&b.a, false, true));

                let ensures = self.visit_exprs(ensures)?;

                self.pop_scope();

                let body = self.visit_expr(body)?;

                self.pop_scope();

                let external_spec = R::map_opt(external_spec, &mut |(var_ident, e)| {
                    let e = self.visit_expr(e)?;
                    R::ret(|| (var_ident.clone(), R::get(e)))
                })?;

                R::ret(|| {
                    expr_new(ExprX::NonSpecClosure {
                        params: R::get_vec_a(params),
                        proof_fn_modes: proof_fn_modes.clone(),
                        body: R::get(body),
                        requires: R::get_vec_a(requires),
                        ensures: R::get_vec_a(ensures),
                        ret: R::get(ret),
                        external_spec: R::get_opt(external_spec),
                    })
                })
            }
            ExprX::ArrayLiteral(es) => {
                let es = self.visit_exprs(es)?;
                R::ret(|| expr_new(ExprX::ArrayLiteral(R::get_vec_a(es))))
            }
            ExprX::Choose { params: bs, cond, body } => {
                let binders = self.visit_binders_typ(bs)?;
                self.push_scope();
                for b in R::get_vec_or(&binders, bs).iter() {
                    self.insert_binding(&b.name, ScopeEntry::new(&b.a, false, true));
                }
                let cond = self.visit_expr(cond)?;
                let body = self.visit_expr(body)?;
                self.pop_scope();
                R::ret(|| {
                    expr_new(ExprX::Choose {
                        params: R::get_vec_a(binders),
                        cond: R::get(cond),
                        body: R::get(body),
                    })
                })
            }
            ExprX::WithTriggers { triggers, body } => {
                let triggers = self.visit_exprs_vec(triggers)?;
                let body = self.visit_expr(body)?;
                R::ret(|| {
                    expr_new(ExprX::WithTriggers {
                        triggers: R::get_vec_a(triggers),
                        body: R::get(body),
                    })
                })
            }
            ExprX::Assign { init_not_mut, lhs, rhs, op } => {
                let lhs = self.visit_expr(lhs)?;
                let rhs = self.visit_expr(rhs)?;
                R::ret(|| {
                    expr_new(ExprX::Assign {
                        init_not_mut: *init_not_mut,
                        lhs: R::get(lhs),
                        rhs: R::get(rhs),
                        op: *op,
                    })
                })
            }
            ExprX::AssignToPlace { place, rhs, op, resolve } => {
                let place = self.visit_place(place)?;
                let rhs = self.visit_expr(rhs)?;
                let resolve = self.visit_opt_typ(resolve)?;
                R::ret(|| {
                    expr_new(ExprX::AssignToPlace {
                        place: R::get(place),
                        rhs: R::get(rhs),
                        op: *op,
                        resolve: R::get_opt(resolve),
                    })
                })
            }
            ExprX::Header(_) => {
                // don't descend into Headers
                R::ret(|| expr_new(expr.x.clone()))
            }
            ExprX::AssertAssume { is_assume, expr, msg } => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| {
                    expr_new(ExprX::AssertAssume {
                        is_assume: *is_assume,
                        expr: R::get(expr),
                        msg: msg.clone(),
                    })
                })
            }
            ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume, expr, fun } => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| {
                    expr_new(ExprX::AssertAssumeUserDefinedTypeInvariant {
                        is_assume: *is_assume,
                        expr: R::get(expr),
                        fun: fun.clone(),
                    })
                })
            }
            ExprX::AssertBy { vars: bs, require, ensure, proof } => {
                let binders = self.visit_binders_typ(bs)?;
                self.push_scope();
                for b in R::get_vec_or(&binders, bs).iter() {
                    self.insert_binding(&b.name, ScopeEntry::new(&b.a, false, true));
                }
                let require = self.visit_expr(require)?;
                let ensure = self.visit_expr(ensure)?;
                let proof = self.visit_expr(proof)?;
                self.pop_scope();
                R::ret(|| {
                    expr_new(ExprX::AssertBy {
                        vars: R::get_vec_a(binders),
                        require: R::get(require),
                        ensure: R::get(ensure),
                        proof: R::get(proof),
                    })
                })
            }
            ExprX::AssertQuery { requires, ensures, proof, mode } => {
                let requires = self.visit_exprs(requires)?;
                let ensures = self.visit_exprs(ensures)?;
                let proof = self.visit_expr(proof)?;
                R::ret(|| {
                    expr_new(ExprX::AssertQuery {
                        requires: R::get_vec_a(requires),
                        ensures: R::get_vec_a(ensures),
                        proof: R::get(proof),
                        mode: *mode,
                    })
                })
            }
            ExprX::AssertCompute(expr, compute_mode) => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| expr_new(ExprX::AssertCompute(R::get(expr), *compute_mode)))
            }
            ExprX::If(cond, thn, els) => {
                let cond = self.visit_expr(cond)?;
                let thn = self.visit_expr(thn)?;
                let els = self.visit_opt_expr(els)?;
                R::ret(|| expr_new(ExprX::If(R::get(cond), R::get(thn), R::get_opt(els))))
            }
            ExprX::Match(place, arms) => {
                let place = self.visit_place(place)?;
                let arms = self.visit_arms(arms)?;
                R::ret(|| expr_new(ExprX::Match(R::get(place), R::get_vec_a(arms))))
            }
            ExprX::Loop { loop_isolation, is_for_loop, label, cond, body, invs, decrease } => {
                let cond = self.visit_opt_expr(cond)?;
                let body = self.visit_expr(body)?;
                let invs = self.visit_loop_invariants(invs)?;
                let decrease = self.visit_exprs(decrease)?;
                R::ret(|| {
                    expr_new(ExprX::Loop {
                        loop_isolation: *loop_isolation,
                        is_for_loop: *is_for_loop,
                        label: label.clone(),
                        cond: R::get_opt(cond),
                        body: R::get(body),
                        invs: R::get_vec_a(invs),
                        decrease: R::get_vec_a(decrease),
                    })
                })
            }
            ExprX::OpenInvariant(e, b, body, ato) => {
                let e = self.visit_expr(e)?;

                let binder = self.visit_binder_typ(b)?;

                self.push_scope();
                let b = R::get_or(&binder, b);
                self.insert_binding(&b.name, ScopeEntry::new(&b.a, true, true));

                let body = self.visit_expr(body)?;

                self.pop_scope();

                R::ret(|| {
                    expr_new(ExprX::OpenInvariant(R::get(e), R::get(binder), R::get(body), *ato))
                })
            }
            ExprX::Return(e) => {
                let e = self.visit_opt_expr(e)?;
                R::ret(|| expr_new(ExprX::Return(R::get_opt(e))))
            }
            ExprX::Ghost { alloc_wrapper, tracked, expr } => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| {
                    expr_new(ExprX::Ghost {
                        alloc_wrapper: *alloc_wrapper,
                        tracked: *tracked,
                        expr: R::get(expr),
                    })
                })
            }
            ExprX::ProofInSpec(e) => {
                let e = self.visit_expr(e)?;
                R::ret(|| expr_new(ExprX::ProofInSpec(R::get(e))))
            }
            ExprX::Block(stmts, e) => {
                let mut scope_count = 0;

                let stmts = R::map_vec_and_flatten(stmts, &mut |s| {
                    let stmts = self.visit_stmt(s)?;

                    for stmt in R::get_vec_or_slice(&stmts, std::array::from_ref(s)).iter() {
                        match &stmt.x {
                            StmtX::Expr(_) => {}
                            StmtX::Decl { pattern, mode: _, init, els: _ } => {
                                self.push_scope();
                                self.insert_pattern_bindings(pattern, init.is_some());
                                scope_count += 1;
                            }
                        }
                    }

                    Ok(stmts)
                })?;

                let e = self.visit_opt_expr(e)?;

                for _i in 0..scope_count {
                    self.pop_scope();
                }

                R::ret(|| expr_new(ExprX::Block(R::get_vec_a(stmts), R::get_opt(e))))
            }
            ExprX::NeverToAny(e) => {
                let e = self.visit_expr(e)?;
                R::ret(|| expr_new(ExprX::NeverToAny(R::get(e))))
            }
            ExprX::BorrowMut(p) => {
                let p = self.visit_place(p)?;
                R::ret(|| expr_new(ExprX::BorrowMut(R::get(p))))
            }
            ExprX::TwoPhaseBorrowMut(p) => {
                let p = self.visit_place(p)?;
                R::ret(|| expr_new(ExprX::TwoPhaseBorrowMut(R::get(p))))
            }
            ExprX::ReadPlace(p, read_type) => {
                let p = self.visit_place(p)?;
                R::ret(|| expr_new(ExprX::ReadPlace(R::get(p), *read_type)))
            }
            ExprX::UseLeftWhereRightCanHaveNoAssignments(e1, e2) => {
                let e1 = self.visit_expr(e1)?;
                let e2 = self.visit_expr(e2)?;
                R::ret(|| {
                    expr_new(ExprX::UseLeftWhereRightCanHaveNoAssignments(R::get(e1), R::get(e2)))
                })
            }
        }
    }

    fn visit_ctor_update_tail(
        &mut self,
        tail: &CtorUpdateTail,
    ) -> Result<R::Ret<CtorUpdateTail>, Err> {
        let CtorUpdateTail { place, taken_fields } = tail;
        let place = self.visit_place(place)?;
        R::ret(|| CtorUpdateTail { place: R::get(place), taken_fields: taken_fields.clone() })
    }

    fn visit_arms(&mut self, arms: &Arms) -> Result<R::Vec<Arm>, Err> {
        R::map_vec(arms, &mut |e| self.visit_arm(e))
    }

    fn visit_arm(&mut self, arm: &Arm) -> Result<R::Ret<Arm>, Err> {
        let ArmX { pattern: p, guard, body } = &arm.x;
        let pattern = self.visit_pattern(p)?;
        self.push_scope();
        self.insert_pattern_bindings(R::get_or(&pattern, p), true);
        let guard = self.visit_expr(guard)?;
        let body = self.visit_expr(body)?;
        self.pop_scope();
        R::ret(|| {
            Spanned::new(
                arm.span.clone(),
                ArmX { pattern: R::get(pattern), guard: R::get(guard), body: R::get(body) },
            )
        })
    }

    fn visit_loop_invariants(
        &mut self,
        invs: &LoopInvariants,
    ) -> Result<R::Vec<LoopInvariant>, Err> {
        R::map_vec(invs, &mut |e| self.visit_loop_invariant(e))
    }

    fn visit_loop_invariant(&mut self, inv: &LoopInvariant) -> Result<R::Ret<LoopInvariant>, Err> {
        let LoopInvariant { kind, inv: e } = inv;
        let e = self.visit_expr(e)?;
        R::ret(|| LoopInvariant { kind: *kind, inv: R::get(e) })
    }

    fn visit_stmt_rec(&mut self, stmt: &Stmt) -> Result<R::Ret<Stmt>, Err> {
        let stmt_new = |s: StmtX| Spanned::new(stmt.span.clone(), s);
        match &stmt.x {
            StmtX::Expr(e) => {
                let e = self.visit_expr(e)?;
                R::ret(|| stmt_new(StmtX::Expr(R::get(e))))
            }
            StmtX::Decl { pattern, mode, init, els } => {
                let pattern = self.visit_pattern(pattern)?;
                let init = self.visit_opt_place(init)?;
                let els = self.visit_opt_expr(els)?;
                R::ret(|| {
                    stmt_new(StmtX::Decl {
                        pattern: R::get(pattern),
                        mode: *mode,
                        init: R::get_opt(init),
                        els: R::get_opt(els),
                    })
                })
            }
        }
    }

    fn visit_pattern_binding(
        &mut self,
        pb: &PatternBinding,
    ) -> Result<R::Ret<PatternBinding>, Err> {
        let PatternBinding { name, by_ref, typ, mutable, copy } = pb;
        let typ = self.visit_typ(typ)?;
        R::ret(|| PatternBinding {
            name: name.clone(),
            by_ref: *by_ref,
            typ: R::get(typ),
            mutable: *mutable,
            copy: *copy,
        })
    }

    fn visit_pattern_rec(&mut self, pattern: &Pattern) -> Result<R::Ret<Pattern>, Err> {
        let typ = self.visit_typ(&pattern.typ)?;
        let pattern_new = |p: PatternX| SpannedTyped::new(&pattern.span, &R::get(typ), p);
        match &pattern.x {
            PatternX::Wildcard(_) => R::ret(|| pattern_new(pattern.x.clone())),
            PatternX::Var(binding) => {
                let binding = self.visit_pattern_binding(binding)?;
                R::ret(|| pattern_new(PatternX::Var(R::get(binding))))
            }
            PatternX::Binding { binding, sub_pat } => {
                let binding = self.visit_pattern_binding(binding)?;
                let sub_pat = self.visit_pattern(sub_pat)?;
                R::ret(|| {
                    pattern_new(PatternX::Binding {
                        binding: R::get(binding),
                        sub_pat: R::get(sub_pat),
                    })
                })
            }
            PatternX::Constructor(dt, ident, bs) => {
                let bs = self.visit_binders_pattern(bs)?;
                R::ret(|| {
                    pattern_new(PatternX::Constructor(dt.clone(), ident.clone(), R::get_vec_a(bs)))
                })
            }
            PatternX::Or(a, b) => {
                let a = self.visit_pattern(a)?;
                let b = self.visit_pattern(b)?;
                R::ret(|| pattern_new(PatternX::Or(R::get(a), R::get(b))))
            }
            PatternX::Expr(e) => {
                let e = self.visit_expr(e)?;
                R::ret(|| pattern_new(PatternX::Expr(R::get(e))))
            }
            PatternX::Range(start, end) => {
                let start = self.visit_opt_expr(start)?;
                let end = R::map_opt(end, &mut |(end_expr, ineq_op)| {
                    let end_expr = self.visit_expr(end_expr)?;
                    R::ret(|| (R::get(end_expr), *ineq_op))
                })?;
                R::ret(|| pattern_new(PatternX::Range(R::get_opt(start), R::get_opt(end))))
            }
            PatternX::ImmutRef(p) => {
                let p = self.visit_pattern(p)?;
                R::ret(|| pattern_new(PatternX::ImmutRef(R::get(p))))
            }
            PatternX::MutRef(p) => {
                let p = self.visit_pattern(p)?;
                R::ret(|| pattern_new(PatternX::MutRef(R::get(p))))
            }
        }
    }

    fn visit_place_rec(&mut self, place: &Place) -> Result<R::Ret<Place>, Err> {
        let typ = self.visit_typ(&place.typ)?;
        let place_new = |p: PlaceX| SpannedTyped::new(&place.span, &R::get(typ), p);
        match &place.x {
            PlaceX::Field(field_opr, p) => {
                let p = self.visit_place(p)?;
                R::ret(|| place_new(PlaceX::Field(field_opr.clone(), R::get(p))))
            }
            PlaceX::Local(_ident) => R::ret(|| place_new(place.x.clone())),
            PlaceX::DerefMut(p) => {
                let p = self.visit_place(p)?;
                R::ret(|| place_new(PlaceX::DerefMut(R::get(p))))
            }
            PlaceX::Temporary(e) => {
                let e = self.visit_expr(e)?;
                R::ret(|| place_new(PlaceX::Temporary(R::get(e))))
            }
            PlaceX::ModeUnwrap(p, mode) => {
                let p = self.visit_place(p)?;
                R::ret(|| place_new(PlaceX::ModeUnwrap(R::get(p), *mode)))
            }
            PlaceX::WithExpr(e, p) => {
                let e = self.visit_expr(e)?;
                let p = self.visit_place(p)?;
                R::ret(|| place_new(PlaceX::WithExpr(R::get(e), R::get(p))))
            }
            PlaceX::Index(p, idx, kind, needs_bounds_check) => {
                let p = self.visit_place(p)?;
                let idx = self.visit_expr(idx)?;
                R::ret(|| {
                    place_new(PlaceX::Index(R::get(p), R::get(idx), *kind, *needs_bounds_check))
                })
            }
        }
    }

    fn visit_typs(&mut self, typs: &Vec<Typ>) -> Result<R::Vec<Typ>, Err> {
        R::map_vec(typs, &mut |t| self.visit_typ(t))
    }

    fn visit_typ_rec(&mut self, typ: &Typ) -> Result<R::Ret<Typ>, Err> {
        match &**typ {
            TypX::Bool => R::ret(|| typ.clone()),
            TypX::Int(_) => R::ret(|| typ.clone()),
            TypX::Real => R::ret(|| typ.clone()),
            TypX::Float(_) => R::ret(|| typ.clone()),
            TypX::TypParam(_) => R::ret(|| typ.clone()),
            TypX::TypeId => R::ret(|| typ.clone()),
            TypX::ConstInt(_) => R::ret(|| typ.clone()),
            TypX::ConstBool(_) => R::ret(|| typ.clone()),
            TypX::Air(_) => R::ret(|| typ.clone()),
            TypX::Opaque { def_path, args } => {
                let args = self.visit_typs(args)?;
                R::ret(|| {
                    Arc::new(TypX::Opaque { def_path: def_path.clone(), args: R::get_vec_a(args) })
                })
            }
            TypX::SpecFn(ts, tr) => {
                let ts = self.visit_typs(ts)?;
                let tr = self.visit_typ(tr)?;
                R::ret(|| Arc::new(TypX::SpecFn(R::get_vec_a(ts), R::get(tr))))
            }
            TypX::AnonymousClosure(ts, tr, id) => {
                let ts = self.visit_typs(ts)?;
                let tr = self.visit_typ(tr)?;
                R::ret(|| Arc::new(TypX::AnonymousClosure(R::get_vec_a(ts), R::get(tr), *id)))
            }
            TypX::FnDef(fun, ts, res_fun) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| Arc::new(TypX::FnDef(fun.clone(), R::get_vec_a(ts), res_fun.clone())))
            }
            TypX::Datatype(path, ts, impl_paths) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| {
                    Arc::new(TypX::Datatype(path.clone(), R::get_vec_a(ts), impl_paths.clone()))
                })
            }
            TypX::Dyn(path, ts, impl_paths) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| Arc::new(TypX::Dyn(path.clone(), R::get_vec_a(ts), impl_paths.clone())))
            }
            TypX::Primitive(p, ts) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| Arc::new(TypX::Primitive(p.clone(), R::get_vec_a(ts))))
            }
            TypX::Decorate(d, targ, t) => {
                let targ = if let Some(TypDecorationArg { allocator_typ }) = targ {
                    let allocator_typ = self.visit_typ(allocator_typ)?;
                    R::ret(|| Some(TypDecorationArg { allocator_typ: R::get(allocator_typ) }))
                } else {
                    R::ret(|| None)
                }?;
                let t = self.visit_typ(t)?;
                R::ret(|| Arc::new(TypX::Decorate(*d, R::get(targ), R::get(t))))
            }
            TypX::Boxed(t) => {
                let t = self.visit_typ(t)?;
                R::ret(|| Arc::new(TypX::Boxed(R::get(t))))
            }
            TypX::Projection { trait_typ_args, trait_path, name } => {
                let trait_typ_args = self.visit_typs(trait_typ_args)?;
                R::ret(|| {
                    Arc::new(TypX::Projection {
                        trait_typ_args: R::get_vec_a(trait_typ_args),
                        trait_path: trait_path.clone(),
                        name: name.clone(),
                    })
                })
            }
            TypX::PointeeMetadata(t) => {
                let t = self.visit_typ(t)?;
                R::ret(|| Arc::new(TypX::PointeeMetadata(R::get(t))))
            }
            TypX::MutRef(t) => {
                let t = self.visit_typ(t)?;
                R::ret(|| Arc::new(TypX::MutRef(R::get(t))))
            }
        }
    }

    fn visit_generic_bound(&mut self, b: &GenericBound) -> Result<R::Ret<GenericBound>, Err> {
        match &**b {
            GenericBoundX::Trait(trait_id, typs) => {
                let ts = self.visit_typs(typs)?;
                R::ret(|| Arc::new(GenericBoundX::Trait(trait_id.clone(), R::get_vec_a(ts))))
            }
            GenericBoundX::TypEquality(path, typs, id, typ) => {
                let ts = self.visit_typs(typs)?;
                let t = self.visit_typ(typ)?;
                R::ret(|| {
                    Arc::new(GenericBoundX::TypEquality(
                        path.clone(),
                        R::get_vec_a(ts),
                        id.clone(),
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
        bs: &Vec<GenericBound>,
    ) -> Result<R::Vec<GenericBound>, Err> {
        R::map_vec(bs, &mut |b| self.visit_generic_bound(b))
    }

    fn visit_param(&mut self, param: &Param) -> Result<R::Ret<Param>, Err> {
        let ParamX { name, typ, mode, is_mut, unwrapped_info } = &param.x;
        let typ = self.visit_typ(typ)?;
        R::ret(|| {
            param.new_x(ParamX {
                name: name.clone(),
                typ: R::get(typ),
                mode: *mode,
                is_mut: *is_mut,
                unwrapped_info: unwrapped_info.clone(),
            })
        })
    }

    fn visit_params(&mut self, params: &Vec<Param>) -> Result<R::Vec<Param>, Err> {
        R::map_vec(params, &mut |p| self.visit_param(p))
    }

    fn visit_mask_spec(&mut self, ms: &MaskSpec) -> Result<R::Ret<MaskSpec>, Err> {
        match ms {
            MaskSpec::InvariantOpens(span, exprs) => {
                let exprs = self.visit_exprs(exprs)?;
                R::ret(|| MaskSpec::InvariantOpens(span.clone(), R::get_vec_a(exprs)))
            }
            MaskSpec::InvariantOpensExcept(span, exprs) => {
                let exprs = self.visit_exprs(exprs)?;
                R::ret(|| MaskSpec::InvariantOpensExcept(span.clone(), R::get_vec_a(exprs)))
            }
            MaskSpec::InvariantOpensSet(expr) => {
                let e = self.visit_expr(expr)?;
                R::ret(|| MaskSpec::InvariantOpensSet(R::get(e)))
            }
        }
    }

    fn visit_unwind_spec(&mut self, us: &UnwindSpec) -> Result<R::Ret<UnwindSpec>, Err> {
        match us {
            UnwindSpec::NoUnwind => R::ret(|| UnwindSpec::NoUnwind),
            UnwindSpec::NoUnwindWhen(expr) => {
                let e = self.visit_expr(expr)?;
                R::ret(|| UnwindSpec::NoUnwindWhen(R::get(e)))
            }
            UnwindSpec::MayUnwind => R::ret(|| UnwindSpec::MayUnwind),
        }
    }

    fn visit_function_kind(&mut self, kind: &FunctionKind) -> Result<R::Ret<FunctionKind>, Err> {
        match kind {
            FunctionKind::Static => R::ret(|| kind.clone()),
            FunctionKind::TraitMethodDecl { trait_path: _, has_default: _ } => {
                R::ret(|| kind.clone())
            }
            FunctionKind::TraitMethodImpl {
                method,
                impl_path,
                trait_path,
                trait_typ_args,
                inherit_body_from,
            } => {
                let trait_typ_args = self.visit_typs(trait_typ_args)?;
                R::ret(|| FunctionKind::TraitMethodImpl {
                    method: method.clone(),
                    impl_path: impl_path.clone(),
                    trait_path: trait_path.clone(),
                    trait_typ_args: R::get_vec_a(trait_typ_args),
                    inherit_body_from: inherit_body_from.clone(),
                })
            }
            FunctionKind::ForeignTraitMethodImpl {
                method,
                impl_path,
                trait_path,
                trait_typ_args,
            } => {
                let trait_typ_args = self.visit_typs(trait_typ_args)?;
                R::ret(|| FunctionKind::ForeignTraitMethodImpl {
                    method: method.clone(),
                    impl_path: impl_path.clone(),
                    trait_path: trait_path.clone(),
                    trait_typ_args: R::get_vec_a(trait_typ_args),
                })
            }
        }
    }

    fn visit_function(&mut self, function: &Function) -> Result<R::Ret<Function>, Err> {
        let FunctionX {
            name,
            proxy,
            kind,
            visibility,
            body_visibility,
            opaqueness,
            owning_module,
            mode,
            typ_params,
            typ_bounds,
            params: ps,
            ret: rt,
            ens_has_return,
            require,
            ensure: (ensure0, ensure1),
            returns,
            decrease,
            decrease_when,
            decrease_by,
            fndef_axioms,
            mask_spec,
            unwind_spec,
            item_kind,
            attrs,
            body,
            extra_dependencies,
        } = &function.x;
        let kind = self.visit_function_kind(kind)?;
        let type_bounds = self.visit_generic_bounds(typ_bounds)?;
        self.push_scope();
        let params = self.visit_params(ps)?;
        for p in R::get_vec_or(&params, ps).iter() {
            let _ = self.insert_binding(
                &p.x.name.clone(),
                ScopeEntry::new_outer_param_ret(&p.x.typ, p.x.is_mut, true),
            );
        }
        let ret = self.visit_param(rt)?;
        let require = self.visit_exprs(require)?;

        self.push_scope();
        if function.x.ens_has_return {
            let r = R::get_or(&ret, rt);
            let _ = self.insert_binding(
                &r.x.name.clone(),
                ScopeEntry::new_outer_param_ret(&r.x.typ, false, true),
            );
        }
        let ensure0 = self.visit_exprs(ensure0)?;
        let ensure1 = self.visit_exprs(ensure1)?;
        self.pop_scope();

        let returns = self.visit_opt_expr(returns)?;
        let decrease = self.visit_exprs(decrease)?;
        let decrease_when = self.visit_opt_expr(decrease_when)?;
        let mask_spec = R::map_opt(mask_spec, &mut |ms| self.visit_mask_spec(ms))?;
        let unwind_spec = R::map_opt(unwind_spec, &mut |us| self.visit_unwind_spec(us))?;
        let body = self.visit_opt_expr(body)?;
        self.pop_scope();

        let fndef_axioms = self.visit_opt_exprs(fndef_axioms)?;
        R::ret(|| {
            function.new_x(FunctionX {
                name: name.clone(),
                proxy: proxy.clone(),
                kind: R::get(kind),
                visibility: visibility.clone(),
                body_visibility: body_visibility.clone(),
                opaqueness: opaqueness.clone(),
                owning_module: owning_module.clone(),
                mode: *mode,
                typ_params: typ_params.clone(),
                typ_bounds: R::get_vec_a(type_bounds),
                params: R::get_vec_a(params),
                ret: R::get(ret),
                ens_has_return: *ens_has_return,
                require: R::get_vec_a(require),
                ensure: (R::get_vec_a(ensure0), R::get_vec_a(ensure1)),
                returns: R::get_opt(returns),
                decrease: R::get_vec_a(decrease),
                decrease_when: R::get_opt(decrease_when),
                decrease_by: decrease_by.clone(),
                fndef_axioms: R::get_opt(fndef_axioms),
                mask_spec: R::get_opt(mask_spec),
                unwind_spec: R::get_opt(unwind_spec),
                item_kind: item_kind.clone(),
                attrs: attrs.clone(),
                body: R::get_opt(body),
                extra_dependencies: extra_dependencies.clone(),
            })
        })
    }

    fn visit_field(&mut self, field: &Field) -> Result<R::Ret<Field>, Err> {
        let (typ, mode, visibility) = &field.a;
        let typ = self.visit_typ(typ)?;
        R::ret(|| field.new_a((R::get(typ), *mode, visibility.clone())))
    }

    fn visit_fields(&mut self, fields: &Vec<Field>) -> Result<R::Vec<Field>, Err> {
        R::map_vec(fields, &mut |b| self.visit_field(b))
    }

    fn visit_variant(&mut self, variant: &Variant) -> Result<R::Ret<Variant>, Err> {
        let fields = self.visit_fields(&variant.fields)?;
        R::ret(|| Variant {
            name: variant.name.clone(),
            fields: R::get_vec_a(fields),
            ctor_style: variant.ctor_style.clone(),
        })
    }

    fn visit_variants(&mut self, variants: &Vec<Variant>) -> Result<R::Vec<Variant>, Err> {
        R::map_vec(variants, &mut |v| self.visit_variant(v))
    }

    fn visit_datatype(&mut self, datatype: &Datatype) -> Result<R::Ret<Datatype>, Err> {
        let DatatypeX {
            name,
            proxy,
            owning_module,
            visibility,
            transparency,
            typ_params,
            typ_bounds,
            variants,
            mode,
            ext_equal,
            user_defined_invariant_fn,
            sized_constraint,
            destructor,
        } = &datatype.x;
        let type_bounds = self.visit_generic_bounds(typ_bounds)?;
        let variants = self.visit_variants(variants)?;
        let sized_constraint = R::map_opt(sized_constraint, &mut |t| self.visit_typ(t))?;
        R::ret(|| {
            datatype.new_x(DatatypeX {
                name: name.clone(),
                proxy: proxy.clone(),
                owning_module: owning_module.clone(),
                visibility: visibility.clone(),
                transparency: transparency.clone(),
                typ_params: typ_params.clone(),
                typ_bounds: R::get_vec_a(type_bounds),
                variants: R::get_vec_a(variants),
                mode: *mode,
                ext_equal: *ext_equal,
                user_defined_invariant_fn: user_defined_invariant_fn.clone(),
                sized_constraint: R::get_opt(sized_constraint),
                destructor: *destructor,
            })
        })
    }

    #[allow(dead_code)]
    fn visit_trait(&mut self, tr: &Trait) -> Result<R::Ret<Trait>, Err> {
        let TraitX {
            name,
            proxy,
            visibility,
            typ_params,
            typ_bounds,
            assoc_typs,
            assoc_typs_bounds,
            methods,
            is_unsafe,
            dyn_compatible,
            external_trait_extension,
        } = &tr.x;
        let type_bounds = self.visit_generic_bounds(typ_bounds)?;
        let assoc_typs_bounds = self.visit_generic_bounds(assoc_typs_bounds)?;
        R::ret(|| {
            tr.new_x(TraitX {
                name: name.clone(),
                proxy: proxy.clone(),
                visibility: visibility.clone(),
                typ_params: typ_params.clone(),
                typ_bounds: R::get_vec_a(type_bounds),
                assoc_typs: assoc_typs.clone(),
                assoc_typs_bounds: R::get_vec_a(assoc_typs_bounds),
                methods: methods.clone(),
                is_unsafe: *is_unsafe,
                dyn_compatible: dyn_compatible.clone(),
                external_trait_extension: external_trait_extension.clone(),
            })
        })
    }

    fn visit_assoc_type_impl(&mut self, imp: &AssocTypeImpl) -> Result<R::Ret<AssocTypeImpl>, Err> {
        let AssocTypeImplX {
            name,
            impl_path,
            typ_params,
            typ_bounds,
            trait_path,
            trait_typ_args,
            typ,
            impl_paths,
        } = &imp.x;
        let type_bounds = self.visit_generic_bounds(typ_bounds)?;
        let trait_typ_args = self.visit_typs(trait_typ_args)?;
        let typ = self.visit_typ(typ)?;
        R::ret(|| {
            imp.new_x(AssocTypeImplX {
                name: name.clone(),
                impl_path: impl_path.clone(),
                typ_params: typ_params.clone(),
                typ_bounds: R::get_vec_a(type_bounds),
                trait_path: trait_path.clone(),
                trait_typ_args: R::get_vec_a(trait_typ_args),
                typ: R::get(typ),
                impl_paths: impl_paths.clone(),
            })
        })
    }

    fn visit_trait_impl(&mut self, imp: &TraitImpl) -> Result<R::Ret<TraitImpl>, Err> {
        let TraitImplX {
            impl_path,
            typ_params,
            typ_bounds,
            trait_path,
            trait_typ_args,
            trait_typ_arg_impls,
            owning_module,
            auto_imported,
            external_trait_blanket,
        } = &imp.x;
        let type_bounds = self.visit_generic_bounds(typ_bounds)?;
        let trait_typ_args = self.visit_typs(trait_typ_args)?;
        R::ret(|| {
            imp.new_x(TraitImplX {
                impl_path: impl_path.clone(),
                typ_params: typ_params.clone(),
                typ_bounds: R::get_vec_a(type_bounds),
                trait_path: trait_path.clone(),
                trait_typ_args: R::get_vec_a(trait_typ_args),
                trait_typ_arg_impls: trait_typ_arg_impls.clone(),
                owning_module: owning_module.clone(),
                auto_imported: *auto_imported,
                external_trait_blanket: *external_trait_blanket,
            })
        })
    }

    fn visit_krate(&mut self, krate: &Krate) -> Result<R::Ret<Krate>, Err> {
        let KrateX {
            functions,
            reveal_groups,
            datatypes,
            traits,
            trait_impls,
            assoc_type_impls,
            modules,
            external_fns,
            external_types,
            path_as_rust_names,
            arch,
            opaque_types,
        } = &**krate;
        let functions = R::map_vec(functions, &mut |f| self.visit_function(f))?;
        let datatypes = R::map_vec(datatypes, &mut |d| self.visit_datatype(d))?;
        let traits = R::map_vec(traits, &mut |t| self.visit_trait(t))?;
        let trait_impls = R::map_vec(trait_impls, &mut |ti| self.visit_trait_impl(ti))?;
        let assoc_type_impls =
            R::map_vec(assoc_type_impls, &mut |ati| self.visit_assoc_type_impl(ati))?;
        R::ret(|| {
            Arc::new(KrateX {
                functions: R::get_vec(functions),
                reveal_groups: reveal_groups.clone(),
                datatypes: R::get_vec(datatypes),
                traits: R::get_vec(traits),
                trait_impls: R::get_vec(trait_impls),
                assoc_type_impls: R::get_vec(assoc_type_impls),
                modules: modules.clone(),
                external_fns: external_fns.clone(),
                external_types: external_types.clone(),
                path_as_rust_names: path_as_rust_names.clone(),
                arch: arch.clone(),
                opaque_types: opaque_types.clone(),
            })
        })
    }
}

pub(crate) fn typ_visitor_check<E, MF>(typ: &Typ, mf: &mut MF) -> Result<(), E>
where
    MF: FnMut(&Typ) -> Result<(), E>,
{
    match typ_visitor_dfs(typ, &mut |typ| match mf(typ) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

struct TypVisitorDfs<'a, FT>(&'a mut FT);

impl<'a, T, FT> AstVisitor<Walk, T, NoScoper> for TypVisitorDfs<'a, FT>
where
    FT: FnMut(&Typ) -> VisitorControlFlow<T>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<(), T> {
        match (self.0)(typ) {
            VisitorControlFlow::Stop(val) => Err(val),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Recurse => self.visit_typ_rec(typ),
        }
    }
}

pub(crate) fn typ_visitor_dfs<T, FT>(typ: &Typ, ft: &mut FT) -> VisitorControlFlow<T>
where
    FT: FnMut(&Typ) -> VisitorControlFlow<T>,
{
    let mut visitor = TypVisitorDfs(ft);
    match visitor.visit_typ(typ) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(val) => VisitorControlFlow::Stop(val),
    }
}

pub(crate) struct WalkTypVisitorEnv<'a, E, FT> {
    pub(crate) env: &'a mut E,
    pub(crate) ft: &'a FT,
}

impl<'a, E, FT> AstVisitor<Walk, VirErr, NoScoper> for WalkTypVisitorEnv<'a, E, FT>
where
    FT: Fn(&mut E, &Typ) -> Result<(), VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<(), VirErr> {
        self.visit_typ_rec(typ)?;
        (self.ft)(&mut self.env, typ)
    }

    fn visit_expr(&mut self, expr: &Expr) -> Result<(), VirErr> {
        self.visit_expr_rec(expr)
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), VirErr> {
        self.visit_stmt_rec(stmt)
    }

    fn visit_place(&mut self, place: &Place) -> Result<(), VirErr> {
        self.visit_place_rec(place)
    }

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<(), VirErr> {
        self.visit_pattern_rec(pattern)
    }
}

struct MapTypVisitorEnv<'a, E, FT> {
    env: &'a mut E,
    ft: &'a FT,
}

impl<'a, E, FT> AstVisitor<Rewrite, VirErr, NoScoper> for MapTypVisitorEnv<'a, E, FT>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        let typ = self.visit_typ_rec(typ)?;
        (self.ft)(&mut self.env, &typ)
    }
}

pub(crate) fn map_typ_visitor_env<E, FT>(typ: &Typ, env: &mut E, ft: &FT) -> Result<Typ, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    visitor.visit_typ(typ)
}

#[allow(dead_code)]
pub(crate) fn map_typs_visitor_env<E, FT>(typs: &Typs, env: &mut E, ft: &FT) -> Result<Typs, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    Ok(Arc::new(visitor.visit_typs(typs)?))
}

struct MapTypVisitor<'a, FT>(&'a FT);

impl<'a, FT> AstVisitor<Rewrite, VirErr, NoScoper> for MapTypVisitor<'a, FT>
where
    FT: Fn(&Typ) -> Result<Typ, VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        let typ = self.visit_typ_rec(typ)?;
        (self.0)(&typ)
    }
}

pub(crate) fn map_typ_visitor<FT>(typ: &Typ, ft: &FT) -> Result<Typ, VirErr>
where
    FT: Fn(&Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitor(ft);
    visitor.visit_typ(typ)
}

fn insert_pattern_vars(map: &mut VisitorScopeMap, pattern: &Pattern, init: bool) {
    match &pattern.x {
        PatternX::Wildcard(_) => {}
        PatternX::Var(PatternBinding { name, mutable, by_ref: _, typ, copy: _ }) => {
            let _ = map.insert(name.clone(), ScopeEntry::new(typ, *mutable, init));
        }
        PatternX::Binding {
            binding: PatternBinding { name, mutable, by_ref: _, typ, copy: _ },
            sub_pat,
        } => {
            insert_pattern_vars(map, sub_pat, init);
            let _ = map.insert(name.clone(), ScopeEntry::new(typ, *mutable, init));
        }
        PatternX::Constructor(_, _, binders) => {
            for binder in binders.iter() {
                insert_pattern_vars(map, &binder.a, init);
            }
        }
        PatternX::Or(pat1, _) => {
            insert_pattern_vars(map, pat1, init);
            // pat2 should bind an identical set of variables
        }
        PatternX::Expr(_) => {}
        PatternX::Range(_, _) => {}
        PatternX::MutRef(pat1) | PatternX::ImmutRef(pat1) => {
            insert_pattern_vars(map, pat1, init);
        }
    }
}

/// Walk the AST, visit every Expr, Stmt, Pattern, Typ

pub(crate) fn ast_visitor_check_with_scope_map<ERR, E, FE, FS, FP, FT, FPL>(
    expr: &Expr,
    scope_map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &mut FE,
    fs: &mut FS,
    fp: &mut FP,
    ft: &mut FT,
    fpl: &mut FPL,
) -> Result<(), ERR>
where
    FE: FnMut(&mut E, &VisitorScopeMap, &Expr) -> Result<(), ERR>,
    FS: FnMut(&mut E, &VisitorScopeMap, &Stmt) -> Result<(), ERR>,
    FP: FnMut(&mut E, &VisitorScopeMap, &Pattern) -> Result<(), ERR>,
    FT: FnMut(&mut E, &VisitorScopeMap, &Typ, &Span) -> Result<(), ERR>,
    FPL: FnMut(&mut E, &VisitorScopeMap, &Place) -> Result<(), ERR>,
{
    match ast_visitor_dfs(
        expr,
        scope_map,
        env,
        &mut |env, scope_map, x| match fe(env, scope_map, x) {
            Ok(()) => VisitorControlFlow::Recurse,
            Err(e) => VisitorControlFlow::Stop(e),
        },
        &mut |env, scope_map, x| match fs(env, scope_map, x) {
            Ok(()) => VisitorControlFlow::Recurse,
            Err(e) => VisitorControlFlow::Stop(e),
        },
        &mut |env, scope_map, x| match fp(env, scope_map, x) {
            Ok(()) => VisitorControlFlow::Recurse,
            Err(e) => VisitorControlFlow::Stop(e),
        },
        &mut |env, scope_map, x, span| match ft(env, scope_map, x, span) {
            Ok(()) => VisitorControlFlow::Recurse,
            Err(e) => VisitorControlFlow::Stop(e),
        },
        &mut |env, scope_map, x| match fpl(env, scope_map, x) {
            Ok(()) => VisitorControlFlow::Recurse,
            Err(e) => VisitorControlFlow::Stop(e),
        },
    ) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

pub(crate) fn ast_visitor_check<ERR, E, FE, FS, FP, FT, FPL>(
    expr: &Expr,
    env: &mut E,
    fe: &mut FE,
    fs: &mut FS,
    fp: &mut FP,
    ft: &mut FT,
    fpl: &mut FPL,
) -> Result<(), ERR>
where
    FE: FnMut(&mut E, &VisitorScopeMap, &Expr) -> Result<(), ERR>,
    FS: FnMut(&mut E, &VisitorScopeMap, &Stmt) -> Result<(), ERR>,
    FP: FnMut(&mut E, &VisitorScopeMap, &Pattern) -> Result<(), ERR>,
    FT: FnMut(&mut E, &VisitorScopeMap, &Typ, &Span) -> Result<(), ERR>,
    FPL: FnMut(&mut E, &VisitorScopeMap, &Place) -> Result<(), ERR>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    ast_visitor_check_with_scope_map(expr, &mut scope_map, env, fe, fs, fp, ft, fpl)
}

struct WalkAstVisitor<'a, E, FE, FS, FP, FT, FPL> {
    env: &'a mut E,
    fe: &'a mut FE,
    fs: &'a mut FS,
    fp: &'a mut FP,
    ft: &'a mut FT,
    fpl: &'a mut FPL,
    map: &'a mut VisitorScopeMap,
    // Since types don't have spans, keep track of the best span as we descend
    most_specific_span: Span,
}

impl<'a, E, FE, FS, FP, FT, FPL, T> AstVisitor<Walk, T, VisitorScopeMap>
    for WalkAstVisitor<'a, E, FE, FS, FP, FT, FPL>
where
    FE: FnMut(&mut E, &mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
    FS: FnMut(&mut E, &mut VisitorScopeMap, &Stmt) -> VisitorControlFlow<T>,
    FP: FnMut(&mut E, &mut VisitorScopeMap, &Pattern) -> VisitorControlFlow<T>,
    FT: FnMut(&mut E, &mut VisitorScopeMap, &Typ, &Span) -> VisitorControlFlow<T>,
    FPL: FnMut(&mut E, &mut VisitorScopeMap, &Place) -> VisitorControlFlow<T>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<(), T> {
        match (self.ft)(&mut self.env, self.map, typ, &self.most_specific_span) {
            VisitorControlFlow::Recurse => self.visit_typ_rec(typ),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Stop(err) => Err(err),
        }
    }

    fn visit_expr(&mut self, expr: &Expr) -> Result<(), T> {
        self.most_specific_span = expr.span.clone();
        match (self.fe)(&mut self.env, self.map, expr) {
            VisitorControlFlow::Recurse => self.visit_expr_rec(expr),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Stop(err) => Err(err),
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), T> {
        self.most_specific_span = stmt.span.clone();
        match (self.fs)(&mut self.env, self.map, stmt) {
            VisitorControlFlow::Recurse => self.visit_stmt_rec(stmt),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Stop(err) => Err(err),
        }
    }

    fn visit_place(&mut self, place: &Place) -> Result<(), T> {
        self.most_specific_span = place.span.clone();
        match (self.fpl)(&mut self.env, self.map, place) {
            VisitorControlFlow::Recurse => self.visit_place_rec(place),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Stop(err) => Err(err),
        }
    }

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<(), T> {
        self.most_specific_span = pattern.span.clone();
        match (self.fp)(&mut self.env, self.map, pattern) {
            VisitorControlFlow::Recurse => self.visit_pattern_rec(pattern),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Stop(err) => Err(err),
        }
    }

    fn scoper(&mut self) -> Option<&mut VisitorScopeMap> {
        Some(self.map)
    }
}

pub(crate) fn ast_visitor_dfs<T, E, FE, FS, FP, FT, FPL>(
    expr: &Expr,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &mut FE,
    fs: &mut FS,
    fp: &mut FP,
    ft: &mut FT,
    fpl: &mut FPL,
) -> VisitorControlFlow<T>
where
    FE: FnMut(&mut E, &mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
    FS: FnMut(&mut E, &mut VisitorScopeMap, &Stmt) -> VisitorControlFlow<T>,
    FP: FnMut(&mut E, &mut VisitorScopeMap, &Pattern) -> VisitorControlFlow<T>,
    FT: FnMut(&mut E, &mut VisitorScopeMap, &Typ, &Span) -> VisitorControlFlow<T>,
    FPL: FnMut(&mut E, &mut VisitorScopeMap, &Place) -> VisitorControlFlow<T>,
{
    let mut vis =
        WalkAstVisitor { env, fe, fs, fp, ft, fpl, map, most_specific_span: expr.span.clone() };
    match vis.visit_expr(expr) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(t) => VisitorControlFlow::Stop(t),
    }
}

/// Walk the AST, visit every Expr

pub(crate) fn expr_visitor_check<E, MF>(expr: &Expr, mf: &mut MF) -> Result<(), E>
where
    MF: FnMut(&VisitorScopeMap, &Expr) -> Result<(), E>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    match expr_visitor_dfs(expr, &mut scope_map, &mut |scope_map, expr| match mf(scope_map, expr) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

struct WalkExprVisitor<'a, MF> {
    mf: &'a mut MF,
    map: &'a mut VisitorScopeMap,
}

impl<'a, MF, T> AstVisitor<Walk, T, VisitorScopeMap> for WalkExprVisitor<'a, MF>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    fn visit_typ(&mut self, _typ: &Typ) -> Result<(), T> {
        Ok(())
        // do nothing
    }

    fn visit_expr(&mut self, expr: &Expr) -> Result<(), T> {
        match (self.mf)(self.map, expr) {
            VisitorControlFlow::Recurse => self.visit_expr_rec(expr),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Stop(err) => Err(err),
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), T> {
        self.visit_stmt_rec(stmt)
    }

    fn visit_place(&mut self, place: &Place) -> Result<(), T> {
        self.visit_place_rec(place)
    }

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<(), T> {
        self.visit_pattern_rec(pattern)
    }

    fn scoper(&mut self) -> Option<&mut VisitorScopeMap> {
        Some(self.map)
    }
}

pub(crate) fn expr_visitor_dfs<T, MF>(
    expr: &Expr,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    let mut vis = WalkExprVisitor { mf, map };
    match vis.visit_expr(expr) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(t) => VisitorControlFlow::Stop(t),
    }
}

pub(crate) fn expr_visitor_walk<MF>(expr: &Expr, mf: &mut MF)
where
    MF: FnMut(&Expr) -> VisitorControlFlow<()>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    expr_visitor_dfs(expr, &mut scope_map, &mut |_scope_map, expr| mf(expr));
}

pub(crate) fn function_visitor_dfs<T, MF>(
    function: &Function,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    let mut vis = WalkExprVisitor { mf, map };
    match vis.visit_function(function) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(t) => VisitorControlFlow::Stop(t),
    }
}

pub(crate) fn function_visitor_check<E, MF>(function: &Function, mf: &mut MF) -> Result<(), E>
where
    MF: FnMut(&Expr) -> Result<(), E>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    match function_visitor_dfs(function, &mut scope_map, &mut |_scope_map, expr| match mf(expr) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

struct MapExprStmtTypVisitor<'a, E, FE, FS, FT, FPL> {
    env: &'a mut E,
    fe: &'a FE,
    fs: &'a FS,
    ft: &'a FT,
    fpl: &'a FPL,
    map: &'a mut VisitorScopeMap,
}

impl<'a, E, FE, FS, FT, FPL> AstVisitor<Rewrite, VirErr, VisitorScopeMap>
    for MapExprStmtTypVisitor<'a, E, FE, FS, FT, FPL>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
    FPL: Fn(&mut E, &mut VisitorScopeMap, &Place) -> Result<Place, VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        let typ = self.visit_typ_rec(typ)?;
        let typ = (self.ft)(self.env, &typ)?;
        Ok(typ)
    }

    fn visit_expr(&mut self, expr: &Expr) -> Result<Expr, VirErr> {
        let expr = self.visit_expr_rec(expr)?;
        let expr = (self.fe)(self.env, self.map, &expr)?;
        Ok(expr)
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<Vec<Stmt>, VirErr> {
        let stmt = self.visit_stmt_rec(stmt)?;
        let stmt = (self.fs)(self.env, self.map, &stmt)?;
        Ok(stmt)
    }

    fn visit_place(&mut self, place: &Place) -> Result<Place, VirErr> {
        let place = self.visit_place_rec(place)?;
        let place = (self.fpl)(self.env, self.map, &place)?;
        Ok(place)
    }

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<Pattern, VirErr> {
        let pattern = self.visit_pattern_rec(pattern)?;
        Ok(pattern)
    }

    fn scoper(&mut self) -> Option<&mut VisitorScopeMap> {
        Some(self.map)
    }
}

pub(crate) fn map_expr_visitor_env<E, FE, FS, FT, FPL>(
    expr: &Expr,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
    fpl: &FPL,
) -> Result<Expr, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
    FPL: Fn(&mut E, &mut VisitorScopeMap, &Place) -> Result<Place, VirErr>,
{
    let mut vis = MapExprStmtTypVisitor { env, fe, fs, ft, fpl, map };
    vis.visit_expr(expr)
}

pub fn map_expr_visitor<FE>(expr: &Expr, fe: &FE) -> Result<Expr, VirErr>
where
    FE: Fn(&Expr) -> Result<Expr, VirErr>,
{
    map_expr_visitor_env(
        expr,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_state, _, expr| fe(expr),
        &|_state, _, stmt| Ok(vec![stmt.clone()]),
        &|_state, typ| Ok(typ.clone()),
        &|_state, _, place| Ok(place.clone()),
    )
}

pub fn map_expr_place_visitor<FE, FPL>(expr: &Expr, fe: &FE, fpl: &FPL) -> Result<Expr, VirErr>
where
    FE: Fn(&Expr) -> Result<Expr, VirErr>,
    FPL: Fn(&Place) -> Result<Place, VirErr>,
{
    map_expr_visitor_env(
        expr,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_state, _, expr| fe(expr),
        &|_state, _, stmt| Ok(vec![stmt.clone()]),
        &|_state, typ| Ok(typ.clone()),
        &|_state, _, place| fpl(place),
    )
}

pub(crate) fn map_param_visitor<E, FT>(param: &Param, env: &mut E, ft: &FT) -> Result<Param, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    visitor.visit_param(param)
}

pub(crate) fn map_params_visitor<E, FT>(
    params: &Params,
    env: &mut E,
    ft: &FT,
) -> Result<Params, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    Ok(Arc::new(vec_map_result(params, |p| map_param_visitor(p, env, ft))?))
}

pub(crate) fn map_generic_bound_visitor<E, FT>(
    bound: &GenericBound,
    env: &mut E,
    ft: &FT,
) -> Result<GenericBound, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    visitor.visit_generic_bound(bound)
}

pub(crate) fn map_generic_bounds_visitor<E, FT>(
    bounds: &crate::ast::GenericBounds,
    env: &mut E,
    ft: &FT,
) -> Result<crate::ast::GenericBounds, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    Ok(Arc::new(vec_map_result(&**bounds, |b| map_generic_bound_visitor(b, env, ft))?))
}

pub(crate) fn map_function_visitor_env<E, FE, FS, FT, FPL>(
    function: &Function,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
    fpl: &FPL,
) -> Result<Function, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
    FPL: Fn(&mut E, &mut VisitorScopeMap, &Place) -> Result<Place, VirErr>,
{
    let mut vis = MapExprStmtTypVisitor { env, fe, fs, ft, fpl, map };
    vis.visit_function(function)
}

pub(crate) fn map_datatype_visitor_env<E, FT>(
    datatype: &Datatype,
    env: &mut E,
    ft: &FT,
) -> Result<Datatype, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    visitor.visit_datatype(datatype)
}

pub(crate) fn map_trait_impl_visitor_env<E, FT>(
    imp: &TraitImpl,
    env: &mut E,
    ft: &FT,
) -> Result<TraitImpl, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    visitor.visit_trait_impl(imp)
}

pub(crate) fn map_assoc_type_impl_visitor_env<E, FT>(
    assoc: &AssocTypeImpl,
    env: &mut E,
    ft: &FT,
) -> Result<AssocTypeImpl, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    visitor.visit_assoc_type_impl(assoc)
}
