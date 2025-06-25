use crate::ast::{
    Arm, ArmX, Arms, AssocTypeImpl, AssocTypeImplX, CallTarget, CallTargetKind, Datatype, DatatypeX, Expr, ExprX, Field,
    Function, FunctionKind, FunctionX, GenericBound, GenericBoundX, MaskSpec, Param, ParamX,
    Params, Pattern, PatternX, SpannedTyped, Stmt, StmtX, TraitImpl, TraitImplX, Typ,
    TypDecorationArg, TypX, Typs, UnaryOpr, UnwindSpec, VarIdent, Variant, VirErr,
    NullaryOpr, BinaryOpr, VarBinder, VarBinders, VarBinderX,
    LoopInvariants, LoopInvariant, Exprs,
};
use crate::def::Spanned;
use crate::util::vec_map_result;
use crate::visitor::expr_visitor_control_flow;
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
    fn new(typ: &Typ, is_mut: bool, init: bool) -> Self {
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
            R::ret(|| Arc::new(R::get_vec(es)))
        })
    }

    fn visit_opt_expr(&mut self, expr_opt: &Option<Expr>) -> Result<R::Opt<Expr>, Err> {
        R::map_opt(expr_opt, &mut |e| self.visit_expr(e))
    }

    fn visit_binders_expr(&mut self, binders: &air::ast::Binders<Expr>) -> Result<R::Vec<air::ast::Binder<Expr>>, Err> {
        R::map_vec(binders, &mut |b| {
            let air::ast::BinderX { name, a } = &**b;
            let a = self.visit_expr(a)?;
            R::ret(|| Arc::new(air::ast::BinderX { name: name.clone(), a: R::get(a) }))
        })
    }

    fn visit_binders_pattern(&mut self, binders: &air::ast::Binders<Pattern>) -> Result<R::Vec<air::ast::Binder<Pattern>>, Err> {
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

    fn visit_binders_typ(&mut self, binders: &VarBinders<Typ>) -> Result<R::Vec<VarBinder<Typ>>, Err> {
        R::map_vec(binders, &mut |b| self.visit_binder_typ(b))
    }

    fn visit_call_target_kind(&mut self, call_target_kind: &CallTargetKind) -> Result<R::Ret<CallTargetKind>, Err> {
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
        }
    }

    fn visit_call_target(&mut self, call_target: &CallTarget) -> Result<R::Ret<CallTarget>, Err> {
        match call_target {
            CallTarget::Fun(kind, fun, typs, impl_paths, au) => {
                let kind = self.visit_call_target_kind(kind)?;
                let typs = self.visit_typs(typs)?;
                R::ret(|| CallTarget::Fun(R::get(kind), fun.clone(), R::get_vec_a(typs), impl_paths.clone(), au.clone()))
            }
            CallTarget::FnSpec(expr) => {
                let e = self.visit_expr(expr)?;
                R::ret(|| CallTarget::FnSpec(R::get(e)))
            }
            CallTarget::BuiltinSpecFun(bsf, typs, impl_paths) => {
                let typs = self.visit_typs(typs)?;
                R::ret(|| CallTarget::BuiltinSpecFun(bsf.clone(), R::get_vec_a(typs), impl_paths.clone()))
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
                R::ret(|| NullaryOpr::TypEqualityBound(path.clone(), R::get_vec_a(ts), id.clone(), R::get(t)))
            }
            NullaryOpr::ConstTypBound(t1, t2) => {
                let t1 = self.visit_typ(t1)?;
                let t2 = self.visit_typ(t2)?;
                R::ret(|| NullaryOpr::ConstTypBound(R::get(t1), R::get(t2)))
            }
            NullaryOpr::NoInferSpecForLoopIter => {
                R::ret(|| nopr.clone())
            }
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
            ExprX::Const(_) => R::ret(|| expr.clone()),
            ExprX::Var(_) => R::ret(|| expr.clone()),
            ExprX::VarLoc(_) => R::ret(|| expr.clone()),
            ExprX::VarAt(_, _) => R::ret(|| expr.clone()),
            ExprX::ConstVar(_, _) => R::ret(|| expr.clone()),
            ExprX::StaticVar(_) => R::ret(|| expr.clone()),
            ExprX::Loc(e) => {
                let e1 = self.visit_expr(e)?;
                R::ret(|| expr_new(ExprX::Loc(R::get(e1))))
            }
            ExprX::Call(call_target, exprs) => {
                let ct = self.visit_call_target(call_target)?;
                let es = self.visit_exprs(exprs)?;
                R::ret(|| expr_new(ExprX::Call(R::get(ct), R::get_vec_a(es))))
            }
            ExprX::Ctor(dt, id, binders, opt_e) => {
                let bs = self.visit_binders_expr(binders)?;
                let oe = self.visit_opt_expr(opt_e)?;
                R::ret(|| expr_new(ExprX::Ctor(dt.clone(), id.clone(), R::get_vec_a(bs), R::get_opt(oe))))
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

                R::ret(|| expr_new(ExprX::NonSpecClosure {
                    params: R::get_vec_a(params),
                    proof_fn_modes: proof_fn_modes.clone(),
                    body: R::get(body),
                    requires: R::get_vec_a(requires),
                    ensures: R::get_vec_a(ensures),
                    ret: R::get(ret),
                    external_spec: R::get_opt(external_spec),
                }))
            }
            ExprX::ArrayLiteral(es) => {
                let es = self.visit_exprs(es)?;
                R::ret(|| expr_new(ExprX::ArrayLiteral(R::get_vec_a(es))))
            }
            ExprX::ExecFnByName(_fun) => R::ret(|| expr.clone()),
            ExprX::Choose { params: bs, cond, body } => {
                let binders = self.visit_binders_typ(bs)?;
                self.push_scope();
                for b in R::get_vec_or(&binders, bs).iter() {
                    self.insert_binding(&b.name, ScopeEntry::new(&b.a, false, true));
                }
                let cond = self.visit_expr(cond)?;
                let body = self.visit_expr(body)?;
                self.pop_scope();
                R::ret(|| expr_new(ExprX::Choose {
                    params: R::get_vec_a(binders),
                    cond: R::get(cond),
                    body: R::get(body),
                }))
            }
            ExprX::WithTriggers { triggers, body } => {
                let triggers = self.visit_exprs_vec(triggers)?;
                let body = self.visit_expr(body)?;
                R::ret(|| expr_new(ExprX::WithTriggers {
                    triggers: R::get_vec_a(triggers),
                    body: R::get(body),
                }))
            }
            ExprX::Assign { init_not_mut, lhs, rhs, op } => {
                let lhs = self.visit_expr(lhs)?;
                let rhs = self.visit_expr(rhs)?;
                R::ret(|| expr_new(ExprX::Assign {
                    init_not_mut: *init_not_mut,
                    lhs: R::get(lhs),
                    rhs: R::get(rhs),
                    op: *op,
                }))
            }
            ExprX::Fuel(_fun, _fuel, _is_broadcast_use) => R::ret(|| expr.clone()),
            ExprX::RevealString(_s) => R::ret(|| expr.clone()),
            ExprX::Header(_) => {
                // don't descend into Headers
                R::ret(|| expr.clone())
            }
            ExprX::AssertAssume { is_assume, expr } => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| expr_new(ExprX::AssertAssume { is_assume: *is_assume, expr: R::get(expr) }))
            }
            ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume, expr, fun } => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| expr_new(ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: *is_assume, expr: R::get(expr), fun: fun.clone() }))
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
                R::ret(|| expr_new(ExprX::AssertBy {
                    vars: R::get_vec_a(binders),
                    require: R::get(require),
                    ensure: R::get(ensure),
                    proof: R::get(proof),
                }))
            }
            ExprX::AssertQuery { requires, ensures, proof, mode } => {
                let requires = self.visit_exprs(requires)?;
                let ensures = self.visit_exprs(ensures)?;
                let proof = self.visit_expr(proof)?;
                R::ret(|| expr_new(ExprX::AssertQuery {
                    requires: R::get_vec_a(requires),
                    ensures: R::get_vec_a(ensures),
                    proof: R::get(proof),
                    mode: *mode,
                }))
            }
            ExprX::AssertCompute(expr, compute_mode) => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| expr_new(ExprX::AssertCompute(
                    R::get(expr), *compute_mode
                )))
            }
            ExprX::If(cond, thn, els) => {
                let cond = self.visit_expr(cond)?;
                let thn = self.visit_expr(thn)?;
                let els = self.visit_opt_expr(els)?;
                R::ret(|| expr_new(ExprX::If(R::get(cond), R::get(thn), R::get_opt(els))))
            }
            ExprX::Match(expr, arms) => {
                let expr = self.visit_expr(expr)?;
                let arms = self.visit_arms(arms)?;
                R::ret(|| expr_new(ExprX::Match(R::get(expr), R::get_vec_a(arms))))
            }
            ExprX::Loop {
                loop_isolation,
                is_for_loop,
                label,
                cond,
                body,
                invs,
                decrease,
            } => {
                let cond = self.visit_opt_expr(cond)?;
                let body = self.visit_expr(body)?;
                let invs = self.visit_loop_invariants(invs)?;
                let decrease = self.visit_exprs(decrease)?;
                R::ret(|| expr_new(ExprX::Loop {
                    loop_isolation: *loop_isolation,
                    is_for_loop: *is_for_loop,
                    label: label.clone(),
                    cond: R::get_opt(cond),
                    body: R::get(body),
                    invs: R::get_vec_a(invs),
                    decrease: R::get_vec_a(decrease),
                }))
            }
            ExprX::OpenInvariant(e, b, body, ato) => {
                let e = self.visit_expr(e)?;

                let binder = self.visit_binder_typ(b)?;

                self.push_scope();
                let b = R::get_or(&binder, b);
                self.insert_binding(&b.name, ScopeEntry::new(&b.a, true, true));

                let body = self.visit_expr(body)?;

                self.pop_scope();

                R::ret(|| expr_new(ExprX::OpenInvariant(R::get(e), R::get(binder), R::get(body), *ato)))
            }
            ExprX::Return(e) => {
                let e = self.visit_opt_expr(e)?;
                R::ret(|| expr_new(ExprX::Return(R::get_opt(e))))
            }
            ExprX::BreakOrContinue { label: _, is_break: _ } => R::ret(|| expr.clone()),
            ExprX::Ghost { alloc_wrapper, tracked, expr } => {
                let expr = self.visit_expr(expr)?;
                R::ret(|| expr_new(ExprX::Ghost {
                    alloc_wrapper: *alloc_wrapper,
                    tracked: *tracked,
                    expr: R::get(expr),
                }))
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
                            StmtX::Expr(_) => { }
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

                for _i in 0 .. scope_count {
                    self.pop_scope();
                }

                R::ret(|| expr_new(ExprX::Block(R::get_vec_a(stmts), R::get_opt(e))))
            }
            ExprX::AirStmt(_) => R::ret(|| expr.clone()),
            ExprX::NeverToAny(e) => {
                let e = self.visit_expr(e)?;
                R::ret(|| expr_new(ExprX::NeverToAny(R::get(e))))
            }
            ExprX::Nondeterministic => R::ret(|| expr.clone()),
        }
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
        R::ret(|| Spanned::new(arm.span.clone(), ArmX {
            pattern: R::get(pattern),
            guard: R::get(guard),
            body: R::get(body),
        }))
    }

    fn visit_loop_invariants(&mut self, invs: &LoopInvariants) -> Result<R::Vec<LoopInvariant>, Err> {
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
                let init = self.visit_opt_expr(init)?;
                let els = self.visit_opt_expr(els)?;
                R::ret(|| stmt_new(StmtX::Decl {
                    pattern: R::get(pattern),
                    mode: *mode,
                    init: R::get_opt(init),
                    els: R::get_opt(els),
                }))
            }
        }
    }

    fn visit_pattern_rec(&mut self, pattern: &Pattern) -> Result<R::Ret<Pattern>, Err> {
        let typ = self.visit_typ(&pattern.typ)?;
        let pattern_new = |p: PatternX| SpannedTyped::new(&pattern.span, &R::get(typ), p);
        match &pattern.x {
            PatternX::Wildcard(_) => R::ret(|| pattern.clone()),
            PatternX::Var { name: _, mutable: _ } => R::ret(|| pattern.clone()),
            PatternX::Binding { name, mutable, sub_pat } => {
                let sub_pat = self.visit_pattern(sub_pat)?;
                R::ret(|| pattern_new(PatternX::Binding {
                    name: name.clone(),
                    mutable: *mutable,
                    sub_pat: R::get(sub_pat),
                }))
            }
            PatternX::Constructor(dt, ident, bs) => {
                let bs = self.visit_binders_pattern(bs)?;
                R::ret(|| pattern_new(PatternX::Constructor(dt.clone(), ident.clone(), R::get_vec_a(bs))))
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
        }
    }

    fn visit_typs(&mut self, typs: &Vec<Typ>) -> Result<R::Vec<Typ>, Err> {
        R::map_vec(typs, &mut |t| self.visit_typ(t))
    }

    fn visit_typ_rec(&mut self, typ: &Typ) -> Result<R::Ret<Typ>, Err> {
        match &**typ {
            TypX::Bool => R::ret(|| typ.clone()),
            TypX::Int(_) => R::ret(|| typ.clone()),
            TypX::TypParam(_) => R::ret(|| typ.clone()),
            TypX::TypeId => R::ret(|| typ.clone()),
            TypX::ConstInt(_) => R::ret(|| typ.clone()),
            TypX::ConstBool(_) => R::ret(|| typ.clone()),
            TypX::Air(_) => R::ret(|| typ.clone()),
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
        }
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
        PatternX::Var { name, mutable } => {
            let _ = map.insert(name.clone(), ScopeEntry::new(&pattern.typ, *mutable, init));
        }
        PatternX::Binding { name, mutable, sub_pat } => {
            insert_pattern_vars(map, sub_pat, init);
            let _ = map.insert(name.clone(), ScopeEntry::new(&pattern.typ, *mutable, init));
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
    }
}

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

pub(crate) fn expr_visitor_dfs<T, MF>(
    expr: &Expr,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    match mf(map, expr) {
        VisitorControlFlow::Stop(val) => VisitorControlFlow::Stop(val),
        VisitorControlFlow::Return => VisitorControlFlow::Recurse,
        VisitorControlFlow::Recurse => {
            match &expr.x {
                ExprX::Const(_)
                | ExprX::Var(_)
                | ExprX::VarLoc(_)
                | ExprX::VarAt(_, _)
                | ExprX::ConstVar(..)
                | ExprX::StaticVar(..)
                | ExprX::AirStmt(_) => (),
                ExprX::Loc(e) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                }
                ExprX::Call(target, es) => {
                    match target {
                        CallTarget::Fun(_, _, _, _, _) => (),
                        CallTarget::BuiltinSpecFun(_, _, _) => (),
                        CallTarget::FnSpec(fun) => {
                            expr_visitor_control_flow!(expr_visitor_dfs(fun, map, mf));
                        }
                    }
                    for e in es.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                    }
                }
                ExprX::ArrayLiteral(es) => {
                    for e in es.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                    }
                }
                ExprX::Ctor(_path, _ident, binders, update) => {
                    match update {
                        None => (),
                        Some(update) => {
                            expr_visitor_control_flow!(expr_visitor_dfs(update, map, mf))
                        }
                    }
                    for binder in binders.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(&binder.a, map, mf));
                    }
                }
                ExprX::NullaryOpr(_op) => (),
                ExprX::Unary(_op, e1) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::UnaryOpr(_op, e1) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::Binary(_, e1, e2) | ExprX::BinaryOpr(_, e1, e2) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(e2, map, mf));
                }
                ExprX::Multi(_op, es) => {
                    for e in es.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                    }
                }
                ExprX::Quant(_quant, binders, e1) => {
                    map.push_scope(true);
                    for binder in binders.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    map.pop_scope();
                }
                ExprX::Closure(params, body) => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::NonSpecClosure {
                    params,
                    proof_fn_modes: _,
                    ret,
                    requires,
                    ensures,
                    body,
                    external_spec,
                } => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    for req in requires.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(req, map, mf));
                    }
                    map.push_scope(true);
                    let _ = map.insert(ret.name.clone(), ScopeEntry::new(&ret.a, false, true));
                    for ens in ensures.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(ens, map, mf));
                    }
                    map.pop_scope();
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();

                    match external_spec {
                        None => {}
                        Some((cid, cexpr)) => {
                            map.push_scope(true);
                            let _ =
                                map.insert(cid.clone(), ScopeEntry::new(&expr.typ, false, true));
                            expr_visitor_control_flow!(expr_visitor_dfs(&cexpr, map, mf));
                            map.pop_scope();
                        }
                    }
                }
                ExprX::ExecFnByName(_fun) => {}
                ExprX::Choose { params, cond, body } => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(cond, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::WithTriggers { triggers, body } => {
                    for trigger in triggers.iter() {
                        for term in trigger.iter() {
                            expr_visitor_control_flow!(expr_visitor_dfs(term, map, mf));
                        }
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                }
                ExprX::Assign { init_not_mut: _, lhs: e1, rhs: e2, op: _ } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(e2, map, mf));
                }
                ExprX::AssertCompute(e, _) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                }
                ExprX::Fuel(_, _, _) => (),
                ExprX::RevealString(_) => (),
                ExprX::Header(_) => (),
                ExprX::AssertAssume { is_assume: _, expr: e1 } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: _, expr: e1, fun: _ } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::AssertBy { vars, require, ensure, proof } => {
                    map.push_scope(true);
                    for binder in vars.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(require, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(ensure, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(proof, map, mf));
                    map.pop_scope();
                }
                ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
                    for req in requires.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(req, map, mf));
                    }
                    for ens in ensures.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(ens, map, mf));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(proof, map, mf));
                }
                ExprX::If(e1, e2, e3) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(e2, map, mf));
                    if let Some(e3) = &e3 {
                        expr_visitor_control_flow!(expr_visitor_dfs(e3, map, mf));
                    }
                }
                ExprX::Match(e1, arms) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    for arm in arms.iter() {
                        map.push_scope(true);
                        insert_pattern_vars(map, &arm.x.pattern, true);
                        expr_visitor_control_flow!(pat_visitor_dfs(&arm.x.pattern, map, mf));
                        expr_visitor_control_flow!(expr_visitor_dfs(&arm.x.guard, map, mf));
                        expr_visitor_control_flow!(expr_visitor_dfs(&arm.x.body, map, mf));
                        map.pop_scope();
                    }
                }
                ExprX::Loop {
                    loop_isolation: _,
                    is_for_loop: _,
                    label: _,
                    cond,
                    body,
                    invs,
                    decrease,
                } => {
                    if let Some(cond) = cond {
                        expr_visitor_control_flow!(expr_visitor_dfs(cond, map, mf));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    for inv in invs.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(&inv.inv, map, mf));
                    }
                    for dec in decrease.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(dec, map, mf));
                    }
                }
                ExprX::OpenInvariant(inv, binder, body, _atomicity) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(inv, map, mf));
                    map.push_scope(true);
                    let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, true, true));
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::Return(e1) => match e1 {
                    None => (),
                    Some(e) => expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf)),
                },
                ExprX::BreakOrContinue { label: _, is_break: _ } => (),
                ExprX::Ghost { alloc_wrapper: _, tracked: _, expr: e1 } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf))
                }
                ExprX::ProofInSpec(e1) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf))
                }
                ExprX::Block(ss, e1) => {
                    for stmt in ss.iter() {
                        expr_visitor_control_flow!(stmt_visitor_dfs(stmt, map, mf));
                    }
                    match e1 {
                        None => (),
                        Some(e) => expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf)),
                    };
                    for stmt in ss.iter() {
                        match &stmt.x {
                            StmtX::Expr(_) => {}
                            StmtX::Decl { .. } => map.pop_scope(),
                        }
                    }
                }
                ExprX::NeverToAny(e) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf))
                }
                ExprX::Nondeterministic => {}
            }
            VisitorControlFlow::Recurse
        }
    }
}

pub(crate) fn expr_visitor_walk<MF>(expr: &Expr, mf: &mut MF)
where
    MF: FnMut(&Expr) -> VisitorControlFlow<()>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    expr_visitor_dfs(expr, &mut scope_map, &mut |_scope_map, expr| mf(expr));
}

pub(crate) fn stmt_visitor_dfs<T, MF>(
    stmt: &Stmt,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    match &stmt.x {
        StmtX::Expr(e) => {
            expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
        }
        StmtX::Decl { pattern, mode: _, init, els } => {
            map.push_scope(true);
            if let Some(init) = init {
                expr_visitor_control_flow!(expr_visitor_dfs(init, map, mf));
            }
            if let Some(els) = els {
                expr_visitor_control_flow!(expr_visitor_dfs(els, map, mf));
            }
            insert_pattern_vars(map, &pattern, init.is_some());
            expr_visitor_control_flow!(pat_visitor_dfs(&pattern, map, mf));
        }
    }
    VisitorControlFlow::Recurse
}

pub(crate) fn pat_visitor_dfs<T, MF>(
    pat: &Pattern,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    match &pat.x {
        PatternX::Wildcard(_dd) => {}
        PatternX::Var { name: _, mutable: _ } => {}
        PatternX::Binding { name: _, mutable: _, sub_pat } => {
            expr_visitor_control_flow!(pat_visitor_dfs(sub_pat, map, mf));
        }
        PatternX::Constructor(_path, _variant, binders) => {
            for binder in binders.iter() {
                expr_visitor_control_flow!(pat_visitor_dfs(&binder.a, map, mf));
            }
        }
        PatternX::Or(pat1, pat2) => {
            expr_visitor_control_flow!(pat_visitor_dfs(pat1, map, mf));
            expr_visitor_control_flow!(pat_visitor_dfs(pat2, map, mf));
        }
        PatternX::Expr(expr) => {
            expr_visitor_control_flow!(expr_visitor_dfs(expr, map, mf));
        }
        PatternX::Range(expr1, expr2) => {
            if let Some(expr1) = expr1 {
                expr_visitor_control_flow!(expr_visitor_dfs(expr1, map, mf));
            }
            if let Some((expr2, _ineq_op)) = expr2 {
                expr_visitor_control_flow!(expr_visitor_dfs(expr2, map, mf));
            }
        }
    };
    VisitorControlFlow::Recurse
}

pub(crate) fn function_visitor_dfs<T, MF>(
    function: &Function,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    let FunctionX {
        name: _,
        proxy: _,
        kind: _,
        visibility: _,
        body_visibility: _,
        opaqueness: _,
        owning_module: _,
        mode: _,
        typ_params: _,
        typ_bounds: _,
        params,
        ret,
        require,
        ensure,
        ens_has_return: _,
        returns,
        decrease,
        decrease_when,
        decrease_by: _,
        fndef_axioms,
        mask_spec,
        unwind_spec,
        item_kind: _,
        attrs: _,
        body,
        extra_dependencies: _,
    } = &function.x;

    map.push_scope(true);
    for p in params.iter() {
        let _ = map
            .insert(p.x.name.clone(), ScopeEntry::new_outer_param_ret(&p.x.typ, p.x.is_mut, true));
    }
    for e in require.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }

    map.push_scope(true);
    if function.x.ens_has_return {
        let _ = map
            .insert(ret.x.name.clone(), ScopeEntry::new_outer_param_ret(&ret.x.typ, false, true));
    }
    for e in ensure.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    map.pop_scope();

    if let Some(e) = returns {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }

    for e in decrease.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    if let Some(e) = decrease_when {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    match mask_spec {
        None => {}
        Some(MaskSpec::InvariantOpens(_span, es) | MaskSpec::InvariantOpensExcept(_span, es)) => {
            for e in es.iter() {
                expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
            }
        }
        Some(MaskSpec::InvariantOpensSet(e)) => {
            expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf))
        }
    }
    match unwind_spec {
        None => {}
        Some(UnwindSpec::MayUnwind) => {}
        Some(UnwindSpec::NoUnwind) => {}
        Some(UnwindSpec::NoUnwindWhen(e)) => {
            expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
        }
    }

    if let Some(e) = body {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    map.pop_scope();

    if let Some(es) = fndef_axioms {
        for e in es.iter() {
            expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
        }
    }

    VisitorControlFlow::Recurse
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

struct MapExprStmtTypVisitor<'a, E, FE, FS, FT> {
    env: &'a mut E,
    fe: &'a FE,
    fs: &'a FS,
    ft: &'a FT,
    map: &'a mut VisitorScopeMap,
}

impl<'a, E, FE, FS, FT> AstVisitor<Rewrite, VirErr, VisitorScopeMap>
  for MapExprStmtTypVisitor<'a, E, FE, FS, FT>
  where
      FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
      FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
      FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
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

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<Pattern, VirErr> {
        let pattern = self.visit_pattern_rec(pattern)?;
        Ok(pattern)
    }

    fn scoper(&mut self) -> Option<&mut VisitorScopeMap> {
        Some(self.map)
    }
}

pub(crate) fn map_expr_visitor_env<E, FE, FS, FT>(
    expr: &Expr,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Expr, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut vis = MapExprStmtTypVisitor {
        env, fe, fs, ft, map,
    };
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
    )
}

pub(crate) fn map_param_visitor<E, FT>(param: &Param, env: &mut E, ft: &FT) -> Result<Param, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let typ = map_typ_visitor_env(&param.x.typ, env, ft)?;
    let paramx = ParamX {
        name: param.x.name.clone(),
        typ,
        mode: param.x.mode,
        is_mut: param.x.is_mut,
        unwrapped_info: param.x.unwrapped_info.clone(),
    };
    Ok(Spanned::new(param.span.clone(), paramx))
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
    match &**bound {
        GenericBoundX::Trait(trait_path, ts) => {
            let ts = map_typs_visitor_env(ts, env, ft)?;
            Ok(Arc::new(GenericBoundX::Trait(trait_path.clone(), ts)))
        }
        GenericBoundX::TypEquality(trait_path, ts, name, t) => {
            let ts = map_typs_visitor_env(ts, env, ft)?;
            let t = map_typ_visitor_env(t, env, ft)?;
            Ok(Arc::new(GenericBoundX::TypEquality(trait_path.clone(), ts, name.clone(), t)))
        }
        GenericBoundX::ConstTyp(t, s) => {
            let t = map_typ_visitor_env(t, env, ft)?;
            let s = map_typ_visitor_env(s, env, ft)?;
            Ok(Arc::new(GenericBoundX::ConstTyp(t, s)))
        }
    }
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

pub(crate) fn map_function_visitor_env<E, FE, FS, FT>(
    function: &Function,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Function, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
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
        params,
        ret,
        ens_has_return,
        require,
        ensure,
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
    let name = name.clone();
    let proxy = proxy.clone();
    let kind = match kind {
        FunctionKind::Static | FunctionKind::TraitMethodDecl { trait_path: _, has_default: _ } => {
            kind.clone()
        }
        FunctionKind::TraitMethodImpl {
            method,
            impl_path,
            trait_path,
            trait_typ_args,
            inherit_body_from,
        } => FunctionKind::TraitMethodImpl {
            method: method.clone(),
            impl_path: impl_path.clone(),
            trait_path: trait_path.clone(),
            trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
            inherit_body_from: inherit_body_from.clone(),
        },
        FunctionKind::ForeignTraitMethodImpl { method, impl_path, trait_path, trait_typ_args } => {
            FunctionKind::ForeignTraitMethodImpl {
                method: method.clone(),
                impl_path: impl_path.clone(),
                trait_path: trait_path.clone(),
                trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
            }
        }
    };
    let visibility = visibility.clone();
    let body_visibility = body_visibility.clone();
    let opaqueness = opaqueness.clone();
    let owning_module = owning_module.clone();
    let mode = *mode;
    let typ_bounds = map_generic_bounds_visitor(typ_bounds, env, ft)?;
    map.push_scope(true);
    let params = map_params_visitor(params, env, ft)?;
    for p in params.iter() {
        let _ = map
            .insert(p.x.name.clone(), ScopeEntry::new_outer_param_ret(&p.x.typ, p.x.is_mut, true));
    }
    let ret = map_param_visitor(ret, env, ft)?;
    let require =
        Arc::new(vec_map_result(require, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);

    map.push_scope(true);
    if function.x.ens_has_return {
        let _ = map
            .insert(ret.x.name.clone(), ScopeEntry::new_outer_param_ret(&ret.x.typ, false, true));
    }
    let ensure =
        Arc::new(vec_map_result(ensure, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);
    map.pop_scope();

    let returns = match returns {
        Some(e) => Some(map_expr_visitor_env(e, map, env, fe, fs, ft)?),
        None => None,
    };

    let decrease =
        Arc::new(vec_map_result(decrease, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);
    let decrease_when = decrease_when
        .as_ref()
        .map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft))
        .transpose()?;
    let decrease_by = decrease_by.clone();

    let mask_spec = match mask_spec {
        None => None,
        Some(MaskSpec::InvariantOpens(span, es)) => Some(MaskSpec::InvariantOpens(
            span.clone(),
            Arc::new(vec_map_result(es, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?),
        )),
        Some(MaskSpec::InvariantOpensExcept(span, es)) => Some(MaskSpec::InvariantOpensExcept(
            span.clone(),
            Arc::new(vec_map_result(es, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?),
        )),
        Some(MaskSpec::InvariantOpensSet(e)) => {
            Some(MaskSpec::InvariantOpensSet(map_expr_visitor_env(e, map, env, fe, fs, ft)?))
        }
    };
    let unwind_spec = match unwind_spec {
        None => None,
        Some(UnwindSpec::MayUnwind) => Some(UnwindSpec::MayUnwind),
        Some(UnwindSpec::NoUnwind) => Some(UnwindSpec::NoUnwind),
        Some(UnwindSpec::NoUnwindWhen(e)) => {
            Some(UnwindSpec::NoUnwindWhen(map_expr_visitor_env(e, map, env, fe, fs, ft)?))
        }
    };
    let attrs = attrs.clone();
    let extra_dependencies = extra_dependencies.clone();
    let item_kind = *item_kind;
    let body = body.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
    map.pop_scope();

    let fndef_axioms = if let Some(es) = fndef_axioms {
        let mut es2 = vec![];
        for e in es.iter() {
            let e2 = map_expr_visitor_env(e, map, env, fe, fs, ft)?;
            es2.push(e2);
        }
        Some(Arc::new(es2))
    } else {
        None
    };

    let functionx = FunctionX {
        name,
        proxy,
        kind,
        visibility,
        body_visibility,
        opaqueness,
        owning_module,
        mode,
        typ_params: typ_params.clone(),
        typ_bounds,
        params,
        ret,
        ens_has_return: *ens_has_return,
        require,
        ensure,
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
    };
    Ok(Spanned::new(function.span.clone(), functionx))
}

pub(crate) fn map_datatype_visitor_env<E, FT>(
    datatype: &Datatype,
    env: &mut E,
    ft: &FT,
) -> Result<Datatype, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let datatypex = datatype.x.clone();
    let typ_bounds = map_generic_bounds_visitor(&datatypex.typ_bounds, env, ft)?;
    let mut variants: Vec<Variant> = Vec::new();
    for variant in datatypex.variants.iter() {
        let mut fields: Vec<Field> = Vec::new();
        for field in variant.fields.iter() {
            let (typ, mode, vis) = &field.a;
            let typ = map_typ_visitor_env(typ, env, ft)?;
            fields.push(field.new_a((typ, *mode, vis.clone())));
        }
        let variant = Variant { fields: Arc::new(fields), ..variant.clone() };
        variants.push(variant);
    }
    let variants = Arc::new(variants);
    Ok(Spanned::new(datatype.span.clone(), DatatypeX { variants, typ_bounds, ..datatypex }))
}

pub(crate) fn map_trait_impl_visitor_env<E, FT>(
    imp: &TraitImpl,
    env: &mut E,
    ft: &FT,
) -> Result<TraitImpl, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let TraitImplX {
        impl_path,
        typ_params,
        typ_bounds,
        trait_path,
        trait_typ_args,
        trait_typ_arg_impls,
        owning_module,
        auto_imported,
    } = &imp.x;
    let impx = TraitImplX {
        impl_path: impl_path.clone(),
        typ_params: typ_params.clone(),
        typ_bounds: map_generic_bounds_visitor(typ_bounds, env, ft)?,
        trait_path: trait_path.clone(),
        trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
        trait_typ_arg_impls: trait_typ_arg_impls.clone(),
        owning_module: owning_module.clone(),
        auto_imported: *auto_imported,
    };
    Ok(Spanned::new(imp.span.clone(), impx))
}

pub(crate) fn map_assoc_type_impl_visitor_env<E, FT>(
    assoc: &AssocTypeImpl,
    env: &mut E,
    ft: &FT,
) -> Result<AssocTypeImpl, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let AssocTypeImplX {
        name,
        impl_path,
        typ_params,
        typ_bounds,
        trait_path,
        trait_typ_args,
        typ,
        impl_paths,
    } = &assoc.x;
    let typ = map_typ_visitor_env(typ, env, ft)?;
    let assocx = AssocTypeImplX {
        name: name.clone(),
        impl_path: impl_path.clone(),
        typ_params: typ_params.clone(),
        typ_bounds: map_generic_bounds_visitor(typ_bounds, env, ft)?,
        trait_path: trait_path.clone(),
        trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
        typ,
        impl_paths: impl_paths.clone(),
    };
    Ok(Spanned::new(assoc.span.clone(), assocx))
}
