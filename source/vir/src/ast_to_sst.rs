use crate::ast::{
    ArithOp, AssertQueryMode, AutospecUsage, BinaryOp, BitwiseOp, CallTarget, ComputeMode,
    Constant, Expr, ExprX, FieldOpr, Fun, Function, Ident, LoopInvariantKind, Mode, PatternX,
    SpannedTyped, Stmt, StmtX, Typ, TypX, Typs, UnaryOp, UnaryOpr, VarAt, VariantCheck, VirErr,
};
use crate::ast::{BuiltinSpecFun, Exprs};
use crate::ast_util::{types_equal, undecorate_typ, QUANT_FORALL};
use crate::context::Ctx;
use crate::def::{unique_bound, unique_local, Spanned};
use crate::func_to_air::{SstInfo, SstMap};
use crate::interpreter::eval_expr;
use crate::messages::{error, error_with_label, internal_error, warning, Span, ToAny};
use crate::sst::{
    Bnd, BndX, CallFun, Dest, Exp, ExpX, Exps, InternalFun, LocalDecl, LocalDeclX, ParPurpose,
    Pars, Stm, StmX, UniqueIdent,
};
use crate::sst_util::{
    bitwidth_sst_from_typ, free_vars_exp, free_vars_stm, sst_array_index, sst_conjoin, sst_equal,
    sst_has_type, sst_int_literal, sst_le, sst_lt,
};
use crate::sst_visitor::{map_exp_visitor, map_stm_exp_visitor};
use crate::triggers::{typ_boxing, TriggerBoxing};
use crate::util::{vec_map, vec_map_result};
use crate::visitor::VisitorControlFlow;
use air::ast::{Binder, BinderX, Binders};
use air::messages::Diagnostics;
use air::scope_map::ScopeMap;
use indexmap::IndexSet;
use num_bigint::BigInt;
use num_traits::identities::Zero;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

#[derive(Clone)]
pub(crate) struct ClosureState {
    ensures: Exps,
    // recommends to check the well-formedness of the ensures clauses themselves
    ensures_checks: crate::sst::Stms,
    dest: UniqueIdent,
}

pub(crate) struct State<'a> {
    // View exec/proof code as spec
    // (used for is_const functions, which are viewable both as spec and exec)
    pub(crate) view_as_spec: bool,
    // If Some((f, scc_rep)), translate recursive calls in f's SCC into StmX::Call
    pub(crate) check_spec_decreases: Option<(Fun, crate::recursion::Node)>,
    // Counter to generate temporary variables
    next_var: u64,
    // Collect all local variable declarations
    pub(crate) local_decls: Vec<LocalDecl>,
    // Rename local variables when needed, using unique integers, to avoid collisions.
    // This is only needed for statement-level declarations (Some(unique_int)),
    // not for expression-level bindings (None).
    rename_map: ScopeMap<Ident, Option<u64>>,
    // Next integer to use for renaming each variable
    rename_counters: HashMap<Ident, u64>,
    // Variables that we considered renaming, but ended up being Bind variables
    // rather than LocalDecls
    dont_rename: HashSet<UniqueIdent>,
    // If > 0, we're making a second pass over AST to generate just a pure Exp, with no Stms.
    // Rationale: in the first pass, when checking preconditions of spec functions
    // (e.g. recommends), we may have to generate Stms for the precondition checking,
    // and we may have to generate LocalDecl to support the Stms rather than Exp::Bind.
    // In some situations (e.g. inside a quantifier), we need a pure Exp with Exp::Bind
    // and no Stms instead, so we make a second pass to generate this.
    only_generate_pure_exp: u64,
    // If > 0, disable checking recommends
    pub(crate) disable_recommends: u64,
    // Mapping from a function's name to the SST version of its body.  Used by the interpreter.
    pub fun_ssts: SstMap,
    // Diagnostic output
    pub diagnostics: &'a (dyn Diagnostics + 'a),
    // If inside a closure
    containing_closure: Option<ClosureState>,
    // Statics that are referenced (not counting statics in loops)
    pub statics: IndexSet<Fun>,
}

#[derive(Clone)]
pub(crate) enum ReturnValue {
    Some(Exp),
    ImplicitUnit(Span),
    Never,
}

impl ReturnValue {
    /// Turn implicit unit into an "explicit unit", i.e., an
    /// sst Exp representing the unit value; meanwhile, return None for Never.
    fn to_value(self) -> Option<Exp> {
        match self {
            ReturnValue::Some(e) => Some(e),
            ReturnValue::ImplicitUnit(span) => Some(lowered_unit_value(&span)),
            ReturnValue::Never => None,
        }
    }

    fn expect_value(self) -> Exp {
        match self {
            ReturnValue::Some(e) => e,
            ReturnValue::ImplicitUnit(span) => lowered_unit_value(&span),
            ReturnValue::Never => panic!("ReturnValue::Never unexpected here"),
        }
    }
}

/// Macro to help while processing an expression.
/// Many expressions have a form where we process subexpressions, and if one
/// of the subexpressions returns Never, then we want to return immediately,
/// returning only the statements we have collected so far and passing the Never
/// up to the next level. This macro makes it a bit more convenient.
macro_rules! unwrap_or_return_never {
    ($e:expr, $stms:expr) => {
        match $e.to_value() {
            Some(e) => e,
            None => {
                return Ok(($stms, ReturnValue::Never));
            }
        }
    };
}

impl<'a> State<'a> {
    pub fn new(diagnostics: &'a impl Diagnostics) -> Self {
        let mut rename_map = ScopeMap::new();
        rename_map.push_scope(true);
        State {
            view_as_spec: false,
            check_spec_decreases: None,
            next_var: 0,
            local_decls: Vec::new(),
            rename_map,
            rename_counters: HashMap::new(),
            dont_rename: HashSet::new(),
            only_generate_pure_exp: 0,
            disable_recommends: 0,
            fun_ssts: crate::update_cell::UpdateCell::new(HashMap::new()),
            diagnostics,
            containing_closure: None,
            statics: IndexSet::new(),
        }
    }

    fn next_temp(&mut self, span: &Span, typ: &Typ) -> (Ident, Exp) {
        self.next_var += 1;
        let x = crate::def::prefix_temp_var(self.next_var);
        (x.clone(), SpannedTyped::new(span, typ, ExpX::Var(unique_local(&x))))
    }

    pub(crate) fn push_scope(&mut self) {
        self.rename_map.push_scope(true);
    }

    pub(crate) fn pop_scope(&mut self) {
        self.rename_map.pop_scope();
    }

    pub(crate) fn get_var_unique_id(&self, x: &Ident) -> UniqueIdent {
        match self.rename_map.get(x) {
            None => panic!("internal error: variable not in rename_map: {}", x),
            Some(id) => UniqueIdent { name: x.clone(), local: *id },
        }
    }

    pub(crate) fn new_statement_var(&mut self, x: &Ident) {
        self.rename_counters.insert(x.clone(), 0);
        self.rename_map.insert(x.clone(), Some(0)).expect("new var");
    }

    pub(crate) fn declare_expression_var(&mut self, x: &Ident) {
        self.rename_map.insert(x.clone(), None).expect("declare var");
    }

    pub(crate) fn alloc_unique_var(&mut self, x: &Ident) -> UniqueIdent {
        let i = match self.rename_counters.get(x).copied() {
            None => 0,
            Some(i) => i + 1,
        };
        self.rename_counters.insert(x.clone(), i);
        UniqueIdent { name: x.clone(), local: Some(i) }
    }

    pub(crate) fn insert_unique_var(&mut self, x: &UniqueIdent) {
        self.rename_map.insert(x.name.clone(), x.local).expect("declare var");
    }

    pub(crate) fn declare_binders<A: Clone>(&mut self, binders: &Binders<A>) {
        for binder in binders.iter() {
            self.declare_expression_var(&binder.name);
        }
    }

    pub(crate) fn declare_new_var(
        &mut self,
        ident: &Ident,
        typ: &Typ,
        mutable: bool,
        may_need_rename: bool,
    ) -> UniqueIdent {
        let unique_ident = if may_need_rename {
            let id = self.alloc_unique_var(ident);
            self.insert_unique_var(&id);
            id
        } else {
            self.new_statement_var(&ident);
            unique_local(&ident)
        };
        let decl = LocalDeclX { ident: unique_ident.clone(), typ: typ.clone(), mutable };
        self.local_decls.push(Arc::new(decl));
        unique_ident
    }

    pub(crate) fn declare_params(&mut self, params: &Pars) {
        for param in params.iter() {
            if !matches!(param.x.purpose, ParPurpose::MutPost) {
                self.declare_new_var(&param.x.name, &param.x.typ, false, false);
            }
        }
    }

    // Erase unused unique ids from Vars and process inline functions
    pub(crate) fn finalize_exp(
        &self,
        ctx: &Ctx,
        fun_ssts: &SstMap,
        exp: &Exp,
    ) -> Result<Exp, VirErr> {
        let exp = map_exp_visitor(exp, &mut |exp| match &exp.x {
            ExpX::Var(x) if self.dont_rename.contains(&x) => {
                SpannedTyped::new(&exp.span, &exp.typ, ExpX::Var(unique_bound(&x.name)))
            }
            _ => exp.clone(),
        });
        let exp = crate::sst_visitor::map_exp_visitor_result(&exp, &mut |exp| match &exp.x {
            ExpX::Call(CallFun::Fun(fun, resolved_method), typs, args) => {
                let (fun, typs) =
                    if let Some((f, ts)) = resolved_method { (f, ts) } else { (fun, typs) };
                if let Some(SstInfo { inline, params, memoize: _, body }) =
                    fun_ssts.borrow().get(fun)
                {
                    if inline.do_inline {
                        let typ_params = &inline.typ_params;
                        let mut typ_substs: HashMap<Ident, Typ> = HashMap::new();
                        let mut substs: HashMap<UniqueIdent, Exp> = HashMap::new();
                        assert!(typ_params.len() == typs.len());
                        for (name, typ) in typ_params.iter().zip(typs.iter()) {
                            assert!(!typ_substs.contains_key(name));
                            let typ = crate::poly::coerce_typ_to_poly(ctx, typ);
                            typ_substs.insert(name.clone(), typ.clone());
                        }
                        assert!(params.len() == args.len());
                        for (param, arg) in params.iter().zip(args.iter()) {
                            let unique = unique_local(&param.x.name);
                            assert!(!substs.contains_key(&unique));
                            substs.insert(unique, arg.clone());
                        }
                        let e = crate::sst_util::subst_exp(&typ_substs, &substs, body);
                        // keep the original outer span for better trigger messages
                        let e = SpannedTyped::new(&exp.span, &e.typ, e.x.clone());
                        return Ok(e);
                    }
                }
                Ok(exp.clone())
            }
            ExpX::Bind(bnd, body) => match &bnd.x {
                BndX::Quant(quant, bs, trigs) => {
                    assert!(trigs.len() == 0);
                    let mut vars: Vec<(Ident, TriggerBoxing)> = Vec::new();
                    for b in bs.iter() {
                        match &*b.a {
                            TypX::TypeId => vars.push((
                                crate::def::suffix_typ_param_id(&b.name),
                                TriggerBoxing::TypeId,
                            )),
                            _ => vars.push((b.name.clone(), typ_boxing(ctx, &b.a))),
                        }
                    }
                    let trigs =
                        crate::triggers::build_triggers(ctx, &exp.span, &vars, &body, false)?;
                    let bnd =
                        Spanned::new(bnd.span.clone(), BndX::Quant(*quant, bs.clone(), trigs));
                    Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
                }
                BndX::Choose(bs, trigs, cond) => {
                    assert!(trigs.len() == 0);
                    let vars = vec_map(bs, |b| (b.name.clone(), typ_boxing(ctx, &b.a)));
                    let trigs =
                        crate::triggers::build_triggers(ctx, &exp.span, &vars, &cond, false)?;
                    let bnd = Spanned::new(
                        bnd.span.clone(),
                        BndX::Choose(bs.clone(), trigs, cond.clone()),
                    );
                    Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
                }
                BndX::Lambda(bs, trigs) => {
                    assert!(trigs.len() == 0);
                    let vars = vec_map(bs, |b| (b.name.clone(), typ_boxing(ctx, &b.a)));
                    let trigs =
                        crate::triggers::build_triggers(ctx, &exp.span, &vars, &body, true)?;
                    let bnd = Spanned::new(bnd.span.clone(), BndX::Lambda(bs.clone(), trigs));
                    Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
                }
                _ => Ok(exp.clone()),
            },
            // remove MustBeFinalized marker to vouch that finalize_exp was called
            ExpX::Unary(UnaryOp::MustBeFinalized, e1) => Ok(e1.clone()),
            _ => Ok(exp.clone()),
        });
        exp
    }

    // Erase unused unique ids from Vars, perform inlining, choose triggers,
    // and perform splitting if necessary
    pub(crate) fn finalize_stm(
        &self,
        ctx: &Ctx,
        diagnostics: &impl Diagnostics,
        fun_ssts: &SstMap,
        stm: &Stm,
        ensures: &Exprs,
        ens_pars: &Pars,
        dest: Option<UniqueIdent>,
    ) -> Result<Stm, VirErr> {
        let stm = map_stm_exp_visitor(stm, &|exp| self.finalize_exp(ctx, fun_ssts, exp))?;
        if ctx.expand_flag {
            crate::split_expression::all_split_exp(
                ctx,
                diagnostics,
                fun_ssts,
                &stm,
                ensures,
                ens_pars,
                dest,
            )
        } else {
            Ok(stm)
        }
    }

    pub(crate) fn finalize(&mut self) {
        self.pop_scope();
        assert_eq!(self.rename_map.num_scopes(), 0);
    }

    fn checking_spec_preconditions(&self, ctx: &Ctx) -> bool {
        ctx.checking_spec_preconditions() && self.only_generate_pure_exp == 0
    }

    fn checking_recommends(&self, ctx: &Ctx) -> bool {
        self.checking_spec_preconditions(ctx) && self.disable_recommends == 0
    }

    fn checking_spec_decreases(
        &self,
        ctx: &Ctx,
        target: &Fun,
        resolved_method: &Option<(Fun, Typs)>,
    ) -> bool {
        if ctx.checking_spec_decreases() && self.only_generate_pure_exp == 0 {
            if let Some((recursive_function_name, scc_rep)) = &self.check_spec_decreases {
                if let Some(callee) = crate::recursion::get_callee(ctx, target, resolved_method) {
                    return &callee == recursive_function_name
                        || &ctx
                            .global
                            .func_call_graph
                            .get_scc_rep(&crate::recursion::Node::Fun(callee.clone()))
                            == scc_rep;
                }
            }
        }
        false
    }

    fn checking_bounds_for_mode(&self, ctx: &Ctx, mode: Mode) -> bool {
        if self.view_as_spec {
            return false;
        }

        match mode {
            Mode::Spec => self.checking_recommends(ctx),
            Mode::Proof | Mode::Exec => !self.checking_spec_preconditions(ctx),
        }
    }
}

pub(crate) fn var_loc_exp(span: &Span, typ: &Typ, lhs: UniqueIdent) -> Exp {
    SpannedTyped::new(span, typ, ExpX::VarLoc(lhs))
}

fn init_var(span: &Span, x: &UniqueIdent, exp: &Exp) -> Stm {
    Spanned::new(
        span.clone(),
        StmX::Assign {
            lhs: Dest { dest: var_loc_exp(&exp.span, &exp.typ, x.clone()), is_init: true },
            rhs: exp.clone(),
        },
    )
}

pub(crate) fn get_function(ctx: &Ctx, span: &Span, name: &Fun) -> Result<Function, VirErr> {
    match ctx.func_map.get(name) {
        None => Err(error(span, format!("could not find function {:?}", &name))),
        Some(func) => Ok(func.clone()),
    }
}

fn function_can_be_exp(
    ctx: &Ctx,
    state: &State,
    expr: &Expr,
    path: &Fun,
    resolved_method: &Option<(Fun, Typs)>,
) -> Result<bool, VirErr> {
    let fun = get_function(ctx, &expr.span, path)?;
    match fun.x.mode {
        Mode::Spec if state.checking_spec_decreases(ctx, path, resolved_method) => Ok(false),
        Mode::Spec => Ok(!state.checking_recommends(ctx) || fun.x.require.len() == 0),
        Mode::Proof | Mode::Exec => Ok(false),
    }
}

pub fn assume_false(span: &Span) -> Stm {
    let expx = ExpX::Const(Constant::Bool(false));
    let exp = SpannedTyped::new(&span, &Arc::new(TypX::Bool), expx);
    Spanned::new(span.clone(), StmX::Assume(exp))
}

pub(crate) fn assume_has_typ(x: &UniqueIdent, typ: &Typ, span: &Span) -> Stm {
    let xvarx = ExpX::Var(x.clone());
    let xvar = SpannedTyped::new(span, &Arc::new(TypX::Bool), xvarx);
    let has_typx = ExpX::UnaryOpr(UnaryOpr::HasType(typ.clone()), xvar);
    let has_typ = SpannedTyped::new(span, &Arc::new(TypX::Bool), has_typx);
    Spanned::new(span.clone(), StmX::Assume(has_typ))
}

fn loop_body_find_break(
    loop_label: &Option<String>,
    in_subloop: bool,
    found_break: &mut bool,
    body: &Expr,
) {
    let mut f = |expr: &Expr| match &expr.x {
        ExprX::Loop { body, .. } => {
            loop_body_find_break(loop_label, true, found_break, body);
            VisitorControlFlow::Return
        }
        ExprX::BreakOrContinue { label: break_label, is_break: true } => {
            if break_label.is_none() {
                if !in_subloop {
                    *found_break = true;
                }
            } else {
                if break_label == loop_label {
                    *found_break = true;
                }
            }
            VisitorControlFlow::Recurse
        }
        _ => VisitorControlFlow::Recurse,
    };
    crate::ast_visitor::expr_visitor_walk(body, &mut f);
}

fn loop_body_has_break(loop_label: &Option<String>, body: &Expr) -> bool {
    let mut found_break = false;
    loop_body_find_break(loop_label, false, &mut found_break, body);
    found_break
}

/// Determine if it's possible for control flow to reach the statement after the loop exit.
/// Naturally, we need to be conservative and answer 'yes' if we can't tell.
/// However, this analysis is also relevant to the typing of the program: in particular,
/// we ALSO need to return 'no' if any case where rustc's typechecker
/// might have said 'no'.
///
/// The reason is that: if rustc determines that the loop can't exit, then
/// the code after this will be unreachable, which means the user might be allowed
/// to leave off a return expression. We need to detect that case, or else we might
/// wrongly determine that it returns a 'unit' and we'll create malformed AIR code.
///
/// So when does Rust do this? As far as I can tell, it only does this if:
///
///   (i) it's a 'loop' statement, and
///   (ii) it doesn't have ANY 'break' statement in it
///        (It is possible that a 'break' statement in a while loop might itself be
///        unreachable, but Rust doesn't seem to take that into account for this purpose.)
///
/// TODO: Update this check when we support 'break' statements.
/// Notes: it may be possible to get this information from rustc, either typeck or MIR.
/// On the other hand, we'll need to answer the question "does this loop have any break
/// statements?" for invariant gen anyway, and that's a slightly different question.

pub fn can_control_flow_reach_after_loop(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Loop { is_for_loop: _, label, cond: None, body, invs: _ } => {
            loop_body_has_break(label, body)
        }
        ExprX::Loop { is_for_loop: _, label: _, cond: Some(_), body: _, invs: _ } => true,
        _ => {
            panic!("expected while loop");
        }
    }
}

enum ReturnedCall {
    Call {
        fun: Fun,
        resolved_method: Option<(Fun, Typs)>,
        typs: Typs,
        has_return: bool,
        args: Exps,
    },
    Never,
}

fn expr_get_call(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, ReturnedCall)>, VirErr> {
    match &expr.x {
        ExprX::Call(target, args) => match target {
            CallTarget::FnSpec(..) => {
                panic!("internal error: CallTarget::FnSpec");
            }
            CallTarget::Fun(kind, x, typs, _impl_paths, autospec_usage) => {
                if *autospec_usage != AutospecUsage::Final {
                    return Err(internal_error(&expr.span, "autospec not discharged"));
                }
                let mut stms: Vec<Stm> = Vec::new();
                let mut exps: Vec<Exp> = Vec::new();
                for arg in args.iter() {
                    let (mut stms0, e0) = expr_to_stm_opt(ctx, state, arg)?;
                    stms.append(&mut stms0);
                    let e0 = match e0.to_value() {
                        Some(e) => e,
                        None => {
                            return Ok(Some((stms, ReturnedCall::Never)));
                        }
                    };
                    exps.push(e0);
                }
                let has_ret = get_function(ctx, &expr.span, x)?.x.has_return();
                Ok(Some((
                    stms,
                    ReturnedCall::Call {
                        fun: x.clone(),
                        resolved_method: kind.resolved(),
                        typs: typs.clone(),
                        has_return: has_ret,
                        args: Arc::new(exps),
                    },
                )))
            }
            CallTarget::BuiltinSpecFun(_, _, _) => {
                panic!("internal error: CallTarget::BuiltinSpecFn");
            }
        },
        _ => Ok(None),
    }
}

// If the Expr is a call that must be a Stm (not an Exp), return it
fn expr_must_be_call_stm(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, ReturnedCall)>, VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::Fun(kind, x, _, _, _), _)
            if !function_can_be_exp(ctx, state, expr, x, &kind.resolved())? =>
        {
            expr_get_call(ctx, state, expr)
        }
        _ => Ok(None),
    }
}

// Check spec preconditions in expr, but don't generate an Exp for Expr
pub(crate) fn check_pure_expr(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Vec<Stm>, VirErr> {
    if state.checking_spec_preconditions(ctx) {
        let (stms, _exp) = expr_to_stm_or_error(ctx, state, expr)?;
        Ok(stms)
    } else {
        Ok(vec![])
    }
}

// Check spec preconditions in expr, but don't generate an Exp for Expr
// Declare variables from binders as locals for checking
pub(crate) fn check_pure_expr_bind(
    ctx: &Ctx,
    state: &mut State,
    binders: &Binders<Typ>,
    expr: &Expr,
) -> Result<Vec<Stm>, VirErr> {
    if state.checking_spec_preconditions(ctx) {
        state.push_scope();
        let mut stms: Vec<Stm> = Vec::new();
        for binder in binders.iter() {
            let x = state.declare_new_var(&binder.name, &binder.a, false, true);
            if crate::poly::typ_is_poly(ctx, &binder.a) {
                stms.push(assume_has_typ(&x, &binder.a, &expr.span));
            }
        }
        let (stms1, _exp) = expr_to_stm_or_error(ctx, state, expr)?;
        stms.extend(stms1);
        state.pop_scope();
        Ok(stms)
    } else {
        Ok(vec![])
    }
}

// This skips the spec precondition checks (e.g. recommends),
// so only use this if there's some justification (i.e. checks happen elsewhere).
// Otherwise, call expr_to_pure_exp_check.
pub(crate) fn expr_to_pure_exp_skip_checks(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Exp, VirErr> {
    state.only_generate_pure_exp += 1;
    let (stms, exp) = expr_to_stm_or_error(ctx, state, expr)?;
    let result = if stms.len() == 0 {
        Ok(exp)
    } else {
        Err(error(&expr.span, "expected pure mathematical expression"))
    };
    state.only_generate_pure_exp -= 1;
    result
}

// For handling recommends, we need to generate both a recommends check of a pure expression
// and the pure expression itself.
pub(crate) fn expr_to_pure_exp_check(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Exp), VirErr> {
    if state.checking_spec_preconditions(ctx) {
        let (stms, exp) = expr_to_stm_or_error(ctx, state, expr)?;
        if stms.len() == 0 {
            return Ok((vec![], exp));
        } else {
            // Discard exp here, but keep stms.
            // exp may depend on stms, so we can't use it as a self-contained pure Exp,
            // so we need to call expr_to_pure_exp_skip_checks to generate a second Exp.
            // It's inefficient to generate exp and throw it away, but
            // it's hard to see what else to do, since the structure of exp
            // may differ substantially from expr_to_pure_exp_skip_checks(ctx, state, expr)?.
            Ok((stms, expr_to_pure_exp_skip_checks(ctx, state, expr)?))
        }
    } else {
        Ok((vec![], expr_to_pure_exp_skip_checks(ctx, state, expr)?))
    }
}

pub(crate) fn expr_to_decls_exp_skip_checks(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    view_as_spec: bool,
    params: &Pars,
    expr: &Expr,
) -> Result<(Vec<LocalDecl>, Exp), VirErr> {
    let mut state = State::new(diagnostics);
    state.view_as_spec = view_as_spec;
    state.declare_params(params);
    let exp = expr_to_pure_exp_skip_checks(ctx, &mut state, expr)?;
    let exp = state.finalize_exp(ctx, fun_ssts, &exp)?;
    state.finalize();
    Ok((state.local_decls, exp))
}

pub(crate) fn expr_to_bind_decls_exp_skip_checks(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    params: &Pars,
    expr: &Expr,
) -> Result<Exp, VirErr> {
    let mut state = State::new(diagnostics);
    for param in params.iter() {
        let id = state.declare_new_var(&param.x.name, &param.x.typ, false, false);
        state.dont_rename.insert(id);
    }
    let exp = expr_to_pure_exp_skip_checks(ctx, &mut state, expr)?;
    let exp = state.finalize_exp(ctx, &fun_ssts, &exp)?;
    state.finalize();
    Ok(exp)
}

pub(crate) fn expr_to_exp_skip_checks(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    params: &Pars,
    expr: &Expr,
) -> Result<Exp, VirErr> {
    Ok(expr_to_decls_exp_skip_checks(ctx, diagnostics, fun_ssts, false, params, expr)?.1)
}

pub(crate) fn expr_to_exp_as_spec_skip_checks(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    params: &Pars,
    expr: &Expr,
) -> Result<Exp, VirErr> {
    Ok(expr_to_decls_exp_skip_checks(ctx, diagnostics, fun_ssts, true, params, expr)?.1)
}

/// Convert an expr to (Vec<Stm>, Exp).
/// Errors if the given expression is one that never returns a value.
/// (This should only be used in contexts where that should never happen, like spec
/// contexts. Otherwise, call `expr_to_stm_opt` and handle the Never case).

pub(crate) fn expr_to_stm_or_error(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Exp), VirErr> {
    let (stms, exp_opt) = expr_to_stm_opt(ctx, state, expr)?;
    match exp_opt.to_value() {
        Some(e) => Ok((stms, e)),
        None => Err(error(&expr.span, "expression must produce a value")),
    }
}

/// Unit type, in the lowered form that ast_simplify produces
fn lowered_unit_typ() -> Typ {
    let path = crate::def::prefix_tuple_type(0);
    Arc::new(TypX::Datatype(path, Arc::new(vec![]), Arc::new(vec![])))
}

/// Unit value, in the lowered form that ast_simplify produces
fn lowered_unit_value(span: &Span) -> Exp {
    let datatype = crate::def::prefix_tuple_type(0);
    let variant = crate::def::prefix_tuple_variant(0);
    SpannedTyped::new(span, &lowered_unit_typ(), ExpX::Ctor(datatype, variant, Arc::new(vec![])))
}

pub(crate) fn stms_to_one_stm(span: &Span, stms: Vec<Stm>) -> Stm {
    if stms.len() == 1 {
        stms[0].clone()
    } else {
        Spanned::new(span.clone(), StmX::Block(Arc::new(stms)))
    }
}

pub(crate) fn stms_to_one_stm_opt(span: &Span, stms: Vec<Stm>) -> Option<Stm> {
    if stms.len() == 0 { None } else { Some(stms_to_one_stm(span, stms)) }
}

/// Convert the expression to a Stm, and assert the post-conditions for
/// the final returned expression.
pub(crate) fn expr_to_one_stm_with_post(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Stm, VirErr> {
    let (mut stms, exp) = expr_to_stm_opt(ctx, state, expr)?;

    // secondary label (indicating which post-condition failed) is added later
    // in ast_to_sst when the post condition is expanded
    let base_error = error_with_label(
        &expr.span,
        crate::def::POSTCONDITION_FAILURE.to_string(),
        "at the end of the function body".to_string(),
    );

    match exp.to_value() {
        Some(exp) => {
            // Emit the postcondition for the common case where the function body
            // terminates with an expression to be returned (or an implicit
            // return value of 'unit').

            stms.push(Spanned::new(
                expr.span.clone(),
                StmX::Return { base_error, ret_exp: Some(exp), inside_body: false },
            ));
        }
        None => {
            // Program execution never gets to this point, so we don't need to check
            // any postconditions.
            // This might happen, for example, if the user writes their code in this style:
            //
            //    fn foo() {
            //        ...
            //        return x;
            //    }
            //
            // Here, we will always process the post-conditions when we get to the `return`
            // statement, but technically, the return statement is still an "early return"
            // and we never actually get to "the end" of the function.
            // Anyway, the point is, we don't need to check the postconditions again
            // in that case, or in any other case where we never reach the end of the
            // function.
        }
    };
    Ok(stms_to_one_stm(&expr.span, stms))
}

fn is_small_exp(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Const(_) => true,
        ExpX::Var(..) | ExpX::VarAt(..) => true,
        ExpX::Old(..) => true,
        ExpX::Unary(UnaryOp::Not | UnaryOp::Clip { .. } | UnaryOp::MustBeFinalized, e) => {
            is_small_exp_or_loc(e)
        }
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_exp_or_loc(e),
        _ => false,
    }
}

fn is_small_exp_or_loc(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Loc(..) => true,
        _ => is_small_exp(exp),
    }
}

fn stm_call(
    ctx: &Ctx,
    state: &mut State,
    span: &Span,
    name: Fun,
    resolved_method: Option<(Fun, Typs)>,
    typs: Typs,
    args: Exps,
    dest: Option<Dest>,
) -> Result<Stm, VirErr> {
    let fun = get_function(ctx, span, &name)?;
    let mut stms: Vec<Stm> = Vec::new();
    if ctx.expand_flag && crate::split_expression::need_split_expression(ctx, span) {
        let error = error(span, crate::def::SPLIT_PRE_FAILURE.to_string());
        let call = StmX::Call {
            fun: name.clone(),
            resolved_method: resolved_method.clone(),
            mode: fun.x.mode,
            typ_args: typs.clone(),
            args: args.clone(),
            split: Some(error),
            dest: None,
        };
        stms.push(Spanned::new(span.clone(), call));
    }

    let mut small_args: Vec<Exp> = Vec::new();
    for arg in args.iter() {
        if is_small_exp_or_loc(arg) {
            small_args.push(arg.clone());
        } else {
            // To avoid copying arg in preconditions and postconditions,
            // put arg into a temporary variable
            let (temp, temp_var) = state.next_temp(&arg.span, &arg.typ);
            small_args.push(temp_var);
            let temp_id = state.declare_new_var(&temp, &arg.typ, false, false);
            stms.push(init_var(&arg.span, &temp_id, arg));
        }
    }
    let call = StmX::Call {
        fun: name,
        resolved_method,
        mode: fun.x.mode,
        typ_args: typs,
        args: Arc::new(small_args),
        split: None,
        dest,
    };
    stms.push(Spanned::new(span.clone(), call));
    Ok(stms_to_one_stm(span, stms))
}

fn if_to_stm(
    state: &mut State,
    expr: &Expr,
    mut stms0: Vec<Stm>,
    e0: &ReturnValue,
    mut stms1: Vec<Stm>,
    e1: &ReturnValue,
    mut stms2: Vec<Stm>,
    e2: &ReturnValue,
) -> (Vec<Stm>, ReturnValue) {
    let e0 = match e0.clone().to_value() {
        Some(e) => e,
        None => {
            return (stms0, ReturnValue::Never);
        }
    };

    match (e1, e2) {
        (ReturnValue::ImplicitUnit(_), _) | (_, ReturnValue::ImplicitUnit(_)) => {
            // If one branch returned an implicit unit, then the other branch
            // must also return a unit (either implicit or explicit).
            // If this sanity check fails, then it's likely we screwed up and
            // the alleged implicit unit branch was actually a never-return.
            assert!(types_equal(&expr.typ, &lowered_unit_typ()));

            let stm1 = stms_to_one_stm(&expr.span, stms1);
            let stm2 = stms_to_one_stm_opt(&expr.span, stms2);
            let if_stmt = StmX::If(e0, stm1, stm2);
            stms0.push(Spanned::new(expr.span.clone(), if_stmt));
            (stms0, ReturnValue::ImplicitUnit(expr.span.clone()))
        }
        (ReturnValue::Never, other) | (other, ReturnValue::Never) => {
            // Suppose one side never returns; the return value of the conditional
            // (assuming it DOES return) will always be the one from the other branch.
            // (Of course, the other branch might be 'Never' too, in which case the
            // return value of the whole expression is Never.)
            //
            // For example, if we have:
            //    let t = if cond { 5 } else { return; };
            // Then we get Some(5) from the left branch, and Never from the right branch.
            // Furthermore, for the purposes of assigning to `t`, we can assume the return
            // value of the branch is _always_ 5.

            let stm1 = stms_to_one_stm(&expr.span, stms1);
            let stm2 = stms_to_one_stm_opt(&expr.span, stms2);
            let if_stmt = StmX::If(e0, stm1, stm2);
            stms0.push(Spanned::new(expr.span.clone(), if_stmt));
            (stms0, other.clone())
        }
        (ReturnValue::Some(e1), ReturnValue::Some(e2)) => {
            if stms1.len() == 0 && stms2.len() == 0 {
                // In this case, we can construct a pure expression.
                let expx = ExpX::If(e0.clone(), e1.clone(), e2.clone());
                let exp = SpannedTyped::new(&expr.span, &expr.typ, expx);
                (stms0, ReturnValue::Some(exp))
            } else {
                // We have `if ( stms0; e0 ) { stms1; e1 } else { stms2; e2 }`.
                // We turn this into:
                //  stms0;
                //  if e0 { stms1; temp = e1; } else { stms2; temp = e2; };
                //  temp

                let (temp, temp_var) = state.next_temp(&expr.span, &expr.typ);
                let temp_id = state.declare_new_var(&temp, &expr.typ, false, false);
                stms1.push(init_var(&expr.span, &temp_id, &e1));
                stms2.push(init_var(&expr.span, &temp_id, &e2));
                let stm1 = stms_to_one_stm(&expr.span, stms1);
                let stm2 = stms_to_one_stm_opt(&expr.span, stms2);
                let if_stmt = StmX::If(e0, stm1, stm2);
                stms0.push(Spanned::new(expr.span.clone(), if_stmt));
                // temp
                (stms0, ReturnValue::Some(temp_var))
            }
        }
    }
}

/// Convert a VIR Expr to a SST (Vec<Stm>, ReturnValue), i.e., instructions of the form,
/// "run these statements, then return this side-effect-free expression".
///
/// Note the 'ReturnValue' can be one of three things:
///  * Some(e) - means the expression e was returned
///  * Unit - for the implicit unit case
///  * Never - the expression can never return (e.g., after a return value or break)

pub(crate) fn expr_to_stm_opt(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, ReturnValue), VirErr> {
    let mk_exp = |expx: ExpX| SpannedTyped::new(&expr.span, &expr.typ, expx);
    match &expr.x {
        ExprX::Const(c) => Ok((vec![], ReturnValue::Some(mk_exp(ExpX::Const(c.clone()))))),
        ExprX::Var(x) => {
            let unique_id = state.get_var_unique_id(&x);
            let e = mk_exp(ExpX::Var(unique_id));
            let e = mk_exp(ExpX::Unary(UnaryOp::MustBeFinalized, e));
            Ok((vec![], ReturnValue::Some(e)))
        }
        ExprX::StaticVar(x) => {
            state.statics.insert(x.clone());
            let e = mk_exp(ExpX::StaticVar(x.clone()));
            Ok((vec![], ReturnValue::Some(e)))
        }
        ExprX::VarLoc(x) => {
            let unique_id = state.get_var_unique_id(&x);
            Ok((vec![], ReturnValue::Some(mk_exp(ExpX::VarLoc(unique_id)))))
        }
        ExprX::VarAt(x, VarAt::Pre) => {
            if let Some((scope, _)) = state.rename_map.scope_and_index_of_key(x) {
                if scope != 0 {
                    Err(error(&expr.span, "the parameter is shadowed here"))?;
                }
            }
            Ok((
                vec![],
                ReturnValue::Some(mk_exp(ExpX::VarAt(state.get_var_unique_id(&x), VarAt::Pre))),
            ))
        }
        ExprX::ConstVar(..) => panic!("ConstVar should already be removed"),
        ExprX::Loc(expr1) => {
            let (stms, e0) = expr_to_stm_opt(ctx, state, expr1)?;
            let e0 = unwrap_or_return_never!(e0, stms);
            Ok((stms, ReturnValue::Some(mk_exp(ExpX::Loc(e0)))))
        }
        ExprX::Assign { init_not_mut, lhs: lhs_expr, rhs: expr2, op } => {
            if op.is_some() {
                panic!("op should already be removed")
            }
            let (mut stms, lhs_exp) = expr_to_stm_opt(ctx, state, lhs_expr)?;
            let lhs_exp = lhs_exp.expect_value();
            match expr_must_be_call_stm(ctx, state, expr2)? {
                Some((stms2, ReturnedCall::Never)) => {
                    stms.extend(stms2.into_iter());
                    Ok((stms, ReturnValue::Never))
                }
                Some((
                    stms2,
                    ReturnedCall::Call { fun, resolved_method, typs, has_return: _, args },
                )) => {
                    // make a Call
                    stms.extend(stms2.into_iter());
                    let (dest, assign) = if matches!(lhs_exp.x, ExpX::VarLoc(_)) {
                        (Dest { dest: lhs_exp, is_init: *init_not_mut }, None)
                    } else {
                        assert!(!*init_not_mut, "init_not_mut unexpected for complex call dest");
                        let (temp, temp_var) = state.next_temp(&lhs_exp.span, &expr2.typ);
                        let temp_ident = state.declare_new_var(&temp, &expr2.typ, false, false);
                        let assign = Spanned::new(
                            lhs_exp.span.clone(),
                            StmX::Assign {
                                lhs: Dest { dest: lhs_exp.clone(), is_init: false },
                                rhs: temp_var,
                            },
                        );
                        (
                            Dest {
                                dest: var_loc_exp(&lhs_exp.span, &expr2.typ, temp_ident),
                                is_init: true,
                            },
                            Some(assign),
                        )
                    };
                    stms.push(stm_call(
                        ctx,
                        state,
                        &expr.span,
                        fun,
                        resolved_method,
                        typs,
                        args,
                        Some(dest),
                    )?);
                    // REVIEW: for a similar case in `ExprX::Call` we emit a StmX::Assign to set the
                    // value of the destination when, in recommends checking, the StmX::Call is used
                    // to check its recommends, however we do not do this here.
                    // That may cause recommends incompleteness. We should either use the `ExprX::Call`
                    // special-case for recommends here, or replace this logic with a recursive call
                    // to handle the right-hand-side, if possible.
                    stms.extend(assign.into_iter());
                    Ok((stms, ReturnValue::ImplicitUnit(expr.span.clone())))
                }
                None => {
                    // make an Assign
                    let (stms2, e2) = expr_to_stm_opt(ctx, state, expr2)?;
                    let e2 = unwrap_or_return_never!(e2, stms2);
                    stms.extend(stms2.into_iter());
                    let rhs = if matches!(lhs_exp.x, ExpX::VarLoc(_)) || is_small_exp(&e2) {
                        e2
                    } else {
                        let (temp, temp_var) = state.next_temp(&e2.span, &e2.typ);
                        let temp_ident = state.declare_new_var(&temp, &e2.typ, false, false);
                        stms.push(init_var(&expr.span, &temp_ident, &e2));
                        temp_var
                    };
                    let assign =
                        StmX::Assign { lhs: Dest { dest: lhs_exp, is_init: *init_not_mut }, rhs };
                    stms.push(Spanned::new(expr.span.clone(), assign));
                    Ok((stms, ReturnValue::ImplicitUnit(expr.span.clone())))
                }
            }
        }
        ExprX::Call(CallTarget::FnSpec(e0), args) => {
            let (mut check_stms, e0) = expr_to_pure_exp_check(ctx, state, e0)?;
            let mut arg_exps: Vec<Exp> = Vec::new();
            for arg in args.iter() {
                let (stms, e) = expr_to_pure_exp_check(ctx, state, arg)?;
                check_stms.extend(stms);
                arg_exps.push(e);
            }
            let call = ExpX::CallLambda(expr.typ.clone(), e0, Arc::new(arg_exps));
            Ok((check_stms, ReturnValue::Some(mk_exp(call))))
        }
        ExprX::Call(CallTarget::BuiltinSpecFun(bsf, ts, _impl_paths), args) => {
            let mut check_stms: Vec<Stm> = Vec::new();
            let mut arg_exps: Vec<Exp> = Vec::new();
            for arg in args.iter() {
                let (stms, e) = expr_to_pure_exp_check(ctx, state, arg)?;
                check_stms.extend(stms);
                arg_exps.push(e);
            }
            let f = match bsf {
                BuiltinSpecFun::ClosureReq => InternalFun::ClosureReq,
                BuiltinSpecFun::ClosureEns => InternalFun::ClosureEns,
            };
            Ok((
                check_stms,
                ReturnValue::Some(mk_exp(ExpX::Call(
                    CallFun::InternalFun(f),
                    ts.clone(),
                    Arc::new(arg_exps),
                ))),
            ))
        }
        ExprX::Call(CallTarget::Fun(..), _) => {
            match expr_get_call(ctx, state, expr)?.expect("Call") {
                (stms, ReturnedCall::Never) => Ok((stms, ReturnValue::Never)),
                (
                    mut stms,
                    ReturnedCall::Call { fun: x, resolved_method, typs, has_return: ret, args },
                ) => {
                    if function_can_be_exp(ctx, state, expr, &x, &resolved_method)? {
                        // ExpX::Call
                        let call = ExpX::Call(
                            CallFun::Fun(x.clone(), resolved_method.clone()),
                            typs.clone(),
                            args,
                        );
                        Ok((stms, ReturnValue::Some(mk_exp(call))))
                    } else if ret {
                        let (temp, temp_var) = state.next_temp(&expr.span, &expr.typ);
                        let temp_ident = state.declare_new_var(&temp, &expr.typ, false, false);
                        // tmp = StmX::Call;
                        let dest = Dest {
                            dest: var_loc_exp(&expr.span, &expr.typ, temp_ident.clone()),
                            is_init: true,
                        };
                        stms.push(stm_call(
                            ctx,
                            state,
                            &expr.span,
                            x.clone(),
                            resolved_method.clone(),
                            typs.clone(),
                            args.clone(),
                            Some(dest),
                        )?);
                        // REVIEW: this emits a StmX::Assign to set the value of the destination when,
                        // in recommends checking, the StmX::Call is used to check its recommends, however
                        // we only do this here, and not in the similar cases in for `ExprX::Assign` and
                        // `StmtX::Decl` where the right-hand-side is an `ExprX::Call`.
                        // That may cause recommends incompleteness. We should either use this case for all
                        // calls, or add this special case to `ExprX::Assign` and `StmtX::Decl`.
                        if state.checking_recommends(ctx)
                            || state.checking_spec_decreases(ctx, &x, &resolved_method)
                        {
                            let fun = get_function(ctx, &expr.span, &x)?;
                            if fun.x.mode == Mode::Spec {
                                // for recommends, we need a StmX::Call for the recommends
                                // and an ExpX::Call for the value.
                                let call = ExpX::Call(
                                    CallFun::Fun(x.clone(), resolved_method.clone()),
                                    typs.clone(),
                                    args,
                                );
                                let call = SpannedTyped::new(&expr.span, &expr.typ, call);
                                stms.push(init_var(&expr.span, &temp_ident, &call));
                            }
                        }
                        // tmp
                        Ok((stms, ReturnValue::Some(temp_var)))
                    } else {
                        // StmX::Call
                        stms.push(stm_call(
                            ctx,
                            state,
                            &expr.span,
                            x.clone(),
                            resolved_method,
                            typs.clone(),
                            args,
                            None,
                        )?);
                        Ok((stms, ReturnValue::ImplicitUnit(expr.span.clone())))
                    }
                }
            }
        }
        ExprX::Tuple(_) => {
            panic!("internal error: Tuple should have been simplified by ast_simplify")
        }
        ExprX::Ctor(p, i, binders, update) => {
            assert!(update.is_none()); // should be simplified by ast_simplify
            let mut stms: Vec<Stm> = Vec::new();
            let mut args: Vec<Binder<Exp>> = Vec::new();
            for binder in binders.iter() {
                let (mut stms1, e1) = expr_to_stm_opt(ctx, state, &binder.a)?;
                stms.append(&mut stms1);
                let e1 = unwrap_or_return_never!(e1, stms);
                let arg = BinderX { name: binder.name.clone(), a: e1 };
                args.push(Arc::new(arg));
            }
            let ctor = ExpX::Ctor(p.clone(), i.clone(), Arc::new(args));
            Ok((stms, ReturnValue::Some(mk_exp(ctor))))
        }
        ExprX::NullaryOpr(op) => {
            Ok((vec![], ReturnValue::Some(mk_exp(ExpX::NullaryOpr(op.clone())))))
        }
        ExprX::Unary(op @ UnaryOp::InferSpecForLoopIter { .. }, spec_expr) => {
            let spec_exp = expr_to_pure_exp_skip_checks(ctx, state, &spec_expr)?;
            let infer_exp = mk_exp(ExpX::Unary(*op, spec_exp));
            Ok((vec![], ReturnValue::Some(infer_exp)))
        }
        ExprX::Unary(op, exprr) => {
            let (mut stms, exp) = expr_to_stm_opt(ctx, state, exprr)?;
            let exp = unwrap_or_return_never!(exp, stms);
            if let (true, UnaryOp::Clip { truncate: false, .. }) =
                (state.checking_recommends(ctx), op)
            {
                let unary = UnaryOpr::HasType(expr.typ.clone());
                let has_type = ExpX::UnaryOpr(unary, exp.clone());
                let has_type = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), has_type);
                let error = crate::messages::error(
                    &expr.span,
                    "recommendation not met: value may be out of range of the target type (use `#[verifier(truncate)]` on the cast to silence this warning)",
                );
                let assert = StmX::Assert(Some(error), has_type);
                let assert = Spanned::new(expr.span.clone(), assert);
                stms.push(assert);
            }
            Ok((stms, ReturnValue::Some(mk_exp(ExpX::Unary(*op, exp)))))
        }
        ExprX::UnaryOpr(op, expr) => {
            let (mut stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
            let exp = unwrap_or_return_never!(exp, stms);
            match (op, state.checking_recommends(ctx)) {
                (
                    UnaryOpr::Field(FieldOpr {
                        datatype,
                        variant,
                        field: _,
                        get_variant: _,
                        check: VariantCheck::Yes,
                    }),
                    false,
                ) => {
                    let unary = UnaryOpr::IsVariant {
                        datatype: datatype.clone(),
                        variant: variant.clone(),
                    };
                    let is_variant = ExpX::UnaryOpr(unary, exp.clone());
                    let is_variant =
                        SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), is_variant);
                    let error = crate::messages::error(
                        &expr.span,
                        "requirement not met: to access this field, the union must be in the correct variant",
                    );
                    let assert = StmX::Assert(Some(error), is_variant);
                    let assert = Spanned::new(expr.span.clone(), assert);
                    stms.push(assert);
                }
                _ => {}
            }
            Ok((stms, ReturnValue::Some(mk_exp(ExpX::UnaryOpr(op.clone(), exp)))))
        }
        ExprX::Binary(op, e1, e2) => {
            // Handle short-circuiting, when applicable.
            // The pair (proceed_on, other) means:
            // If e1 evaluates to `proceed_on`, then evaluate and
            // return e2; otherwise, return the value `other`
            // (without evaluating `e2`).
            // Also note: if `e2` is a pure expression, we don't need to do the
            // special handling.
            let short_circuit = match op {
                BinaryOp::And => Some((true, false)),
                BinaryOp::Implies => Some((true, true)),
                BinaryOp::Or => Some((false, true)),
                _ => None,
            };
            let (mut stms1, e1) = expr_to_stm_opt(ctx, state, e1)?;
            let (mut stms2, e2) = expr_to_stm_opt(ctx, state, e2)?;
            match (short_circuit, stms2.len()) {
                (Some((proceed_on, other)), n) if n > 0 => {
                    // and:
                    //   if e1 { stmts2; e2 } else { false }
                    // implies:
                    //   if e1 { stmts2; e2 } else { true }
                    // or:
                    //   if e1 { true } else { stmts2; e2 }
                    let bx = ExpX::Const(Constant::Bool(other));
                    let b = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), bx);
                    let b = ReturnValue::Some(b);
                    if proceed_on {
                        Ok(if_to_stm(state, expr, stms1, &e1, stms2, &e2, vec![], &b))
                    } else {
                        Ok(if_to_stm(state, expr, stms1, &e1, vec![], &b, stms2, &e2))
                    }
                }
                _ => {
                    let e1 = unwrap_or_return_never!(e1, stms1);
                    stms1.append(&mut stms2);
                    let e2 = unwrap_or_return_never!(e2, stms1);
                    let bin = mk_exp(ExpX::Binary(*op, e1.clone(), e2.clone()));

                    if let BinaryOp::Arith(arith, arith_mode) = op {
                        // Insert bounds check

                        match (
                            arith_mode,
                            state.checking_bounds_for_mode(ctx, *arith_mode),
                            &*undecorate_typ(&expr.typ),
                        ) {
                            (_, false, _) => {}
                            (Mode::Exec, true, TypX::Int(ir)) if ir.is_bounded() => {
                                let (assert_exp, msg) = match arith {
                                    ArithOp::Add | ArithOp::Sub | ArithOp::Mul => {
                                        let unary = UnaryOpr::HasType(expr.typ.clone());
                                        let has_type = ExpX::UnaryOpr(unary, bin.clone());
                                        let has_type = SpannedTyped::new(
                                            &expr.span,
                                            &Arc::new(TypX::Bool),
                                            has_type,
                                        );
                                        (has_type, "possible arithmetic underflow/overflow")
                                    }
                                    ArithOp::EuclideanDiv | ArithOp::EuclideanMod => {
                                        let zero = ExpX::Const(Constant::Int(BigInt::zero()));
                                        let ne =
                                            ExpX::Binary(BinaryOp::Ne, e2.clone(), e2.new_x(zero));
                                        let ne = SpannedTyped::new(
                                            &expr.span,
                                            &Arc::new(TypX::Bool),
                                            ne,
                                        );
                                        (ne, "possible division by zero")
                                    }
                                };
                                let error = error(&expr.span, msg);
                                let assert = StmX::Assert(Some(error), assert_exp);
                                let assert = Spanned::new(expr.span.clone(), assert);
                                stms1.push(assert);
                            }
                            _ => {}
                        }
                    }

                    // Add overflow checks for bit shifts
                    // For a shift `a << b` or `a >> b`, Rust requires that
                    //    0 <= b < (bitsize of a)
                    // However, for spec code, this is extended in the obvious way to
                    // integers outside the range (at least, for b >= 0).
                    // So we don't need to do a check for here spec code.

                    if let BinaryOp::Bitwise(bitwise, mode) = op {
                        match (*mode, state.checking_bounds_for_mode(ctx, *mode), bitwise) {
                            (_, false, _) => {}
                            (Mode::Exec, true, BitwiseOp::Shr | BitwiseOp::Shl) => {
                                let zero = sst_int_literal(&expr.span, 0);
                                let bitwidth =
                                    bitwidth_sst_from_typ(&expr.span, &e1.typ, &ctx.global.arch);
                                let assert_exp = sst_conjoin(
                                    &expr.span,
                                    &vec![
                                        sst_le(&expr.span, &zero, &e2),
                                        sst_lt(&expr.span, &e2, &bitwidth),
                                    ],
                                );

                                let msg = "possible bit shift underflow/overflow";
                                let error = error(&expr.span, msg);
                                let assert = StmX::Assert(Some(error), assert_exp);
                                let assert = Spanned::new(expr.span.clone(), assert);
                                stms1.push(assert);
                            }
                            (Mode::Proof | Mode::Spec, true, BitwiseOp::Shr | BitwiseOp::Shl) => {}
                            (_, true, BitwiseOp::BitXor | BitwiseOp::BitAnd | BitwiseOp::BitOr) => {
                                // no overflow check needed
                            }
                        }
                    }

                    Ok((stms1, ReturnValue::Some(bin)))
                }
            }
        }
        ExprX::BinaryOpr(op, e1, e2) => {
            let (mut stms1, e1) = expr_to_stm_opt(ctx, state, e1)?;
            let (mut stms2, e2) = expr_to_stm_opt(ctx, state, e2)?;
            let e1 = unwrap_or_return_never!(e1, stms1);
            stms1.append(&mut stms2);
            let e2 = unwrap_or_return_never!(e2, stms1);
            let bin = mk_exp(ExpX::BinaryOpr(op.clone(), e1, e2));
            Ok((stms1, ReturnValue::Some(bin)))
        }
        ExprX::Multi(..) => {
            panic!("internal error: Multi should have been simplified by ast_simplify")
        }
        ExprX::Quant(quant, binders, body) => {
            let check_stms = check_pure_expr_bind(ctx, state, binders, body)?;
            state.push_scope();
            state.declare_binders(binders);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions with check_pure_expr_bind
            let exp = expr_to_pure_exp_skip_checks(ctx, state, body)?;
            state.pop_scope();
            let trigs = Arc::new(vec![]); // real triggers will be set by finalize_exp
            let bnd = Spanned::new(body.span.clone(), BndX::Quant(*quant, binders.clone(), trigs));
            let e = mk_exp(ExpX::Bind(bnd, exp));
            let e = mk_exp(ExpX::Unary(UnaryOp::MustBeFinalized, e));
            Ok((check_stms, ReturnValue::Some(e)))
        }
        ExprX::Closure(params, body) => {
            state.disable_recommends += 1;
            let check_stms = check_pure_expr_bind(ctx, state, params, body)?;
            // Note: to avoid false alarms, we don't check recommends inside closures
            // (since there's no precondition on the closure parameters)
            state.push_scope();
            state.declare_binders(params);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions with check_pure_expr_bind
            let mut exp = expr_to_pure_exp_skip_checks(ctx, state, body)?;
            state.pop_scope();

            // Parameters and return types must be boxed, so insert necessary box/unboxing
            match &*body.typ {
                TypX::TypParam(_) | TypX::Boxed(_) | TypX::Projection { .. } => {}
                _ => {
                    let boxed_typ = Arc::new(TypX::Boxed(body.typ.clone()));
                    let boxx = ExpX::UnaryOpr(UnaryOpr::Box(body.typ.clone()), exp);
                    exp = SpannedTyped::new(&body.span, &boxed_typ, boxx);
                }
            }
            let mut let_box_binds: Vec<Binder<Exp>> = Vec::new();
            let mut boxed_params: Vec<Binder<Typ>> = Vec::new();
            for p in params.iter() {
                match &*p.a {
                    TypX::TypParam(_) | TypX::Boxed(_) | TypX::Projection { .. } => {
                        boxed_params.push(p.clone());
                    }
                    _ => {
                        let boxed_typ = Arc::new(TypX::Boxed(p.a.clone()));
                        boxed_params.push(p.new_a(boxed_typ.clone()));
                        let varx = ExpX::Var(unique_bound(&p.name));
                        let var = SpannedTyped::new(&expr.span, &boxed_typ, varx);
                        let unboxx = ExpX::UnaryOpr(UnaryOpr::Unbox(p.a.clone()), var);
                        let unbox = SpannedTyped::new(&expr.span, &p.a, unboxx);
                        let_box_binds.push(p.new_a(unbox));
                    }
                };
            }
            if let_box_binds.len() != 0 {
                let bnd = Spanned::new(body.span.clone(), BndX::Let(Arc::new(let_box_binds)));
                exp = SpannedTyped::new(&body.span, &exp.typ, ExpX::Bind(bnd, exp.clone()));
            }

            let trigs = Arc::new(vec![]); // real triggers will be set by finalize_exp
            let bnd = Spanned::new(body.span.clone(), BndX::Lambda(Arc::new(boxed_params), trigs));
            state.disable_recommends -= 1;
            Ok((check_stms, ReturnValue::Some(mk_exp(ExpX::Bind(bnd, exp)))))
        }
        ExprX::ExecClosure { params, body, requires, ensures, ret, external_spec } => {
            let mut all_stms = Vec::new();

            // Emit the internals of the closure (ClosureInner behaves like a dead-end)
            // This includes assuming the requires, asserting the ensures, everything else

            let (inner_stms, typ_inv_vars) =
                exec_closure_body_stms(ctx, state, params, ret, body, requires, ensures)?;
            let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(inner_stms)));
            let clos =
                Spanned::new(expr.span.clone(), StmX::ClosureInner { body: block, typ_inv_vars });
            all_stms.push(clos);

            // Create the closure object and assume all the information given in its
            // specification that the world external to the closure gets to assume.

            let (cid, cexpr) = external_spec
                .as_ref()
                .expect("external_spec should have been added in ast_simplifiy");
            state.push_scope();
            let uid = state.declare_new_var(&cid, &expr.typ, false, false);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions in exec_closure_body_stms
            let cexp = expr_to_pure_exp_skip_checks(ctx, state, &cexpr)?;
            state.pop_scope();

            all_stms.push(Spanned::new(expr.span.clone(), StmX::Assume(cexp)));

            let v = mk_exp(ExpX::Var(uid));

            Ok((all_stms, ReturnValue::Some(v)))
        }
        ExprX::ArrayLiteral(elems) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut exps: Vec<Exp> = Vec::new();
            for elem in elems.iter() {
                let (mut stms0, e0) = expr_to_stm_opt(ctx, state, elem)?;
                stms.append(&mut stms0);
                let e0 = match e0.to_value() {
                    Some(e) => e,
                    None => {
                        return Ok((stms, ReturnValue::Never));
                    }
                };
                exps.push(e0);
            }

            let (tmp_ident, _tmp_exp) = state.next_temp(&expr.span, &expr.typ);
            let uid = state.declare_new_var(&tmp_ident, &expr.typ, false, false);
            let v = mk_exp(ExpX::Var(uid));

            // assume the type invariant
            // (this implies that v.len() == len because of a vstd axiom,
            // array_len_matches_n)
            let has_typ = sst_has_type(&expr.span, &v, &expr.typ);
            stms.push(Spanned::new(expr.span.clone(), StmX::Assume(has_typ)));
            for (i, exp) in exps.into_iter().enumerate() {
                // assume v[i] == exp
                let elem_i_eq = sst_equal(
                    &expr.span,
                    &sst_array_index(ctx, &expr.span, &v, &sst_int_literal(&expr.span, i as i128)),
                    &exp,
                );
                stms.push(Spanned::new(expr.span.clone(), StmX::Assume(elem_i_eq)));
            }

            Ok((stms, ReturnValue::Some(v)))
        }
        ExprX::ExecFnByName(fun) => {
            let v = mk_exp(ExpX::ExecFnByName(fun.clone()));
            Ok((vec![], ReturnValue::Some(v)))
        }
        ExprX::Choose { params, cond, body } => {
            let mut check_stms = check_pure_expr_bind(ctx, state, params, cond)?;
            check_stms.extend(check_pure_expr_bind(ctx, state, params, body)?);
            state.push_scope();
            state.declare_binders(&params);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions with check_pure_expr_bind
            let cond_exp = expr_to_pure_exp_skip_checks(ctx, state, cond)?;
            let body_exp = expr_to_pure_exp_skip_checks(ctx, state, body)?;
            state.pop_scope();
            let trigs = Arc::new(vec![]); // real triggers will be set by finalize_exp
            let bnd_choosex = BndX::Choose(params.clone(), trigs.clone(), cond_exp.clone());
            let bnd_choose = Spanned::new(body.span.clone(), bnd_choosex);
            let e_choose = mk_exp(ExpX::Bind(bnd_choose, body_exp));
            let e_choose = mk_exp(ExpX::Unary(UnaryOp::MustBeFinalized, e_choose));
            if state.checking_recommends(ctx) {
                let quant = crate::ast::Quant { quant: air::ast::Quant::Exists };
                let bnd_exists =
                    Spanned::new(body.span.clone(), BndX::Quant(quant, params.clone(), trigs));
                let e_exists = mk_exp(ExpX::Bind(bnd_exists, cond_exp.clone()));
                let e_exists = mk_exp(ExpX::Unary(UnaryOp::MustBeFinalized, e_exists));
                let error = error(
                    &cond_exp.span,
                    "recommendation not met: cannot prove that there exists values that satisfy the condition of the choose expression",
                );
                let assertx = StmX::Assert(Some(error), e_exists);
                check_stms.push(Spanned::new(cond_exp.span.clone(), assertx));
            }
            Ok((check_stms, ReturnValue::Some(e_choose)))
        }
        ExprX::WithTriggers { triggers, body } => {
            let mut trigs: Vec<crate::sst::Trig> = Vec::new();
            for trigger in triggers.iter() {
                // Use expr_to_pure_exp_skip_checks,
                // because spec preconditions are not checked in triggers
                // because they are just hints for quantifier instantiation
                let t =
                    vec_map_result(&**trigger, |e| expr_to_pure_exp_skip_checks(ctx, state, e))?;
                trigs.push(Arc::new(t));
            }
            let trigs = Arc::new(trigs);
            let (check_stms, body_exp) = expr_to_pure_exp_check(ctx, state, body)?;
            Ok((check_stms, ReturnValue::Some(mk_exp(ExpX::WithTriggers(trigs, body_exp)))))
        }
        ExprX::Fuel(x, fuel) => {
            // It's possible that the function may have pruned out of the crate
            // because there are no transitive dependencies.
            // If so, just skip the fuel/reveal statement entirely
            // (it can't possibly have any effect)
            let skip = !ctx.func_map.contains_key(x);

            if skip {
                state.diagnostics.report(&warning(
                    &expr.span, "this reveal/fuel statement has no effect because no verification condition in this module depends on this function").to_any());
            }

            let stms = if skip {
                vec![]
            } else {
                let stm = Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel));
                vec![stm]
            };
            Ok((stms, ReturnValue::ImplicitUnit(expr.span.clone())))
        }
        ExprX::RevealString(path) => {
            let stm = Spanned::new(expr.span.clone(), StmX::RevealString(path.clone()));
            Ok((vec![stm], ReturnValue::ImplicitUnit(expr.span.clone())))
        }
        ExprX::Header(_) => {
            return Err(error(&expr.span, "header expression not allowed here"));
        }
        ExprX::AssertAssume { is_assume: false, expr: e } => {
            if state.checking_recommends(ctx) {
                let (mut stms, exp) = expr_to_stm_or_error(ctx, state, e)?;
                let stm = Spanned::new(expr.span.clone(), StmX::Assume(exp));
                stms.push(stm);
                Ok((stms, ReturnValue::ImplicitUnit(expr.span.clone())))
            } else {
                let mut stms: Vec<Stm> = Vec::new();
                let split = crate::split_expression::need_split_expression(ctx, &e.span);
                // Use expr_to_pure_exp_skip_checks,
                // because we checked spec preconditions above with expr_to_stm_or_error
                let exp = expr_to_pure_exp_skip_checks(ctx, state, e)?;
                let exp = crate::heuristics::insert_ext_eq_in_assert(ctx, &exp);
                let small = is_small_exp_or_loc(&exp);
                let exp = if small || split {
                    exp.clone()
                } else {
                    // To avoid copying exp in Assert and Assume,
                    // put exp into a temporary variable
                    let (temp, temp_var) = state.next_temp(&exp.span, &exp.typ);
                    let temp_id = state.declare_new_var(&temp, &exp.typ, false, false);
                    stms.push(init_var(&exp.span, &temp_id, &exp));
                    temp_var
                };
                stms.push(Spanned::new(e.span.clone(), StmX::Assert(None, exp.clone())));
                stms.push(Spanned::new(e.span.clone(), StmX::Assume(exp)));
                Ok((stms, ReturnValue::ImplicitUnit(expr.span.clone())))
            }
        }
        ExprX::AssertAssume { is_assume: true, expr: e } => {
            // Use expr_to_pure_exp_skip_checks,
            // because the goal of assume is to add an assumption, not to perform checks
            let exp = expr_to_pure_exp_skip_checks(ctx, state, e)?;
            let stm = Spanned::new(expr.span.clone(), StmX::Assume(exp));
            Ok((vec![stm], ReturnValue::ImplicitUnit(expr.span.clone())))
        }
        ExprX::AssertBy { vars, require, ensure, proof } => {
            // deadend {
            //   assume(require)
            //   proof
            //   assert(ensure);
            // }
            // assume(forall vars. require ==> ensure)
            let mut stms: Vec<Stm> = Vec::new();

            // Translate proof into a dead-end ending with an assert
            state.push_scope();
            let mut body: Vec<Stm> = Vec::new();
            for var in vars.iter() {
                let x = state.declare_new_var(&var.name, &var.a, false, true);
                body.push(assume_has_typ(&x, &var.a, &require.span));
            }
            let (mut proof_stms, e) = expr_to_stm_opt(ctx, state, proof)?;
            if let ReturnValue::Some(_) = e {
                return Err(error(
                    &expr.span,
                    "'assert ... by' block cannot end with an expression",
                ));
            }
            let (require_checks, require_exp) = expr_to_pure_exp_check(ctx, state, &require)?;
            body.extend(require_checks);
            let assume = Spanned::new(require.span.clone(), StmX::Assume(require_exp));
            body.push(assume);
            body.append(&mut proof_stms);
            if state.checking_spec_preconditions(ctx) {
                body.extend(check_pure_expr(ctx, state, &ensure)?);
            } else {
                // Use expr_to_pure_exp_skip_checks,
                // because we checked spec preconditions above with check_pure_expr
                let ensure_exp = expr_to_pure_exp_skip_checks(ctx, state, &ensure)?;
                let assert = Spanned::new(ensure.span.clone(), StmX::Assert(None, ensure_exp));
                body.push(assert);
            }
            let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(body)));
            let deadend = Spanned::new(expr.span.clone(), StmX::DeadEnd(block));
            stms.push(deadend);
            state.pop_scope();

            // Translate ensure into an assume
            let implyx = ExprX::Binary(BinaryOp::Implies, require.clone(), ensure.clone());
            let imply = SpannedTyped::new(&ensure.span, &Arc::new(TypX::Bool), implyx);
            let forallx = ExprX::Quant(QUANT_FORALL, vars.clone(), imply);
            let forall = SpannedTyped::new(&ensure.span, &Arc::new(TypX::Bool), forallx);
            // Use expr_to_pure_exp_skip_checks,
            // because we already checked spec preconditions for require and ensure above
            let forall_exp = expr_to_pure_exp_skip_checks(ctx, state, &forall)?;
            let assume = Spanned::new(ensure.span.clone(), StmX::Assume(forall_exp));
            stms.push(assume);
            Ok((stms, ReturnValue::ImplicitUnit(expr.span.clone())))
        }
        ExprX::AssertQuery { requires, ensures, proof, mode } => {
            // Note that `ExprX::AssertQuery` makes a separate query for AssertQueryMode::NonLinear and AssertQueryMode::BitVector
            // only `requires` and type invariants will be provided to prove `ensures`
            match mode {
                AssertQueryMode::NonLinear => {
                    let mut inner_body: Vec<Stm> = Vec::new();
                    let mut vars = BTreeMap::new(); // order vars by UniqueIdent

                    // Translate body as separate query
                    state.push_scope();
                    for r in requires.iter() {
                        let (require_check_recommends, require_exp) =
                            expr_to_pure_exp_check(ctx, state, &r)?;
                        inner_body.extend(require_check_recommends);
                        vars.extend(free_vars_exp(&require_exp).into_iter());
                        let assume = Spanned::new(r.span.clone(), StmX::Assume(require_exp));
                        inner_body.push(assume);
                    }

                    let (proof_stms, e) = expr_to_stm_opt(ctx, state, proof)?;
                    if let ReturnValue::Some(_) = e {
                        return Err(error(
                            &expr.span,
                            "'assert ... by' block cannot end with an expression",
                        ));
                    }
                    inner_body.extend(proof_stms);

                    for e in ensures.iter() {
                        if state.checking_spec_preconditions(ctx) {
                            let check_stms = check_pure_expr(ctx, state, &e)?;
                            for s in check_stms.iter() {
                                vars.extend(free_vars_stm(&s).into_iter());
                            }
                            inner_body.extend(check_stms);
                        } else {
                            // Use expr_to_pure_exp_skip_checks,
                            // because we checked spec preconditions above with check_pure_expr
                            let ensure_exp = expr_to_pure_exp_skip_checks(ctx, state, &e)?;
                            vars.extend(free_vars_exp(&ensure_exp).into_iter());
                            let assert =
                                Spanned::new(e.span.clone(), StmX::Assert(None, ensure_exp));
                            inner_body.push(assert);
                        }
                    }

                    let inner_body =
                        Spanned::new(expr.span.clone(), StmX::Block(Arc::new(inner_body)));
                    state.pop_scope();

                    let mut outer: Vec<Stm> = Vec::new();

                    // Translate as assert, assume in outer query
                    for r in requires.iter() {
                        if state.checking_spec_preconditions(ctx) {
                            outer.extend(check_pure_expr(ctx, state, &r)?);
                        } else {
                            // Use expr_to_pure_exp_skip_checks,
                            // because we checked spec preconditions above with check_pure_expr
                            let require_exp = expr_to_pure_exp_skip_checks(ctx, state, &r)?;
                            let assert = Spanned::new(
                                r.span.clone(),
                                StmX::Assert(
                                    Some(crate::messages::error(
                                        &r.span.clone(),
                                        "requires not satisfied".to_string(),
                                    )),
                                    require_exp,
                                ),
                            );
                            outer.push(assert);
                        }
                    }
                    for e in ensures.iter() {
                        // Use expr_to_pure_exp_skip_checks,
                        // because we already checked spec preconditions above with check_pure_expr
                        let ensure_exp = expr_to_pure_exp_skip_checks(ctx, state, &e)?;
                        let assume = Spanned::new(e.span.clone(), StmX::Assume(ensure_exp));
                        outer.push(assume);
                    }

                    let outer_block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(outer)));

                    let nonlinear = Spanned::new(
                        expr.span.clone(),
                        StmX::AssertQuery {
                            body: inner_body,
                            typ_inv_vars: Arc::new(vars.into_iter().collect()),
                            mode: *mode,
                        },
                    );
                    Ok((vec![outer_block, nonlinear], ReturnValue::ImplicitUnit(expr.span.clone())))
                }

                AssertQueryMode::BitVector => {
                    // check if assertion block is consisted only with requires/ensures
                    let (proof_stms, e) = expr_to_stm_opt(ctx, state, proof)?;
                    let proof_block_err =
                        Err(error(&expr.span, "assert_bitvector_by cannot contain a proof block"));
                    if let ReturnValue::Some(_) = e {
                        return Err(error(
                            &expr.span,
                            "assert_bitvector_by cannot contain a return value",
                        ));
                    }
                    if proof_stms.len() > 1 {
                        return proof_block_err;
                    }
                    if let StmX::Block(st) = &proof_stms[0].x {
                        if st.len() > 0 {
                            return proof_block_err;
                        }
                    } else {
                        return proof_block_err;
                    }

                    // translate requires/ensures expression
                    let mut requires_in = vec![];
                    let mut ensures_in = vec![];
                    let mut outer: Vec<Stm> = Vec::new();
                    state.push_scope();
                    // We won't have the context to check recommends, so skip them
                    state.disable_recommends += 1;
                    for r in requires.iter() {
                        let (check_stms, require_exp) = expr_to_pure_exp_check(ctx, state, &r)?;
                        outer.extend(check_stms);
                        requires_in.push(require_exp.clone());
                    }
                    for e in ensures.iter() {
                        let (check_stms, ensure_exp) = expr_to_pure_exp_check(ctx, state, &e)?;
                        outer.extend(check_stms);
                        ensures_in.push(ensure_exp.clone());
                    }
                    state.disable_recommends -= 1;
                    state.pop_scope();

                    // Translate as assert, assume in outer query
                    if !state.checking_recommends(&ctx) {
                        for r in requires.iter() {
                            // Use expr_to_pure_exp_skip_checks,
                            // because we checked spec preconditions above with expr_to_pure_exp_check
                            let require_exp = expr_to_pure_exp_skip_checks(ctx, state, &r)?;
                            let assert = Spanned::new(
                                r.span.clone(),
                                StmX::Assert(
                                    Some(error(
                                        &r.span.clone(),
                                        "requires not satisfied".to_string(),
                                    )),
                                    require_exp,
                                ),
                            );
                            outer.push(assert);
                        }
                    }
                    for e in ensures.iter() {
                        // Use expr_to_pure_exp_skip_checks,
                        // because we checked spec preconditions above with expr_to_pure_exp_check
                        let ensure_exp = expr_to_pure_exp_skip_checks(ctx, state, &e)?;
                        let assume = Spanned::new(e.span.clone(), StmX::Assume(ensure_exp));
                        outer.push(assume);
                    }
                    let outer_block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(outer)));

                    let bitvector = Spanned::new(
                        expr.span.clone(),
                        StmX::AssertBitVector {
                            requires: Arc::new(requires_in),
                            ensures: Arc::new(ensures_in),
                        },
                    );
                    Ok((vec![outer_block, bitvector], ReturnValue::ImplicitUnit(expr.span.clone())))
                }
            }
        }
        ExprX::AssertCompute(e, mode) => {
            // We won't have the context to check recommends, so skip them
            state.disable_recommends += 1;
            let (mut stms, expr) = expr_to_pure_exp_check(ctx, state, &e)?;
            state.disable_recommends -= 1;
            let ret = ReturnValue::ImplicitUnit(expr.span.clone());
            // We assert the (hopefully simplified) result of calling the interpreter
            // but assume the original expression, so we get the benefits
            // of any ensures, triggers, etc., that it might provide
            let interp_exp = eval_expr(
                &ctx.global,
                &state.finalize_exp(ctx, &state.fun_ssts, &expr)?,
                state.diagnostics,
                &mut state.fun_ssts,
                ctx.global.rlimit,
                ctx.global.arch,
                *mode,
                &mut ctx.global.interpreter_log.lock().unwrap(),
            )?;
            let err = error_with_label(
                &expr.span.clone(),
                "assertion failed",
                format!("simplified to {}", interp_exp.x.to_user_string(&ctx.global)),
            );
            if matches!(mode, ComputeMode::Z3) {
                let assert = Spanned::new(expr.span.clone(), StmX::Assert(Some(err), interp_exp));
                stms.push(assert);
            }
            let assume = Spanned::new(expr.span.clone(), StmX::Assume(expr));
            stms.push(assume);
            Ok((stms, ret))
        }
        ExprX::If(expr0, expr1, None) => {
            let (stms0, e0) = expr_to_stm_opt(ctx, state, expr0)?;
            let (stms1, e1) = expr_to_stm_opt(ctx, state, expr1)?;
            let stms2 = vec![];
            let e2 = ReturnValue::ImplicitUnit(expr.span.clone());
            Ok(if_to_stm(state, expr, stms0, &e0, stms1, &e1, stms2, &e2))
        }
        ExprX::If(expr0, expr1, Some(expr2)) => {
            let (stms0, e0) = expr_to_stm_opt(ctx, state, expr0)?;
            let (stms1, e1) = expr_to_stm_opt(ctx, state, expr1)?;
            let (stms2, e2) = expr_to_stm_opt(ctx, state, expr2)?;
            Ok(if_to_stm(state, expr, stms0, &e0, stms1, &e1, stms2, &e2))
        }
        ExprX::Match(..) => {
            panic!("internal error: Match should have been simplified by ast_simplify")
        }
        ExprX::Loop { is_for_loop, label, cond, body, invs } => {
            let has_break = loop_body_has_break(label, body);
            let simple_invs = invs.iter().all(|inv| inv.kind == LoopInvariantKind::Invariant);
            let simple_while = !has_break && simple_invs && cond.is_some();
            let mut cnd = if let Some(cond) = cond {
                let (stms0, e0) = expr_to_stm_opt(ctx, state, cond)?;
                let e0 = match e0 {
                    ReturnValue::Some(e0) => e0,
                    ReturnValue::ImplicitUnit(_) => {
                        panic!("while loop condition doesn't return a bool expression");
                    }
                    ReturnValue::Never => {
                        // If the condition never returns (which would be odd, but it
                        // could happen) then the body of the while loop never gets to go at all.
                        return Ok((stms0, ReturnValue::Never));
                    }
                };
                let block0 = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(stms0)));
                Some((block0, e0))
            } else {
                None
            };

            let (mut stms1, _e1) = expr_to_stm_opt(ctx, state, body)?;
            let mut check_recommends: Vec<Stm> = Vec::new();
            let mut invs1: Vec<crate::sst::LoopInv> = Vec::new();
            for inv in invs.iter() {
                let (rec, exp) = expr_to_pure_exp_check(ctx, state, &inv.inv)?;
                check_recommends.extend(rec);
                let (at_entry, at_exit) = match inv.kind {
                    LoopInvariantKind::Invariant if simple_while => (true, true),
                    LoopInvariantKind::Invariant => (true, false),
                    LoopInvariantKind::InvariantEnsures => (true, true),
                    LoopInvariantKind::Ensures => (false, true),
                };
                let inv1 = crate::sst::LoopInv { inv: exp, at_entry, at_exit };
                invs1.push(inv1);
            }
            if ctx.checking_spec_preconditions() {
                stms1.splice(0..0, check_recommends);
            }
            if !simple_while {
                // must be "loop", not "while"
                if let Some((c_stm, c_exp)) = cnd {
                    // convert while into loop
                    let not_c = c_exp.new_x(ExpX::Unary(UnaryOp::Not, c_exp.clone()));
                    let break_stmx = StmX::BreakOrContinue { label: None, is_break: true };
                    let break_stm = Spanned::new(c_exp.span.clone(), break_stmx);
                    let if_stm = Spanned::new(c_exp.span.clone(), StmX::If(not_c, break_stm, None));
                    stms1.insert(0, c_stm);
                    stms1.insert(1, if_stm);
                    cnd = None;
                }
            }
            let while_stm = Spanned::new(
                expr.span.clone(),
                StmX::Loop {
                    is_for_loop: *is_for_loop,
                    label: label.clone(),
                    cond: cnd,
                    body: stms_to_one_stm(&body.span, stms1),
                    invs: Arc::new(invs1),
                    // These are filled in later, in sst_vars
                    typ_inv_vars: Arc::new(vec![]),
                    modified_vars: Arc::new(vec![]),
                },
            );
            if can_control_flow_reach_after_loop(expr) {
                let ret = ReturnValue::ImplicitUnit(expr.span.clone());
                Ok((vec![while_stm], ret))
            } else {
                let stms = vec![while_stm, assume_false(&expr.span)];
                Ok((stms, ReturnValue::Never))
            }
        }
        ExprX::OpenInvariant(inv, binder, body, atomicity) => {
            // Evaluate `inv`
            let (mut stms0, big_inv_exp) = expr_to_stm_opt(ctx, state, inv)?;
            let big_inv_exp = unwrap_or_return_never!(big_inv_exp, stms0);

            // Assign it to a constant temp variable to ensure it is constant
            // across the entire block.
            let (temp, temp_var) = state.next_temp(&big_inv_exp.span, &inv.typ);
            let temp_id = state.declare_new_var(&temp, &inv.typ, false, false);
            stms0.push(init_var(&big_inv_exp.span, &temp_id, &big_inv_exp));

            // Process the body

            state.push_scope();
            let ident = state.declare_new_var(
                &binder.name,
                &binder.a,
                /* mutable */ true,
                /* maybe_need_rename */ true,
            );
            let (body_stms, body_e) = expr_to_stm_opt(ctx, state, body)?;
            state.pop_scope();

            let body_stm = stms_to_one_stm(&expr.span, body_stms);
            stms0.push(Spanned::new(
                expr.span.clone(),
                StmX::OpenInvariant(temp_var, ident, binder.a.clone(), body_stm, *atomicity),
            ));

            let _body_e = unwrap_or_return_never!(body_e, stms0);
            return Ok((stms0, ReturnValue::ImplicitUnit(expr.span.clone())));
        }
        ExprX::Return(e1) => {
            let (mut stms, ret_exp) = match e1 {
                None => (vec![], lowered_unit_value(&expr.span)),
                Some(e) => {
                    let (ret_stms, exp) = expr_to_stm_opt(ctx, state, e)?;
                    let exp = unwrap_or_return_never!(exp, ret_stms);

                    (ret_stms, exp)
                }
            };

            let containing_closure = state.containing_closure.clone();
            match &containing_closure {
                None => {
                    let base_error = error_with_label(
                        &expr.span,
                        crate::def::POSTCONDITION_FAILURE.to_string(),
                        "at this exit".to_string(),
                    );

                    stms.push(Spanned::new(
                        expr.span.clone(),
                        StmX::Return { base_error, ret_exp: Some(ret_exp), inside_body: true },
                    ));
                    stms.push(assume_false(&expr.span));
                }
                Some(closure_state) => {
                    closure_emit_postconditions(ctx, state, closure_state, &ret_exp, &mut stms);
                }
            }
            Ok((stms, ReturnValue::Never))
        }
        ExprX::BreakOrContinue { label, is_break } => {
            let stmx = StmX::BreakOrContinue { label: label.clone(), is_break: *is_break };
            let stm = Spanned::new(expr.span.clone(), stmx);
            Ok((vec![stm], ReturnValue::ImplicitUnit(expr.span.clone())))
        }
        ExprX::Ghost { .. } => {
            panic!("internal error: ExprX::Ghost should have been simplified by ast_simplify")
        }
        ExprX::Block(stmts, body_opt) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut local_decls: Vec<LocalDecl> = Vec::new();
            let mut binds: Vec<Bnd> = Vec::new();
            let mut is_pure_exp = true;
            let mut never_return = false;
            for stmt in stmts.iter() {
                let (mut stms0, e0, decl_bnd_opt) = stmt_to_stm(ctx, state, stmt)?;
                match decl_bnd_opt {
                    Some((decl, bnd)) => {
                        state.push_scope();
                        local_decls.push(decl.clone());
                        state.insert_unique_var(&decl.ident);
                        match bnd {
                            None => {
                                is_pure_exp = false;
                            }
                            Some(bnd) => {
                                binds.push(bnd);
                            }
                        }
                    }
                    None => {
                        // the statement wasn't a Decl; it could have been anything
                        is_pure_exp = false;
                    }
                }
                stms.append(&mut stms0);
                match e0 {
                    ReturnValue::Never => {
                        is_pure_exp = false;
                        never_return = true;
                        // Don't process any of the later statements: they are unreachable.
                        break;
                    }
                    _ => {}
                }
            }
            let exp = if never_return {
                ReturnValue::Never
            } else if let Some(expr) = body_opt {
                let (mut stms1, exp) = expr_to_stm_opt(ctx, state, expr)?;
                if stms1.len() > 0 {
                    is_pure_exp = false;
                }
                stms.append(&mut stms1);
                exp
            } else {
                ReturnValue::ImplicitUnit(expr.span.clone())
            };
            for _ in local_decls.iter() {
                state.pop_scope();
            }
            match exp {
                ReturnValue::Some(mut exp) if is_pure_exp => {
                    // Pure expression: fold decls into Let bindings and return a single expression
                    for bnd in binds.iter().rev() {
                        exp = SpannedTyped::new(
                            &expr.span,
                            &exp.typ,
                            ExpX::Bind(bnd.clone(), exp.clone()),
                        );
                    }
                    // We don't generate a LocalDecl, so we don't want to rename the variables
                    for decl in local_decls {
                        state.dont_rename.insert(decl.ident.clone());
                    }

                    assert!(!never_return);
                    return Ok((vec![], ReturnValue::Some(exp)));
                }
                _ => {
                    // Not pure: return statements + an expression
                    for decl in local_decls {
                        state.local_decls.push(decl);
                    }
                    let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(stms)));
                    Ok((vec![block], exp))
                }
            }
        }
    }
}

/// In the case that this stmt is a Decl, we also return the following information:
///
///    * An SST LocalDecl for the declaration
///    * Optionally, An SST Bnd for the declaration (only if the right-hand side is pure)
///
/// Thus, when the Bnd is available, the caller of this fn has the option of whether
/// to use the LocalDecl or the Bnd; they can use the Bnds in order to construct a pure
/// expression or LocalDecls to construct an impure one.
/// (Note: a declaration by itself being marked 'mutable' doesn't matter for determining
/// purity; it only matters if there are assignments later.)

fn stmt_to_stm(
    ctx: &Ctx,
    state: &mut State,
    stmt: &Stmt,
) -> Result<(Vec<Stm>, ReturnValue, Option<(LocalDecl, Option<Bnd>)>), VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => {
            let (stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
            Ok((stms, exp, None))
        }
        StmtX::Decl { pattern, mode: _, init } => {
            let (name, mutable) = match &pattern.x {
                PatternX::Var { name, mutable } => (name, mutable),
                _ => panic!("internal error: Decl should have been simplified by ast_simplify"),
            };

            let ident = state.alloc_unique_var(&name);
            let typ = pattern.typ.clone();
            let decl = Arc::new(LocalDeclX { ident, typ: typ.clone(), mutable: *mutable });

            // First check if the initializer needs to be translate to a Call instead
            // of an Exp. If so, translate it that way.
            if let Some(init) = init {
                match expr_must_be_call_stm(ctx, state, init)? {
                    Some((stms, ReturnedCall::Never)) => {
                        return Ok((stms, ReturnValue::Never, None));
                    }
                    Some((
                        mut stms,
                        ReturnedCall::Call { fun, resolved_method, typs, has_return: _, args },
                    )) => {
                        // Special case: convert to a Call
                        // It can't be pure in this case, so don't return a Bnd.
                        let dest = Dest {
                            dest: var_loc_exp(&pattern.span, &typ, decl.ident.clone()),
                            is_init: true,
                        };
                        stms.push(stm_call(
                            ctx,
                            state,
                            &init.span,
                            fun,
                            resolved_method,
                            typs,
                            args,
                            Some(dest),
                        )?);
                        // REVIEW: for a similar case in `ExprX::Call` we emit a StmX::Assign to set the
                        // value of the destination when, in recommends checking, the StmX::Call is used
                        // to check its recommends, however we do not do this here.
                        // That may cause recommends incompleteness. We should either use the `ExprX::Call`
                        // special-case for recommends here, or replace this logic with a recursive call
                        // to handle the right-hand-side, if possible.
                        let ret = ReturnValue::ImplicitUnit(stmt.span.clone());
                        return Ok((stms, ret, Some((decl, None))));
                    }
                    None => {}
                }
            }

            // Otherwise, translate the initializer to an Exp.

            let (mut stms, exp) = match init {
                None => (vec![], None),
                Some(init) => {
                    let (stms, exp) = expr_to_stm_opt(ctx, state, init)?;
                    let exp = match exp.to_value() {
                        Some(exp) => exp,
                        None => {
                            return Ok((stms, ReturnValue::Never, None));
                        }
                    };
                    (stms, Some(exp))
                }
            };

            // For a pure expression (i.e., one with no SST statements), return a binder
            let bnd = match &exp {
                Some(exp) if stms.len() == 0 => {
                    let binder = BinderX { name: name.clone(), a: exp.clone() };
                    let bnd = BndX::Let(Arc::new(vec![Arc::new(binder)]));
                    Some(Spanned::new(stmt.span.clone(), bnd))
                }
                _ => None,
            };

            match (*mutable, &exp) {
                (false, None) => {}
                (true, None) => {}
                (_, Some(exp)) => {
                    stms.push(init_var(&stmt.span, &decl.ident, exp));
                }
            }

            let ret = ReturnValue::ImplicitUnit(stmt.span.clone());
            Ok((stms, ret, Some((decl, bnd))))
        }
    }
}

/// Handle the internal of a closure

fn exec_closure_body_stms(
    ctx: &Ctx,
    state: &mut State,
    params: &Binders<Typ>,
    ret: &Binder<Typ>,
    body: &Expr,
    requires: &Exprs,
    ensures: &Exprs,
) -> Result<(Vec<Stm>, Arc<Vec<(UniqueIdent, Typ)>>), VirErr> {
    let mut typ_inv_vars = vec![];

    state.push_scope();
    for param in params.iter() {
        let uid = state.declare_new_var(&param.name, &param.a, false, false);
        typ_inv_vars.push((uid, param.a.clone()));
    }

    // Assert all the requires

    let mut stms = Vec::new();
    for req in requires.iter() {
        let (check_stms, exp) = expr_to_pure_exp_check(ctx, state, req)?;
        stms.extend(check_stms);
        let stm = Spanned::new(req.span.clone(), StmX::Assume(exp));
        stms.push(stm);
    }

    state.declare_new_var(&ret.name, &ret.a, false, false);
    let dest = unique_local(&ret.name);

    let mut ens_exps = Vec::new();
    let mut ens_checks = Vec::new();
    for ens in ensures.iter() {
        let (check_stms, exp) = expr_to_pure_exp_check(ctx, state, ens)?;
        ens_checks.extend(check_stms);
        ens_exps.push(exp);
    }

    // Set up the ClosureState so any 'return' statements inside know what to do

    let mut containing_closure = Some(ClosureState {
        ensures: Arc::new(ens_exps),
        dest: dest,
        ensures_checks: Arc::new(ens_checks),
    });
    std::mem::swap(&mut state.containing_closure, &mut containing_closure);

    let (mut body_stms, exp) = expr_to_stm_opt(ctx, state, body)?;
    stms.append(&mut body_stms);

    std::mem::swap(&mut state.containing_closure, &mut containing_closure);

    match exp.to_value() {
        Some(e) => {
            // Post condition for the return-value expression

            let closure_state = containing_closure.as_ref().unwrap();
            closure_emit_postconditions(ctx, state, closure_state, &e, &mut stms);
        }
        None => { /* never-return case */ }
    }

    state.pop_scope();

    Ok((stms, Arc::new(typ_inv_vars)))
}

fn closure_emit_postconditions(
    ctx: &Ctx,
    state: &mut State,
    containing_closure: &ClosureState,
    ret_value: &Exp,
    stms: &mut Vec<Stm>,
) {
    let ClosureState { dest, ensures, ensures_checks } = containing_closure;
    stms.extend(ensures_checks.iter().cloned());
    if ensures.len() > 0 && !state.checking_spec_preconditions(ctx) {
        stms.push(init_var(&ret_value.span, dest, &ret_value));
        for ens in ensures.iter() {
            let er = error_with_label(
                &ret_value.span,
                "unable to prove post-condition of closure",
                "returning this expression",
            )
            .secondary_label(&ens.span, crate::def::THIS_POST_FAILED);
            let stm = Spanned::new(ens.span.clone(), StmX::Assert(Some(er), ens.clone()));
            stms.push(stm);
        }
    }
}
