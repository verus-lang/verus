use crate::ast::{
    ArithOp, AssertQueryMode, AutospecUsage, BinaryOp, BitshiftBehavior, BitwiseOp, BoundsCheck,
    ByRef, CallTarget, ComputeMode, Constant, Div0Behavior, Expr, ExprX, FieldOpr, Fun, Function,
    Ident, IntRange, InvAtomicity, LoopInvariantKind, MaskSpec, Mode, OverflowBehavior,
    PatternBinding, PatternX, Place, PlaceX, SpannedTyped, Stmt, StmtX, Typ, TypX, Typs, UnaryOp,
    UnaryOpr, VarAt, VarBinder, VarBinderX, VarBinders, VarIdent, VarIdentDisambiguate,
    VariantCheck, VirErr,
};
use crate::ast::{BuiltinSpecFun, Exprs};
use crate::ast_util::{
    QUANT_FORALL, bool_typ, place_to_expr, types_equal, undecorate_typ, unit_typ,
};
use crate::context::Ctx;
use crate::def::{Spanned, unique_local};
use crate::inv_masks::MaskSet;
use crate::messages::{Span, ToAny, error, error_with_secondary_label, internal_error, warning};
use crate::sst::{
    Bnd, BndX, CallFun, Dest, Exp, ExpX, Exps, InternalFun, LocalDecl, LocalDeclKind, LocalDeclX,
    ParPurpose, Pars, Stm, StmX, UniqueIdent,
};
use crate::sst_util::{
    sst_bitwidth, sst_conjoin, sst_equal, sst_int_literal, sst_le, sst_lt, sst_mut_ref_current,
    sst_unit_value, subst_exp, subst_pre_local_decl, subst_stm,
};
use crate::sst_visitor::{map_exp_visitor, map_stm_exp_visitor, map_stm_visitor};
use crate::util::vec_map_result;
use crate::visitor::VisitorControlFlow;
use air::ast::{Binder, BinderX};
use air::messages::Diagnostics;
use air::scope_map::ScopeMap;
use indexmap::IndexSet;
use num_bigint::BigInt;
use num_traits::identities::Zero;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone)]
pub(crate) struct ClosureState {
    ensures: Exps,
    // recommends to check the well-formedness of the ensures clauses themselves
    ensures_checks: crate::sst::Stms,
    dest: UniqueIdent,
}

#[derive(Clone, Copy)]
pub(crate) struct Immutable(pub LocalDeclKind);

#[derive(Clone, Copy)]
pub(crate) enum PreLocalDeclKind {
    /// Any 'immutable' kind
    Immutable(Immutable),
    /// Param (mutability to be inferred)
    Param,
    /// StmtLet (mutability to be inferred)
    StmtLet,
    /// Param, always consider mut
    MutParam,
}

#[derive(Clone)]
pub(crate) struct PreLocalDecl {
    pub ident: VarIdent,
    pub typ: Typ,
    pub kind: PreLocalDeclKind,
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
    pre_local_decls: Vec<PreLocalDecl>,
    // Populated by finalize_stm
    mutated_var_idents: HashMap<VarIdent, Span>,
    // Rename variables when needed, using unique integers, to avoid collisions.
    rename_map: ScopeMap<VarIdent, VarIdent>,
    // Track which variable Ident have potentially been used in this scope as Exp-bound
    // (used to remove the numeric id from an Exp-bound variable when it can't
    // shadow another Exp-bound variable)
    rename_exp_idents: ScopeMap<Ident, ()>,
    // Next integer to use for renaming each variable
    rename_counters: HashMap<Ident, u64>,
    // Decide final name in a second pass, when a decision has been made on whether the
    // variable is Exp-bound or Stm-bound.  (We start with Stm-bound, and replace with
    // Exp-bound if possible.)
    rename_delayed: HashMap<VarIdent, VarIdent>,
    // If > 0, we're making a second pass over AST to generate just a pure Exp, with no Stms.
    // Rationale: in the first pass, when checking preconditions of spec functions
    // (e.g. recommends), we may have to generate Stms for the precondition checking,
    // and we may have to generate LocalDecl to support the Stms rather than Exp::Bind.
    // In some situations (e.g. inside a quantifier), we need a pure Exp with Exp::Bind
    // and no Stms instead, so we make a second pass to generate this.
    only_generate_pure_exp: u64,
    // If > 0, disable checking recommends
    pub(crate) disable_recommends: u64,
    // Diagnostic output
    pub diagnostics: &'a (dyn Diagnostics + 'a),
    // If inside a closure
    containing_closure: Option<ClosureState>,
    // Statics that are referenced (not counting statics in loops)
    statics: IndexSet<Fun>,
    pub assert_id_counter: u64,
    loop_id_counter: u64,

    pub mask: Option<MaskSet>,
}

pub(crate) struct FinalState {
    pub local_decls: Vec<LocalDecl>,
    pub statics: IndexSet<Fun>,
}

/// Used to represent the result of a computation that might not terminate
#[derive(Clone, Debug)]
pub(crate) enum Maybe<T> {
    Some(T),
    Never,
}

/// An Exp that remembers if it comes from an "implicit unit"
#[derive(Clone, Debug)]
pub(crate) enum Value {
    Exp(Exp),
    ImplicitUnit(Span),
}

impl Value {
    /// Turn this into a normal Exp
    fn to_exp(self) -> Exp {
        match self {
            Value::Exp(e) => e,
            Value::ImplicitUnit(span) => sst_unit_value(&span),
        }
    }
}

impl Maybe<Value> {
    /// Map `to_exp` over the Some case
    fn to_maybe_exp(self) -> Maybe<Exp> {
        match self {
            Maybe::Some(val) => Maybe::Some(val.to_exp()),
            Maybe::Never => Maybe::Never,
        }
    }

    /// Expect the Some case and return the Exp; panic on the Never case
    fn expect_exp(self) -> Exp {
        match self {
            Maybe::Some(val) => val.to_exp(),
            Maybe::Never => panic!("Maybe::Never unexpected here"),
        }
    }
}

/// Unwraps a Maybe while possibly returning Never. This is sort of like `?`
/// but also deals with the fact that we need to return Stms.
///
/// Specifically: `unwrap_or_return_never!(e, stms)` either unwraps `e` or return
/// `(stms, Maybe::Never)`
macro_rules! unwrap_or_return_never {
    ($e:expr, $stms:expr) => {
        match $e {
            Maybe::Some(e) => e,
            Maybe::Never => {
                return Ok(($stms, Maybe::Never));
            }
        }
    };
    ($e:expr, $stms:expr, $stms2:expr) => {
        match $e {
            Maybe::Some(e) => e,
            Maybe::Never => {
                let mut all_stms = $stms;
                all_stms.extend($stms2);
                return Ok((all_stms, Maybe::Never));
            }
        }
    };
}

/// Like unwrap_or_return_never, but also converts the Value to an Exp
macro_rules! to_exp_or_return_never {
    ($e:expr, $stms:expr) => {
        match $e.to_maybe_exp() {
            Maybe::Some(e) => e,
            Maybe::Never => {
                return Ok(($stms, Maybe::Never));
            }
        }
    };
}

/// Checks the output of Sequencer::push and returns Never if necessary
macro_rules! push_or_return_never {
    ($e:expr) => {
        match $e {
            Some(stms) => {
                return Ok((stms, Maybe::Never));
            }
            None => {}
        }
    };
}

impl<'a> State<'a> {
    pub fn new(diagnostics: &'a dyn Diagnostics) -> Self {
        let mut rename_map = ScopeMap::new();
        let mut rename_exp_idents = ScopeMap::new();
        rename_map.push_scope(true);
        rename_exp_idents.push_scope(true);
        State {
            view_as_spec: false,
            check_spec_decreases: None,
            next_var: 0,
            pre_local_decls: Vec::new(),
            mutated_var_idents: HashMap::new(),
            rename_map,
            rename_exp_idents,
            rename_counters: HashMap::new(),
            rename_delayed: HashMap::new(),
            only_generate_pure_exp: 0,
            disable_recommends: 0,
            diagnostics,
            containing_closure: None,
            statics: IndexSet::new(),
            assert_id_counter: 0,
            loop_id_counter: 0,

            mask: None,
        }
    }

    fn next_temp(&mut self, span: &Span, typ: &Typ) -> (VarIdent, Exp) {
        self.next_var += 1;
        let x = crate::def::new_temp_var(self.next_var);
        (x.clone(), SpannedTyped::new(span, typ, ExpX::Var(x.clone())))
    }

    pub(crate) fn push_scope(&mut self) {
        self.rename_map.push_scope(true);
        self.rename_exp_idents.push_scope(true);
    }

    pub(crate) fn pop_scope(&mut self) {
        self.rename_map.pop_scope();
        self.rename_exp_idents.pop_scope();
    }

    pub(crate) fn get_var_unique_id(&self, x: &VarIdent) -> VarIdent {
        match self.rename_map.get(x) {
            None => x.clone(),
            Some(x2) => x2.clone(),
        }
    }

    pub(crate) fn rename_var_general(
        &mut self,
        x: &VarIdent,
        is_stm: bool,
        maybe_exp: bool,
    ) -> VarIdent {
        let does_shadow = self.rename_exp_idents.contains_key(&x.0);
        let id = match self.rename_counters.get(&x.0).copied() {
            None => 0,
            Some(id) => id + 1,
        };
        if maybe_exp {
            let add = if self.rename_exp_idents.contains_key(&x.0) {
                let (scope, _) =
                    self.rename_exp_idents.scope_and_index_of_key(&x.0).expect("scope");
                scope != self.rename_exp_idents.num_scopes() - 1
            } else {
                true
            };
            if add {
                self.rename_exp_idents.insert(x.0.clone(), ()).expect("rename_var");
            }
        }
        let crate::ast::VarIdent(name, d) = x.clone();
        assert!(!matches!(d, VarIdentDisambiguate::VirRenumbered { .. }));
        let d = if is_stm || does_shadow {
            self.rename_counters.insert(x.0.clone(), id);
            // Note that if maybe_exp, we might end up delayed-renaming this later:
            VarIdentDisambiguate::VirRenumbered { is_stmt: is_stm, does_shadow, id }
        } else {
            VarIdentDisambiguate::VirExprNoNumber
        };
        let x2 = crate::ast::VarIdent(name, d);
        if !(is_stm && maybe_exp) {
            self.rename_map.insert(x.clone(), x2.clone()).expect("rename_map");
        }
        x2
    }

    pub(crate) fn rename_var_stm(&mut self, x: &VarIdent) -> VarIdent {
        self.rename_var_general(x, true, false)
    }

    pub(crate) fn rename_var_exp(&mut self, x: &VarIdent) -> VarIdent {
        self.rename_var_general(x, false, true)
    }

    // Note: this does not insert into rename_map; this is done at a later step
    // (see insert_var_maybe_exp) so that it can be inserted into the correct scope
    // (after a push_scope).
    pub(crate) fn rename_var_maybe_exp(&mut self, x: &VarIdent) -> VarIdent {
        self.rename_var_general(x, true, true)
    }

    pub(crate) fn insert_var_maybe_exp(&mut self, x: &VarIdent, x2: &VarIdent) {
        self.rename_map.insert(x.clone(), x2.clone()).expect("rename_map");
    }

    pub(crate) fn rename_delayed_to_exp(&mut self, x: &VarIdent) -> VarIdent {
        let crate::ast::VarIdent(name, d) = x.clone();
        let (does_shadow, id) = match d {
            VarIdentDisambiguate::VirRenumbered { is_stmt: true, does_shadow, id } => {
                (does_shadow, id)
            }
            _ => panic!("rename_delayed called on non-maybe_exp variable"),
        };
        let d = if does_shadow {
            VarIdentDisambiguate::VirRenumbered { is_stmt: false, does_shadow, id }
        } else {
            VarIdentDisambiguate::VirExprNoNumber
        };
        let x2 = crate::ast::VarIdent(name, d);
        self.rename_delayed.insert(x.clone(), x2.clone()).map(|_| panic!("rename_delayed"));
        x2
    }

    pub(crate) fn rename_binders_exp<A: Clone>(
        &mut self,
        binders: &VarBinders<A>,
    ) -> VarBinders<A> {
        let mut bs: Vec<VarBinder<A>> = Vec::new();
        for binder in binders.iter() {
            bs.push(binder.rename(self.rename_var_exp(&binder.name)));
        }
        Arc::new(bs)
    }

    pub(crate) fn rename_delayed_to_exp_binders<A: Clone>(
        &mut self,
        binders: &VarBinders<A>,
    ) -> VarBinders<A> {
        let mut bs: Vec<VarBinder<A>> = Vec::new();
        for binder in binders.iter() {
            bs.push(binder.rename(self.rename_delayed_to_exp(&binder.name)));
        }
        Arc::new(bs)
    }

    pub(crate) fn declare_var_stm(
        &mut self,
        ident: &VarIdent,
        typ: &Typ,
        kind: PreLocalDeclKind,
        may_need_rename: bool,
    ) -> VarIdent {
        let unique_ident = if may_need_rename { self.rename_var_stm(ident) } else { ident.clone() };
        let decl = PreLocalDecl { ident: unique_ident.clone(), typ: typ.clone(), kind };
        self.pre_local_decls.push(decl);
        unique_ident
    }

    pub(crate) fn declare_imm_var_stm(
        &mut self,
        ident: &VarIdent,
        typ: &Typ,
        kind: LocalDeclKind,
        may_need_rename: bool,
    ) -> VarIdent {
        let kind = PreLocalDeclKind::Immutable(Immutable(kind));
        self.declare_var_stm(ident, typ, kind, may_need_rename)
    }

    fn declare_temp_var_stm(
        &mut self,
        span: &Span,
        typ: &Typ,
        kind: PreLocalDeclKind,
    ) -> (VarIdent, Exp) {
        let (temp, temp_var) = self.next_temp(span, typ);
        let temp_id = self.declare_var_stm(&temp, typ, kind, false);
        (temp_id, temp_var)
    }

    fn declare_temp_assign(&mut self, span: &Span, typ: &Typ) -> (VarIdent, Exp) {
        let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::TempViaAssign));
        self.declare_temp_var_stm(span, typ, kind)
    }

    pub(crate) fn declare_params(&mut self, params: &Pars) {
        for param in params.iter() {
            if !matches!(param.x.purpose, ParPurpose::MutPost) {
                let name = &param.x.name;
                self.rename_counters.insert(name.0.clone(), 0).map(|_| panic!("rename_counters"));
                self.rename_map.insert(name.clone(), name.clone()).expect("rename_map");
                self.declare_imm_var_stm(
                    name,
                    &param.x.typ,
                    LocalDeclKind::Param { mutable: false },
                    false,
                );
            }
        }
    }

    // Erase unused unique ids from Vars and process inline functions
    pub(crate) fn finalize_exp(&self, _ctx: &Ctx, exp: &Exp) -> Result<Exp, VirErr> {
        let exp = map_exp_visitor(exp, &mut |exp| match &exp.x {
            ExpX::Var(x) if self.rename_delayed.contains_key(x) => {
                SpannedTyped::new(&exp.span, &exp.typ, ExpX::Var(self.rename_delayed[x].clone()))
            }
            ExpX::Unary(UnaryOp::MustBeFinalized, e1) => e1.clone(),
            _ => exp.clone(),
        });
        Ok(exp)
    }

    // Erase unused unique ids from Vars, perform inlining, choose triggers,
    // and perform splitting if necessary
    pub(crate) fn finalize_stm(&mut self, ctx: &Ctx, stm: &Stm) -> Result<Stm, VirErr> {
        let stm = map_stm_exp_visitor(stm, &|exp| self.finalize_exp(ctx, exp))?;
        map_stm_visitor(&stm, &mut |stm| {
            // TODO doesn't need to be a map
            crate::sst_vars::stm_get_mutations_shallow(stm, &mut self.mutated_var_idents);
            Ok(stm.clone())
        })
        .unwrap();
        Ok(stm)
    }

    pub(crate) fn finalize(mut self) -> Result<FinalState, VirErr> {
        self.pop_scope();
        assert_eq!(self.rename_map.num_scopes(), 0);
        let mut local_decls = vec![];
        for pre_local_decl in self.pre_local_decls.into_iter() {
            let mutbl = self.mutated_var_idents.get(&pre_local_decl.ident);
            local_decls.push(pre_local_decl.into_local_decl(mutbl)?);
        }
        Ok(FinalState { local_decls, statics: self.statics })
    }

    fn checking_spec_preconditions(&self, ctx: &Ctx) -> bool {
        ctx.checking_spec_preconditions() && self.only_generate_pure_exp == 0
    }

    // For either checking_spec_preconditions or checking_spec_decreases,
    // we have to flatten expressions into statements so the statements can be checked
    // for preconditions or termination
    fn checking_spec_general(&self, ctx: &Ctx) -> bool {
        ctx.checking_spec_general() && self.only_generate_pure_exp == 0
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

    pub fn next_assert_id(&mut self) -> Option<air::ast::AssertId> {
        let aid = vec![self.assert_id_counter];
        self.assert_id_counter += 1;
        Some(Arc::new(aid))
    }

    /// Creates a new tmp var and adds a Stm to the stms vec asserting the new
    /// temp var is equal to the given exp. Returns an exp for the temp var.
    pub fn make_tmp_var_for_exp(&mut self, stms: &mut Vec<Stm>, exp: Exp) -> Exp {
        let (temp_id, temp_var) = self.declare_temp_assign(&exp.span, &exp.typ);
        stms.push(init_var(&exp.span, &temp_id, &exp));
        temp_var
    }
}

impl PreLocalDecl {
    fn into_local_decl(self, mutbl: Option<&Span>) -> Result<LocalDecl, VirErr> {
        Ok(Arc::new(LocalDeclX {
            ident: self.ident,
            typ: self.typ,
            kind: self.kind.into_local_decl_kind(mutbl)?,
        }))
    }
}

impl PreLocalDeclKind {
    fn into_local_decl_kind(self, mutbl: Option<&Span>) -> Result<LocalDeclKind, VirErr> {
        match self {
            PreLocalDeclKind::Immutable(Immutable(imm)) => {
                if let Some(span) = mutbl {
                    Err(error(
                        span,
                        format!(
                            "Verus Internal Error: assignment for immutable decl kind {:?}",
                            imm
                        ),
                    ))
                } else {
                    Ok(imm)
                }
            }
            PreLocalDeclKind::Param => Ok(LocalDeclKind::Param { mutable: mutbl.is_some() }),
            PreLocalDeclKind::StmtLet => Ok(LocalDeclKind::StmtLet { mutable: mutbl.is_some() }),
            PreLocalDeclKind::MutParam => Ok(LocalDeclKind::Param { mutable: true }),
        }
    }
}

pub(crate) fn var_loc_exp(span: &Span, typ: &Typ, lhs: UniqueIdent) -> Exp {
    SpannedTyped::new(span, typ, ExpX::VarLoc(lhs))
}

pub(crate) fn init_var(span: &Span, x: &UniqueIdent, exp: &Exp) -> Stm {
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

pub(crate) fn get_function_sst(
    ctx: &Ctx,
    span: &Span,
    name: &Fun,
) -> Result<crate::sst::FunctionSst, VirErr> {
    match ctx.func_sst_map.get(name) {
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
    // TODO: Bool is wrong here
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
/// To be conservative, we need to answer 'yes' (true) if we can't tell.
///
/// Note: we originally used this to handle the case where the loop body returns
/// the never type (!). However, that isn't actually important anymore since loops will
/// be wrapped in the NeverToAny node. It's likely that this check can simply be removed.
pub fn can_control_flow_reach_after_loop(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Loop { label, cond: None, body, .. } => loop_body_has_break(label, body),
        ExprX::Loop { cond: Some(_), .. } => true,
        _ => {
            panic!("expected while loop");
        }
    }
}

/// The `Sequencer` struct should be used for most nodes that have multiple Exprs as input
/// in order to make sure the resulting Stms and Exps have the right ordering.
///
/// Given a bunch of Exprs, e.g., Expr[0], Expr[1], ..., then upon immediate lowering,
/// each Expr becomes a (Vec<Stm>, Exp), which together make sense when evaluated in the
/// following order:
///
///    stms[0], exps[0], stms[1], exps[1], ...
///
/// However, what we _need_ is to put all the Stms together at the beginning and the Exps at
/// the end, so we can input the Exps to the computation of interest (e.g., function call,
/// binary op, etc.). However, later Stms might change the meaning of earlier Exps (which
/// can happen if the Stms contain assignments to variables which are read by the Exps).
///
/// The purpose of the `Sequencer` object is to safely commute all the Exps to the end.
struct Sequencer {
    stms: Vec<Vec<Stm>>,
    exps: Vec<(Exp, Immutable)>,
}

impl Sequencer {
    fn new() -> Self {
        Sequencer { stms: vec![], exps: vec![] }
    }

    /// Append the given Stms and Maybe<Value>.
    /// In the event that the Maybe<Value> is a Never, this will return all the Stms pushed
    /// up this point (including the Stms from the present call).
    ///
    /// The `kind` argument is the LocalDeclKind that should be used in the event that a
    /// temporary is created.
    #[must_use]
    fn push(&mut self, stms: Vec<Stm>, rv: Maybe<Value>, kind: Immutable) -> Option<Vec<Stm>> {
        self.stms.push(stms);
        match rv.to_maybe_exp() {
            Maybe::Some(e) => {
                self.exps.push((e, kind));
                None
            }
            Maybe::Never => {
                let all_stms = std::mem::take(&mut self.stms).into_iter().flatten().collect();
                Some(all_stms)
            }
        }
    }

    /// Upon completion, turn all the inputted data into (Stms, Exps) that can be evaluated
    /// in that order.
    fn into_stms_exps(self, state: &mut State) -> (Vec<Stm>, Vec<Exp>) {
        assert!(self.stms.len() == self.exps.len() || self.stms.len() == self.exps.len() + 1);

        let mut largest_idx_with_stm = None;
        for i in (0..self.stms.len()).rev() {
            if self.stms[i].len() > 0 {
                largest_idx_with_stm = Some(i);
                break;
            }
        }

        let mut final_stms = self.stms;
        let mut final_exps = vec![];

        for i in 0..self.exps.len() {
            let (arg, kind) = &self.exps[i];

            // Create a temporary for any exp that comes before a stm
            if largest_idx_with_stm.is_some()
                && i < largest_idx_with_stm.unwrap()
                && !matches!(&arg.x, ExpX::Loc(_))
            {
                let (temp_id, temp_var) = state.declare_temp_var_stm(
                    &arg.span,
                    &arg.typ,
                    PreLocalDeclKind::Immutable(*kind),
                );
                final_exps.push(temp_var);
                final_stms[i].push(init_var(&arg.span, &temp_id, arg));
            } else {
                final_exps.push(arg.clone());
            }
        }

        let final_stms = final_stms.into_iter().flatten().collect::<Vec<_>>();
        (final_stms, final_exps)
    }

    /// Helper for the special case of binary ops
    fn into_stms_exps_expect_2(self, state: &mut State) -> (Vec<Stm>, Exp, Exp) {
        let (stms, exps) = self.into_stms_exps(state);
        assert!(exps.len() == 2);
        (stms, exps[0].clone(), exps[1].clone())
    }

    /// Use this when there are extra Stms at the end that don't go with any of the
    /// expressions
    /// i.e. if we have
    ///    stms[0], exps[0], stms[1], exps[1], ... stms[n], exps[n], stms[n+1]
    /// Then pass stms[n+1] as the argument to this function
    fn into_stms_exps_with_extra(self, state: &mut State, stms: Vec<Stm>) -> (Vec<Stm>, Vec<Exp>) {
        let mut s = self;
        s.stms.push(stms);
        s.into_stms_exps(state)
    }
}

struct ReturnedCall {
    fun: Fun,
    resolved_method: Option<(Fun, Typs)>,
    is_trait_default: Option<bool>,
    typs: Typs,
    has_return: bool,
    args: Exps,
}

fn expr_get_call(
    ctx: &Ctx,
    state: &mut State,
    disallow_poly_ret: Option<&Typ>,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, Maybe<ReturnedCall>)>, VirErr> {
    match &expr.x {
        ExprX::Call(target, args, post_args) => match target {
            CallTarget::FnSpec(..) => {
                panic!("internal error: CallTarget::FnSpec");
            }
            CallTarget::Fun(kind, x, typs, _impl_paths, autospec_usage) => {
                if *autospec_usage != AutospecUsage::Final {
                    return Err(internal_error(&expr.span, "autospec not discharged"));
                }
                let function = get_function(ctx, &expr.span, x)?;
                let has_ret = function.x.ens_has_return;
                if disallow_poly_ret.is_some()
                    && has_ret
                    && crate::poly::ret_needs_native(
                        ctx,
                        &function.x.kind,
                        &function.x.ret.x.typ,
                        disallow_poly_ret.unwrap(),
                    )
                {
                    // Anticipate that poly.rs will need to coerce the result from poly to native,
                    // so we return None to force the creation of a temp variable for the coercion.
                    // TODO: in the long run, this would make more sense to handle entirely
                    // in poly.rs, but for now, we continue to handle this here to avoid
                    // disrupting the old behavior.
                    return Ok(None);
                }

                let mut sequr = Sequencer::new();

                // Suppose have as arguments:
                //   TwoPhaseMutBorrow(p1)
                //   TwoPhaseMutBorrow(p2)
                //
                // Then the "second phase" of these arguments goes after the argument evaluation.
                // So the result would look like:
                //
                //  eval p1
                //  eval p2
                //  Phase2 mutation for p1
                //  Phase2 mutation for p2
                //  post_args
                //  execute the "call"
                //
                // Note that the "post_args" may contain AssumeResolved statements inserted
                // by the resolution inference; these are supposed to go after the phase2
                // mutations.

                // delayed "phase2" Stms
                let mut second_phase: Vec<Stm> = Vec::new();

                for arg in args.iter() {
                    let poly =
                        crate::poly::arg_is_poly(ctx, &function.x.kind, function.x.mode, &arg.typ);
                    let kind = Immutable(LocalDeclKind::StmCallArg { native: !poly });

                    match &arg.x {
                        ExprX::TwoPhaseBorrowMut(_) => {
                            let (phase1_stms, bor_sst) = borrow_mut_to_sst(ctx, state, arg)?;
                            let mut_ref_exp = match &bor_sst {
                                Maybe::Never => Maybe::Never,
                                Maybe::Some(bor_sst) => {
                                    Maybe::Some(Value::Exp(bor_sst.mut_ref_exp.clone()))
                                }
                            };

                            let early_return = sequr.push(phase1_stms, mut_ref_exp, kind);
                            if let Some(stms) = early_return {
                                return Ok(Some((stms, Maybe::Never)));
                            }

                            let Maybe::Some(bor_sst) = bor_sst else { unreachable!() };
                            second_phase.push(bor_sst.phase2_stm);
                        }
                        _ => {
                            let (stms0, e0) = expr_to_stm_opt(ctx, state, &arg)?;
                            let early_return = sequr.push(stms0, e0, kind);
                            if let Some(stms) = early_return {
                                return Ok(Some((stms, Maybe::Never)));
                            }
                        }
                    };
                }

                if let Some(post_args) = post_args {
                    let (mut stms0, e0) = expr_to_stm_opt(ctx, state, post_args)?;
                    assert!(matches!(e0, Maybe::Some(Value::ImplicitUnit(_))));
                    second_phase.append(&mut stms0);
                }

                let (stms, exps) = sequr.into_stms_exps_with_extra(state, second_phase);

                use crate::ast::{CallTargetKind, FunctionKind};
                let is_trait_default =
                    if let FunctionKind::TraitMethodDecl { has_default: true, .. } =
                        &function.x.kind
                    {
                        match kind {
                            CallTargetKind::Static => None,
                            CallTargetKind::ProofFn(..) => None,
                            CallTargetKind::Dynamic => Some(false),
                            CallTargetKind::DynamicResolved { is_trait_default, .. } => {
                                Some(*is_trait_default)
                            }
                            CallTargetKind::ExternalTraitDefault => Some(true),
                        }
                    } else {
                        None
                    };
                Ok(Some((
                    stms,
                    Maybe::Some(ReturnedCall {
                        fun: x.clone(),
                        resolved_method: kind.resolved(),
                        is_trait_default,
                        typs: typs.clone(),
                        has_return: has_ret,
                        args: Arc::new(exps),
                    }),
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
    disallow_poly_ret: Option<&Typ>,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, Maybe<ReturnedCall>)>, VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::Fun(kind, x, _, _, _), _, _)
            if !function_can_be_exp(ctx, state, expr, x, &kind.resolved())? =>
        {
            expr_get_call(ctx, state, disallow_poly_ret, expr)
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
    if state.checking_spec_general(ctx) {
        let (stms, _exp) = expr_to_stm_or_error(ctx, state, expr)?;
        Ok(stms)
    } else {
        Ok(vec![])
    }
}

// Check spec preconditions in expr, but don't generate an Exp for Expr
// Declare variables from binders as locals for checking
fn check_pure_expr_bind(
    ctx: &Ctx,
    state: &mut State,
    binders: &VarBinders<Typ>,
    kind: PreLocalDeclKind,
    expr: &Expr,
) -> Result<Vec<Stm>, VirErr> {
    if state.checking_spec_general(ctx) {
        state.push_scope();
        let mut stms: Vec<Stm> = Vec::new();
        for binder in binders.iter() {
            let x = state.declare_var_stm(&binder.name, &binder.a, kind, true);
            stms.push(assume_has_typ(&x, &binder.a, &expr.span));
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
    if state.checking_spec_general(ctx) {
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

pub(crate) fn expr_to_pure_exp_check_with_typ_substs(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
    typ_substs: &HashMap<Ident, Typ>,
) -> Result<(Vec<Stm>, Exp), VirErr> {
    let local_decls_init_len = state.pre_local_decls.len();

    let (stms, exp) = expr_to_pure_exp_check(ctx, state, expr)?;

    let exp = subst_exp(typ_substs, &HashMap::new(), &exp);
    let stms: Vec<_> =
        stms.iter().map(|stm| subst_stm(typ_substs, &HashMap::new(), &stm)).collect();

    let local_decls_new_len = state.pre_local_decls.len();
    for i in local_decls_init_len..local_decls_new_len {
        state.pre_local_decls[i] = subst_pre_local_decl(typ_substs, &state.pre_local_decls[i]);
    }

    Ok((stms, exp))
}

pub(crate) fn expr_to_decls_exp_skip_checks(
    ctx: &Ctx,
    diagnostics: &dyn Diagnostics,
    view_as_spec: bool,
    params: &Pars,
    expr: &Expr,
) -> Result<(Vec<LocalDecl>, Exp), VirErr> {
    let mut state = State::new(diagnostics);
    state.view_as_spec = view_as_spec;
    state.declare_params(params);
    let exp = expr_to_pure_exp_skip_checks(ctx, &mut state, expr)?;
    let exp = state.finalize_exp(ctx, &exp)?;
    let FinalState { local_decls, statics: _ } = state.finalize()?;
    Ok((local_decls, exp))
}

pub(crate) fn expr_to_bind_decls_exp_skip_checks(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    params: &Pars,
    expr: &Expr,
) -> Result<Exp, VirErr> {
    let mut state = State::new(diagnostics);
    state.declare_params(params);
    let exp = expr_to_pure_exp_skip_checks(ctx, &mut state, expr)?;
    let exp = state.finalize_exp(ctx, &exp)?;
    state.finalize()?;
    Ok(exp)
}

pub(crate) fn expr_to_exp_skip_checks(
    ctx: &Ctx,
    diagnostics: &dyn Diagnostics,
    params: &Pars,
    expr: &Expr,
) -> Result<Exp, VirErr> {
    Ok(expr_to_decls_exp_skip_checks(ctx, diagnostics, false, params, expr)?.1)
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
    match exp_opt.to_maybe_exp() {
        Maybe::Some(e) => Ok((stms, e)),
        Maybe::Never => Err(error(&expr.span, "expression must produce a value")),
    }
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
    func_span: &Span,
) -> Result<Stm, VirErr> {
    let (mut stms, exp) = expr_to_stm_opt(ctx, state, expr)?;

    // secondary label (indicating which post-condition failed) is added later
    // in ast_to_sst when the post condition is expanded
    let base_error = error_with_secondary_label(
        find_last_span_in_expr(&expr, func_span),
        crate::def::POSTCONDITION_FAILURE.to_string(),
        "at the end of the function body".to_string(),
    );

    match exp.to_maybe_exp() {
        Maybe::Some(exp) => {
            // Emit the postcondition for the common case where the function body
            // terminates with an expression to be returned (or an implicit
            // return value of 'unit').

            stms.push(Spanned::new(
                expr.span.clone(),
                StmX::Return {
                    base_error,
                    ret_exp: Some(exp),
                    inside_body: false,
                    assert_id: state.next_assert_id(),
                },
            ));
        }
        Maybe::Never => {
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

fn find_last_span_in_expr<'x>(expr: &'x Expr, fn_span: &'x Span) -> &'x Span {
    match &expr.x {
        ExprX::Block(_vec, block_expr) => block_expr.as_ref().map(|x| &x.span).unwrap_or(&fn_span),
        _ => &expr.span,
    }
}

fn is_small_exp(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Const(_) => true,
        ExpX::Var(..) | ExpX::VarAt(..) => true,
        ExpX::Old(..) => true,
        ExpX::Unary(UnaryOp::Not | UnaryOp::Clip { .. } | UnaryOp::MustBeFinalized, e) => {
            is_small_exp_or_loc(e)
        }
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), _) => panic!("unexpected box"),
        _ => false,
    }
}

fn is_small_exp_or_loc(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Loc(..) => true,
        _ => is_small_exp(exp),
    }
}

fn mask_set_for_call(fun: &Function, typs: &Typs, args: Arc<Vec<Exp>>) -> MaskSet {
    let mask_spec = fun.x.mask_spec_or_default(&fun.span);
    match &mask_spec {
        MaskSpec::InvariantOpens(span, es) | MaskSpec::InvariantOpensExcept(span, es) => {
            let mut inv_exps = vec![];
            for (i, e) in es.iter().enumerate() {
                let expx = ExpX::Call(
                    CallFun::InternalFun(InternalFun::OpenInvariantMask(fun.x.name.clone(), i)),
                    typs.clone(),
                    args.clone(),
                );
                let exp = SpannedTyped::new(&e.span, &e.typ, expx);
                inv_exps.push(exp);
            }
            match &mask_spec {
                MaskSpec::InvariantOpens(..) => MaskSet::from_list(&inv_exps, span),
                MaskSpec::InvariantOpensExcept(..) => {
                    MaskSet::from_list_complement(&inv_exps, span)
                }
                MaskSpec::InvariantOpensSet(..) => panic!(),
            }
        }
        MaskSpec::InvariantOpensSet(e) => {
            let expx = ExpX::Call(
                CallFun::InternalFun(InternalFun::OpenInvariantMask(fun.x.name.clone(), 0)),
                typs.clone(),
                args.clone(),
            );
            let exp = SpannedTyped::new(&e.span, &e.typ, expx);
            MaskSet::arbitrary(&exp)
        }
    }
}

fn stm_call(
    ctx: &Ctx,
    state: &mut State,
    span: &Span,
    name: Fun,
    resolved_method: Option<(Fun, Typs)>,
    is_trait_default: Option<bool>,
    typs: Typs,
    args: Exps,
    dest: Option<Dest>,
) -> Result<Stm, VirErr> {
    let fun = get_function(ctx, span, &name)?;
    let mut stms: Vec<Stm> = Vec::new();

    let mut small_args: Vec<Exp> = Vec::new();
    for arg in args.iter() {
        if is_small_exp_or_loc(arg) {
            small_args.push(arg.clone());
        } else {
            // To avoid copying arg in preconditions and postconditions,
            // put arg into a temporary variable
            let poly = crate::poly::arg_is_poly(ctx, &fun.x.kind, fun.x.mode, &arg.typ);
            let kind =
                PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::StmCallArg { native: !poly }));
            let (temp_id, temp_var) = state.declare_temp_var_stm(&arg.span, &arg.typ, kind);
            small_args.push(temp_var);
            stms.push(init_var(&arg.span, &temp_id, arg));
        }
    }

    let small_args = Arc::new(small_args);
    if !state.checking_recommends(ctx) {
        match &state.mask {
            Some(caller_mask) => {
                let callee_mask = mask_set_for_call(&fun, &typs, small_args.clone());
                for assertion in callee_mask.subset_of(ctx, caller_mask, span) {
                    stms.push(Spanned::new(
                        span.clone(),
                        StmX::Assert(state.next_assert_id(), Some(assertion.err), assertion.cond),
                    ))
                }
            }
            None => (),
        }
    }

    let call = StmX::Call {
        fun: name,
        resolved_method,
        mode: fun.x.mode,
        is_trait_default,
        typ_args: typs,
        args: small_args,
        split: None,
        dest,
        assert_id: state.next_assert_id(),
    };

    stms.push(Spanned::new(span.clone(), call));
    Ok(stms_to_one_stm(span, stms))
}

fn if_to_stm(
    state: &mut State,
    expr: &Expr,
    mut stms0: Vec<Stm>,
    e0: &Maybe<Value>,
    mut stms1: Vec<Stm>,
    e1: &Maybe<Value>,
    mut stms2: Vec<Stm>,
    e2: &Maybe<Value>,
) -> (Vec<Stm>, Maybe<Value>) {
    let e0 = match e0.clone().to_maybe_exp() {
        Maybe::Some(e) => e,
        Maybe::Never => {
            return (stms0, Maybe::Never);
        }
    };

    match (e1, e2) {
        (Maybe::Some(Value::ImplicitUnit(_)), _) | (_, Maybe::Some(Value::ImplicitUnit(_))) => {
            // If one branch returned an implicit unit, then the other branch
            // must also return a unit (either implicit or explicit).
            // If this sanity check fails, then it's likely we screwed up and
            // the alleged implicit unit branch was actually a never-return.
            assert!(types_equal(&expr.typ, &unit_typ()));

            let stm1 = stms_to_one_stm(&expr.span, stms1);
            let stm2 = stms_to_one_stm_opt(&expr.span, stms2);
            let if_stmt = StmX::If(e0, stm1, stm2);
            stms0.push(Spanned::new(expr.span.clone(), if_stmt));
            (stms0, Maybe::Some(Value::ImplicitUnit(expr.span.clone())))
        }
        (Maybe::Never, other) | (other, Maybe::Never) => {
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
        (Maybe::Some(Value::Exp(e1)), Maybe::Some(Value::Exp(e2))) => {
            if stms1.len() == 0 && stms2.len() == 0 {
                // In this case, we can construct a pure expression.
                let expx = ExpX::If(e0.clone(), e1.clone(), e2.clone());
                let exp = SpannedTyped::new(&expr.span, &expr.typ, expx);
                (stms0, Maybe::Some(Value::Exp(exp)))
            } else {
                // We have `if ( stms0; e0 ) { stms1; e1 } else { stms2; e2 }`.
                // We turn this into:
                //  stms0;
                //  if e0 { stms1; temp = e1; } else { stms2; temp = e2; };
                //  temp

                let (temp_id, temp_var) = state.declare_temp_assign(&expr.span, &expr.typ);
                stms1.push(init_var(&expr.span, &temp_id, &e1));
                stms2.push(init_var(&expr.span, &temp_id, &e2));
                let stm1 = stms_to_one_stm(&expr.span, stms1);
                let stm2 = stms_to_one_stm_opt(&expr.span, stms2);
                let if_stmt = StmX::If(e0, stm1, stm2);
                stms0.push(Spanned::new(expr.span.clone(), if_stmt));
                // temp
                (stms0, Maybe::Some(Value::Exp(temp_var)))
            }
        }
    }
}

/// Convert a VIR Expr to a SST (Vec<Stm>, Maybe<Value>), i.e., instructions of the form,
/// "run these statements, then return this side-effect-free expression".
///
/// Note the 'Maybe<Value>' can be one of three things:
///  * Maybe::Some(Value::Exp(e)) - means the expression e was returned
///  * Maybe::Some(ImplicitUnit(_)) - for the implicit unit case
///  * Maybe::Never - the expression can never return (e.g., after a return value or break)
pub(crate) fn expr_to_stm_opt(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Maybe<Value>), VirErr> {
    let mk_exp = |expx: ExpX| SpannedTyped::new(&expr.span, &expr.typ, expx);
    match &expr.x {
        ExprX::Const(c) => Ok((vec![], Maybe::Some(Value::Exp(mk_exp(ExpX::Const(c.clone())))))),
        ExprX::Var(x) => {
            let unique_id = state.get_var_unique_id(&x);
            let e = mk_exp(ExpX::Var(unique_id));
            let e = mk_exp(ExpX::Unary(UnaryOp::MustBeFinalized, e));
            Ok((vec![], Maybe::Some(Value::Exp(e))))
        }
        ExprX::StaticVar(x) => {
            state.statics.insert(x.clone());
            let e = mk_exp(ExpX::StaticVar(x.clone()));
            Ok((vec![], Maybe::Some(Value::Exp(e))))
        }
        ExprX::VarLoc(x) => {
            let unique_id = state.get_var_unique_id(&x);
            Ok((vec![], Maybe::Some(Value::Exp(mk_exp(ExpX::VarLoc(unique_id))))))
        }
        ExprX::VarAt(x, VarAt::Pre) => {
            if let Some((scope, _)) = state.rename_map.scope_and_index_of_key(x) {
                if scope != 0 {
                    Err(error(&expr.span, "the parameter is shadowed here"))?;
                }
            }
            Ok((
                vec![],
                Maybe::Some(Value::Exp(mk_exp(ExpX::VarAt(
                    state.get_var_unique_id(&x),
                    VarAt::Pre,
                )))),
            ))
        }
        ExprX::ConstVar(..) => panic!("ConstVar should already be removed"),
        ExprX::Loc(expr1) => {
            let (stms, e0) = expr_to_stm_opt(ctx, state, expr1)?;
            let e0 = to_exp_or_return_never!(e0, stms);
            Ok((stms, Maybe::Some(Value::Exp(mk_exp(ExpX::Loc(e0))))))
        }
        ExprX::AssignToPlace { place, rhs, op: Some(binary_op), resolve } => {
            assert!(resolve.is_none());

            // No support for short-circuit ops here
            assert!(!matches!(binary_op, BinaryOp::And | BinaryOp::Or | BinaryOp::Implies));

            let (stms_r, e_r) = expr_to_stm_opt(ctx, state, rhs)?;
            let e_r = to_exp_or_return_never!(e_r, stms_r);

            let (stms_l, exps) = place_to_exp_pair(ctx, state, place)?;
            let (lhs_exp, e_l) = unwrap_or_return_never!(exps, stms_r, stms_l);

            let mut sequr = Sequencer::new();
            push_or_return_never!(sequr.push(
                stms_r,
                Maybe::Some(Value::Exp(e_r)),
                Immutable(LocalDeclKind::TempViaAssign)
            ));
            push_or_return_never!(sequr.push(
                stms_l,
                Maybe::Some(Value::Exp(e_l)),
                Immutable(LocalDeclKind::TempViaAssign)
            ));

            let (mut stms, e_r, e_l) = sequr.into_stms_exps_expect_2(state);
            let (mut stms3, bin) =
                binary_op_exp(ctx, state, &expr.span, &place.typ, *binary_op, &e_l, &e_r);
            stms.append(&mut stms3);

            let assign = StmX::Assign { lhs: Dest { dest: lhs_exp, is_init: false }, rhs: bin };
            stms.push(Spanned::new(expr.span.clone(), assign));

            Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::AssignToPlace { place, rhs, op: None, resolve } => {
            let (stms_r, e_r) = expr_to_stm_opt(ctx, state, rhs)?;
            let e_r = to_exp_or_return_never!(e_r, stms_r);

            let (stms_l, exps) = place_to_exp_pair(ctx, state, place)?;
            let (lhs_exp, e_l) = unwrap_or_return_never!(exps, stms_r, stms_l);

            let mut sequr = Sequencer::new();
            push_or_return_never!(sequr.push(
                stms_r,
                Maybe::Some(Value::Exp(e_r)),
                Immutable(LocalDeclKind::TempViaAssign)
            ));
            push_or_return_never!(sequr.push(
                stms_l,
                Maybe::Some(Value::Exp(e_l)),
                Immutable(LocalDeclKind::TempViaAssign)
            ));

            let (mut stms, e_r, e_l) = sequr.into_stms_exps_expect_2(state);

            if let Some(t) = resolve {
                let resx = ExpX::UnaryOpr(UnaryOpr::HasResolved(t.clone()), e_l.clone());
                let res = SpannedTyped::new(&expr.span, &bool_typ(), resx);
                let assume_stm = Spanned::new(expr.span.clone(), StmX::Assume(res));
                stms.push(assume_stm);
            }

            let assign = StmX::Assign { lhs: Dest { dest: lhs_exp, is_init: false }, rhs: e_r };
            stms.push(Spanned::new(expr.span.clone(), assign));

            Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::Assign { lhs: lhs_expr, rhs: expr2, op } => {
            if op.is_some() {
                panic!("op should already be removed")
            }
            let (mut stms, lhs_exp) = expr_to_stm_opt(ctx, state, lhs_expr)?;
            let lhs_exp = lhs_exp.expect_exp();
            let direct_assign =
                if matches!(lhs_exp.x, ExpX::VarLoc(_)) { Some(&lhs_exp.typ) } else { None };
            match expr_must_be_call_stm(ctx, state, direct_assign, expr2)? {
                Some((stms2, Maybe::Never)) => {
                    stms.extend(stms2.into_iter());
                    Ok((stms, Maybe::Never))
                }
                Some((
                    stms2,
                    Maybe::Some(ReturnedCall {
                        fun,
                        resolved_method,
                        is_trait_default,
                        typs,
                        has_return: _,
                        args,
                    }),
                )) => {
                    // make a Call
                    stms.extend(stms2.into_iter());
                    let (dest, assign) = if direct_assign.is_some() {
                        (Dest { dest: lhs_exp, is_init: false }, None)
                    } else {
                        let (temp_ident, temp_var) =
                            state.declare_temp_assign(&lhs_exp.span, &expr2.typ);
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
                        is_trait_default,
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
                    Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
                }
                None => {
                    // make an Assign
                    let (stms2, e2) = expr_to_stm_opt(ctx, state, expr2)?;
                    let e2 = to_exp_or_return_never!(e2, stms2);
                    stms.extend(stms2.into_iter());
                    let rhs = if matches!(lhs_exp.x, ExpX::VarLoc(_)) || is_small_exp(&e2) {
                        e2
                    } else {
                        let (temp_ident, temp_var) = state.declare_temp_assign(&e2.span, &e2.typ);
                        stms.push(init_var(&expr.span, &temp_ident, &e2));
                        temp_var
                    };
                    let assign = StmX::Assign { lhs: Dest { dest: lhs_exp, is_init: false }, rhs };
                    stms.push(Spanned::new(expr.span.clone(), assign));
                    Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
                }
            }
        }
        ExprX::Call(CallTarget::FnSpec(e0), args, post_args) => {
            assert!(post_args.is_none());
            let (mut check_stms, e0) = expr_to_pure_exp_check(ctx, state, e0)?;
            let mut arg_exps: Vec<Exp> = Vec::new();
            for arg in args.iter() {
                let (stms, e) = expr_to_pure_exp_check(ctx, state, arg)?;
                check_stms.extend(stms);
                arg_exps.push(e);
            }
            let call = ExpX::CallLambda(e0, Arc::new(arg_exps));
            Ok((check_stms, Maybe::Some(Value::Exp(mk_exp(call)))))
        }
        ExprX::Call(CallTarget::BuiltinSpecFun(bsf, ts, _impl_paths), args, post_args) => {
            assert!(post_args.is_none());
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
                BuiltinSpecFun::DefaultEns => InternalFun::DefaultEns,
            };
            Ok((
                check_stms,
                Maybe::Some(Value::Exp(mk_exp(ExpX::Call(
                    CallFun::InternalFun(f),
                    ts.clone(),
                    Arc::new(arg_exps),
                )))),
            ))
        }
        ExprX::Call(CallTarget::Fun(..), _, _) => {
            match expr_get_call(ctx, state, None, expr)?.expect("Call") {
                (stms, Maybe::Never) => Ok((stms, Maybe::Never)),
                (
                    mut stms,
                    Maybe::Some(ReturnedCall {
                        fun: x,
                        resolved_method,
                        is_trait_default,
                        typs,
                        has_return: ret,
                        args,
                    }),
                ) => {
                    if function_can_be_exp(ctx, state, expr, &x, &resolved_method)? {
                        // ExpX::Call
                        let call = ExpX::Call(
                            CallFun::Fun(x.clone(), resolved_method.clone()),
                            typs.clone(),
                            args,
                        );
                        Ok((stms, Maybe::Some(Value::Exp(mk_exp(call)))))
                    } else if ret {
                        let (temp_ident, temp_var) =
                            state.declare_temp_assign(&expr.span, &expr.typ);
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
                            is_trait_default,
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
                        Ok((stms, Maybe::Some(Value::Exp(temp_var))))
                    } else {
                        // StmX::Call
                        stms.push(stm_call(
                            ctx,
                            state,
                            &expr.span,
                            x.clone(),
                            resolved_method,
                            is_trait_default,
                            typs.clone(),
                            args,
                            None,
                        )?);
                        Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
                    }
                }
            }
        }
        ExprX::Ctor(p, i, binders, update) => {
            assert!(update.is_none()); // should be simplified by ast_simplify

            // Handle two-phase borrow; see the explanation in expr_get_call
            let mut second_phase: Vec<Stm> = Vec::new();

            let mut sequr = Sequencer::new();
            for binder in binders.iter() {
                let arg = &binder.a;
                let kind = Immutable(LocalDeclKind::TempViaAssign);
                match &arg.x {
                    ExprX::TwoPhaseBorrowMut(_) => {
                        let (phase1_stms, bor_sst) = borrow_mut_to_sst(ctx, state, arg)?;
                        let mut_ref_exp = match &bor_sst {
                            Maybe::Never => Maybe::Never,
                            Maybe::Some(bor_sst) => {
                                Maybe::Some(Value::Exp(bor_sst.mut_ref_exp.clone()))
                            }
                        };
                        push_or_return_never!(sequr.push(phase1_stms, mut_ref_exp, kind));
                        let Maybe::Some(bor_sst) = bor_sst else { unreachable!() };
                        second_phase.push(bor_sst.phase2_stm);
                    }
                    _ => {
                        let (stms0, e0) = expr_to_stm_opt(ctx, state, &binder.a)?;
                        push_or_return_never!(sequr.push(stms0, e0, kind));
                    }
                }
            }
            let (stms, exps) = sequr.into_stms_exps_with_extra(state, second_phase);

            let mut args: Vec<Binder<Exp>> = Vec::new();
            for (binder, e1) in binders.iter().zip(exps.into_iter()) {
                let arg = BinderX { name: binder.name.clone(), a: e1 };
                args.push(Arc::new(arg));
            }
            let ctor = ExpX::Ctor(p.clone(), i.clone(), Arc::new(args));
            Ok((stms, Maybe::Some(Value::Exp(mk_exp(ctor)))))
        }
        ExprX::NullaryOpr(op) => {
            Ok((vec![], Maybe::Some(Value::Exp(mk_exp(ExpX::NullaryOpr(op.clone()))))))
        }
        ExprX::Unary(op @ UnaryOp::InferSpecForLoopIter { .. }, spec_expr) => {
            let spec_exp = expr_to_pure_exp_skip_checks(ctx, state, &spec_expr)?;
            let infer_exp = mk_exp(ExpX::Unary(*op, spec_exp));
            Ok((vec![], Maybe::Some(Value::Exp(infer_exp))))
        }
        ExprX::Unary(op, exprr) => {
            let (mut stms, exp) = expr_to_stm_opt(ctx, state, exprr)?;
            let exp = to_exp_or_return_never!(exp, stms);
            if let (true, UnaryOp::Clip { truncate: false, .. }) =
                (state.checking_recommends(ctx), op)
            {
                let unary = UnaryOpr::HasType(expr.typ.clone());
                let has_type = ExpX::UnaryOpr(unary, exp.clone());
                let has_type = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), has_type);
                let error = crate::messages::error(
                    &expr.span,
                    "recommendation not met: value may be out of range of the target type (use `#[verifier::truncate]` on the cast to silence this warning)",
                );
                let assert = StmX::Assert(state.next_assert_id(), Some(error), has_type);
                let assert = Spanned::new(expr.span.clone(), assert);
                stms.push(assert);
            }
            Ok((stms, Maybe::Some(Value::Exp(mk_exp(ExpX::Unary(*op, exp))))))
        }
        ExprX::UnaryOpr(op, arg) => {
            let (mut stms, exp) = expr_to_stm_opt(ctx, state, arg)?;
            let exp = to_exp_or_return_never!(exp, stms);
            let (check, op) = match op {
                UnaryOpr::Field(field_opr) => match field_opr.check {
                    VariantCheck::Union => {
                        let (condition, msg) = crate::place_preconditions::sst_field_check(
                            &expr.span, &exp, field_opr,
                        );
                        let field_opr = FieldOpr { check: VariantCheck::None, ..field_opr.clone() };
                        (Some((condition, msg)), UnaryOpr::Field(field_opr))
                    }
                    VariantCheck::None => (None, op.clone()),
                },
                _ => (None, op.clone()),
            };
            if let Some((condition, msg)) = check {
                if !state.checking_recommends(ctx) {
                    let assert = StmX::Assert(state.next_assert_id(), Some(msg), condition.clone());
                    let assert = Spanned::new(expr.span.clone(), assert);
                    stms.push(assert);
                }
                let assume = StmX::Assume(condition);
                let assume = Spanned::new(expr.span.clone(), assume);
                stms.push(assume);
            }
            Ok((stms, Maybe::Some(Value::Exp(mk_exp(ExpX::UnaryOpr(op, exp))))))
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
            let (stms1, e1) = expr_to_stm_opt(ctx, state, e1)?;
            let (stms2, e2) = expr_to_stm_opt(ctx, state, e2)?;
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
                    let b = Maybe::Some(Value::Exp(b));
                    if proceed_on {
                        Ok(if_to_stm(state, expr, stms1, &e1, stms2, &e2, vec![], &b))
                    } else {
                        Ok(if_to_stm(state, expr, stms1, &e1, vec![], &b, stms2, &e2))
                    }
                }
                _ => {
                    let mut sequr = Sequencer::new();
                    push_or_return_never!(sequr.push(
                        stms1,
                        e1,
                        Immutable(LocalDeclKind::TempViaAssign)
                    ));
                    push_or_return_never!(sequr.push(
                        stms2,
                        e2,
                        Immutable(LocalDeclKind::TempViaAssign)
                    ));
                    let (mut stms, e1, e2) = sequr.into_stms_exps_expect_2(state);

                    let (mut stms3, bin) =
                        binary_op_exp(ctx, state, &expr.span, &expr.typ, *op, &e1, &e2);
                    stms.append(&mut stms3);

                    Ok((stms, Maybe::Some(Value::Exp(bin))))
                }
            }
        }
        ExprX::BinaryOpr(op, e1, e2) => {
            let (stms1, e1) = expr_to_stm_opt(ctx, state, e1)?;
            let (stms2, e2) = expr_to_stm_opt(ctx, state, e2)?;

            let mut sequr = Sequencer::new();
            push_or_return_never!(sequr.push(stms1, e1, Immutable(LocalDeclKind::TempViaAssign)));
            push_or_return_never!(sequr.push(stms2, e2, Immutable(LocalDeclKind::TempViaAssign)));
            let (stms, e1, e2) = sequr.into_stms_exps_expect_2(state);

            let bin = mk_exp(ExpX::BinaryOpr(op.clone(), e1, e2));
            Ok((stms, Maybe::Some(Value::Exp(bin))))
        }
        ExprX::Multi(..) => {
            panic!("internal error: Multi should have been simplified by ast_simplify")
        }
        ExprX::Quant(quant, binders, body) => {
            let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::QuantBinder));
            let check_stms = check_pure_expr_bind(ctx, state, binders, kind, body)?;
            state.push_scope();
            let binders = state.rename_binders_exp(binders);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions with check_pure_expr_bind
            let exp = expr_to_pure_exp_skip_checks(ctx, state, body)?;
            state.pop_scope();
            let trigs = Arc::new(vec![]); // real triggers will be set by finalize_exp
            let bnd =
                Spanned::new(body.span.clone(), BndX::Quant(*quant, binders.clone(), trigs, None));
            let e = mk_exp(ExpX::Bind(bnd, exp));
            let e = mk_exp(ExpX::Unary(UnaryOp::MustBeElaborated, e));
            Ok((check_stms, Maybe::Some(Value::Exp(e))))
        }
        ExprX::Closure(params, body) => {
            state.disable_recommends += 1;
            let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::ClosureBinder));
            let check_stms = check_pure_expr_bind(ctx, state, params, kind, body)?;
            // Note: to avoid false alarms, we don't check recommends inside closures
            // (since there's no precondition on the closure parameters)
            state.push_scope();
            let params = state.rename_binders_exp(params);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions with check_pure_expr_bind
            let exp = expr_to_pure_exp_skip_checks(ctx, state, body)?;
            state.pop_scope();

            let trigs = Arc::new(vec![]); // real triggers will be set by finalize_exp
            let bnd = Spanned::new(body.span.clone(), BndX::Lambda(params.clone(), trigs));
            state.disable_recommends -= 1;
            Ok((check_stms, Maybe::Some(Value::Exp(mk_exp(ExpX::Bind(bnd, exp))))))
        }
        ExprX::NonSpecClosure {
            params,
            proof_fn_modes: _,
            body,
            requires,
            ensures,
            ret,
            external_spec,
        } => {
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
                .expect("external_spec should have been added in ast_simplify");
            state.push_scope();
            let uid =
                state.declare_imm_var_stm(&cid, &expr.typ, LocalDeclKind::ExecClosureId, false);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions in exec_closure_body_stms
            let cexp = expr_to_pure_exp_skip_checks(ctx, state, &cexpr)?;
            state.pop_scope();

            all_stms.push(Spanned::new(expr.span.clone(), StmX::Assume(cexp)));

            let v = mk_exp(ExpX::Var(uid));

            Ok((all_stms, Maybe::Some(Value::Exp(v))))
        }
        ExprX::ArrayLiteral(elems) => {
            let mut sequr = Sequencer::new();
            for elem in elems.iter() {
                let (stms0, e0) = expr_to_stm_opt(ctx, state, elem)?;
                push_or_return_never!(sequr.push(
                    stms0,
                    e0,
                    Immutable(LocalDeclKind::TempViaAssign)
                ));
            }
            let (stms, exps) = sequr.into_stms_exps(state);
            let array_lit = mk_exp(ExpX::ArrayLiteral(Arc::new(exps)));
            Ok((stms, Maybe::Some(Value::Exp(array_lit))))
        }
        ExprX::ExecFnByName(fun) => {
            let v = mk_exp(ExpX::ExecFnByName(fun.clone()));
            Ok((vec![], Maybe::Some(Value::Exp(v))))
        }
        ExprX::Choose { params, cond, body } => {
            let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::ChooseBinder));
            let mut check_stms = check_pure_expr_bind(ctx, state, params, kind, cond)?;
            check_stms.extend(check_pure_expr_bind(ctx, state, params, kind, body)?);
            state.push_scope();
            let params = state.rename_binders_exp(&params);
            // Use expr_to_pure_exp_skip_checks,
            // because we checked spec preconditions with check_pure_expr_bind
            let cond_exp = expr_to_pure_exp_skip_checks(ctx, state, cond)?;
            let body_exp = expr_to_pure_exp_skip_checks(ctx, state, body)?;
            state.pop_scope();
            let trigs = Arc::new(vec![]); // real triggers will be set by finalize_exp
            let bnd_choosex = BndX::Choose(params.clone(), trigs.clone(), cond_exp.clone());
            let bnd_choose = Spanned::new(body.span.clone(), bnd_choosex);
            let e_choose = mk_exp(ExpX::Bind(bnd_choose, body_exp));
            let e_choose = mk_exp(ExpX::Unary(UnaryOp::MustBeElaborated, e_choose));
            if state.checking_recommends(ctx) {
                let quant = crate::ast::Quant { quant: air::ast::Quant::Exists };
                let bnd_exists = Spanned::new(
                    body.span.clone(),
                    BndX::Quant(quant, params.clone(), trigs, None),
                );
                let e_exists = mk_exp(ExpX::Bind(bnd_exists, cond_exp.clone()));
                let e_exists = mk_exp(ExpX::Unary(UnaryOp::MustBeElaborated, e_exists));
                let error = error(
                    &cond_exp.span,
                    "recommendation not met: cannot prove that there exists values that satisfy the condition of the choose expression",
                );
                let assertx = StmX::Assert(state.next_assert_id(), Some(error), e_exists);
                check_stms.push(Spanned::new(cond_exp.span.clone(), assertx));
            }
            Ok((check_stms, Maybe::Some(Value::Exp(e_choose))))
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
            Ok((check_stms, Maybe::Some(Value::Exp(mk_exp(ExpX::WithTriggers(trigs, body_exp))))))
        }
        ExprX::Fuel(x, fuel, is_broadcast_use) => {
            // It's possible that the function may have pruned out of the crate
            // because there are no transitive dependencies.
            // If so, just skip the fuel/reveal statement entirely
            // (it can't possibly have any effect)
            let skip = !ctx.reveal_group_set.contains(x) && !ctx.func_map.contains_key(x);

            if skip {
                state.diagnostics.report(&warning(
                    &expr.span, "this reveal/fuel statement has no effect because no verification condition in this module depends on this function").to_any());
            }

            let stms = if skip {
                vec![]
            } else {
                if !is_broadcast_use {
                    let function = get_function(ctx, &expr.span, x)?;
                    if *fuel >= 2 && !crate::recursion::fun_is_recursive(ctx, &function) {
                        return Err(error(
                            &expr.span,
                            "this function is not recursive (nor mutually recursive), so fuel cannot be set to more than 1",
                        ));
                    }
                }

                let stm = Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel));
                vec![stm]
            };
            Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::RevealString(path) => {
            let stm = Spanned::new(expr.span.clone(), StmX::RevealString(path.clone()));
            Ok((vec![stm], Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::Header(_) => {
            return Err(error(&expr.span, "header expression not allowed here"));
        }
        ExprX::AssertAssume { is_assume: false, expr: e, msg } => {
            if state.checking_recommends(ctx) {
                let (mut stms, exp) = expr_to_stm_or_error(ctx, state, e)?;
                let stm = Spanned::new(expr.span.clone(), StmX::Assume(exp));
                stms.push(stm);
                Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
            } else {
                let mut stms: Vec<Stm> = Vec::new();
                // Use expr_to_pure_exp_skip_checks,
                // because we checked spec preconditions above with expr_to_stm_or_error
                let exp = expr_to_pure_exp_skip_checks(ctx, state, e)?;
                let exp = crate::heuristics::maybe_insert_auto_ext_equal(ctx, &exp, |x| x.assert);
                let small = is_small_exp_or_loc(&exp);
                let exp = if small {
                    exp.clone()
                } else {
                    // To avoid copying exp in Assert and Assume,
                    // put exp into a temporary variable
                    let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::Assert));
                    let (temp_id, temp_var) = state.declare_temp_var_stm(&exp.span, &exp.typ, kind);
                    stms.push(init_var(&exp.span, &temp_id, &exp));
                    temp_var
                };
                stms.push(Spanned::new(
                    e.span.clone(),
                    StmX::Assert(state.next_assert_id(), msg.clone(), exp.clone()),
                ));
                stms.push(Spanned::new(e.span.clone(), StmX::Assume(exp)));
                Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
            }
        }
        ExprX::AssertAssume { is_assume: true, expr: e, msg: _ } => {
            // Use expr_to_pure_exp_skip_checks,
            // because the goal of assume is to add an assumption, not to perform checks
            let exp = expr_to_pure_exp_skip_checks(ctx, state, e)?;
            let stm = Spanned::new(expr.span.clone(), StmX::Assume(exp));
            Ok((vec![stm], Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume, expr, fun } => {
            let (mut stms, exp) = expr_to_stm_opt(ctx, state, expr)?;

            if state.view_as_spec {
                return Ok((stms, exp));
            }

            let exp = to_exp_or_return_never!(exp, stms);

            let tmp = state.make_tmp_var_for_exp(&mut stms, exp);
            assert_assume_satisfies_user_defined_type_invariant(
                ctx, state, &tmp, &mut stms, fun, *is_assume,
            );
            Ok((stms, Maybe::Some(Value::Exp(tmp))))
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
            let mut locals: Vec<VarIdent> = Vec::new();
            for var in vars.iter() {
                let x = state.declare_imm_var_stm(
                    &var.name,
                    &var.a,
                    LocalDeclKind::AssertByVar { native: false },
                    true,
                );
                body.push(assume_has_typ(&x, &var.a, &require.span));
                locals.push(x);
            }
            let (mut proof_stms, e) = expr_to_stm_opt(ctx, state, proof)?;
            if let Maybe::Some(Value::Exp(_)) = e {
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
                let ensure_exp =
                    crate::heuristics::maybe_insert_auto_ext_equal(ctx, &ensure_exp, |x| {
                        x.assert_by
                    });
                let assert = Spanned::new(
                    ensure.span.clone(),
                    StmX::Assert(state.next_assert_id(), None, ensure_exp),
                );
                body.push(assert);
            }
            let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(body)));
            let deadend = Spanned::new(expr.span.clone(), StmX::DeadEnd(block));
            stms.push(deadend);
            state.pop_scope();

            // Translate ensure into an assume
            let implyx = ExprX::Binary(BinaryOp::Implies, require.clone(), ensure.clone());
            let imply = SpannedTyped::new(&ensure.span, &Arc::new(TypX::Bool), implyx);
            state.push_scope();
            let vars = state.rename_binders_exp(vars);
            // Use expr_to_pure_exp_skip_checks,
            // because we already checked spec preconditions for require and ensure above
            let imply_exp = expr_to_pure_exp_skip_checks(ctx, state, &imply)?;
            state.pop_scope();
            let trigs = Arc::new(vec![]); // real triggers will be set by finalize_exp
            let bndx = BndX::Quant(QUANT_FORALL, vars.clone(), trigs, Some(Arc::new(locals)));
            let bnd = Spanned::new(ensure.span.clone(), bndx);
            let forall_exp = mk_exp(ExpX::Bind(bnd, imply_exp));
            let forall_exp = mk_exp(ExpX::Unary(UnaryOp::MustBeElaborated, forall_exp));
            let assume = Spanned::new(ensure.span.clone(), StmX::Assume(forall_exp));
            stms.push(assume);
            Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::AssertQuery { requires, ensures, proof, mode } => {
            // Note that `ExprX::AssertQuery` makes a separate query for AssertQueryMode::NonLinear and AssertQueryMode::BitVector.
            // Only `requires` and type invariants will be provided to prove `ensures`.
            match mode {
                AssertQueryMode::NonLinear => {
                    let mut inner_body: Vec<Stm> = Vec::new();
                    let mut exps: Vec<Exp> = Vec::new();

                    // Translate body as separate query
                    state.push_scope();
                    for r in requires.iter() {
                        let (require_check_recommends, require_exp) =
                            expr_to_pure_exp_check(ctx, state, &r)?;
                        inner_body.extend(require_check_recommends);
                        let assume = Spanned::new(r.span.clone(), StmX::Assume(require_exp));
                        inner_body.push(assume);
                    }

                    let (proof_stms, e) = expr_to_stm_opt(ctx, state, proof)?;
                    if let Maybe::Some(Value::Exp(_)) = e {
                        return Err(error(
                            &expr.span,
                            "'assert ... by' block cannot end with an expression",
                        ));
                    }
                    inner_body.extend(proof_stms);

                    for e in ensures.iter() {
                        // Use expr_to_pure_exp_skip_checks,
                        // because we check spec preconditions below with check_pure_expr
                        let ensure_exp = expr_to_pure_exp_skip_checks(ctx, state, &e)?;
                        exps.push(ensure_exp.clone());
                        if state.checking_spec_preconditions(ctx) {
                            let check_stms = check_pure_expr(ctx, state, &e)?;
                            inner_body.extend(check_stms);
                        } else {
                            let assert = Spanned::new(
                                e.span.clone(),
                                StmX::Assert(state.next_assert_id(), None, ensure_exp),
                            );
                            inner_body.push(assert);
                        }
                    }

                    let inner_body =
                        Spanned::new(expr.span.clone(), StmX::Block(Arc::new(inner_body)));
                    state.pop_scope();

                    let mut outer: Vec<Stm> = Vec::new();

                    // Translate as assert, assume in outer query
                    for r in requires.iter() {
                        // Use expr_to_pure_exp_skip_checks,
                        // because we check spec preconditions below with check_pure_expr
                        let require_exp = expr_to_pure_exp_skip_checks(ctx, state, &r)?;
                        exps.push(require_exp.clone());
                        if state.checking_spec_preconditions(ctx) {
                            outer.extend(check_pure_expr(ctx, state, &r)?);
                        } else {
                            let assert = Spanned::new(
                                r.span.clone(),
                                StmX::Assert(
                                    state.next_assert_id(),
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
                            typ_inv_exps: Arc::new(exps),
                            typ_inv_vars: Arc::new(vec![]),
                            mode: *mode,
                        },
                    );
                    Ok((
                        vec![outer_block, nonlinear],
                        Maybe::Some(Value::ImplicitUnit(expr.span.clone())),
                    ))
                }

                AssertQueryMode::BitVector => {
                    // check if assertion block consists only of requires/ensures
                    let (proof_stms, e) = expr_to_stm_opt(ctx, state, proof)?;
                    let proof_block_err =
                        Err(error(&expr.span, "assert_bitvector_by cannot contain a proof block"));
                    if let Maybe::Some(Value::Exp(_)) = e {
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
                                    state.next_assert_id(),
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
                    Ok((
                        vec![outer_block, bitvector],
                        Maybe::Some(Value::ImplicitUnit(expr.span.clone())),
                    ))
                }
            }
        }
        ExprX::AssertCompute(e, compute) => {
            // We won't have the context to check recommends, so skip them
            state.disable_recommends += 1;
            let (mut stms, exp) = expr_to_pure_exp_check(ctx, state, &e)?;
            state.disable_recommends -= 1;
            let ret = Maybe::Some(Value::ImplicitUnit(exp.span.clone()));
            // We assert the (hopefully simplified) result of calling the interpreter
            // but assume the original expression, so we get the benefits
            // of any ensures, triggers, etc., that it might provide
            if !ctx.checking_spec_preconditions_for_non_spec() {
                let id = match compute {
                    ComputeMode::Z3 => state.next_assert_id(),
                    ComputeMode::ComputeOnly => None,
                };
                let assert =
                    Spanned::new(exp.span.clone(), StmX::AssertCompute(id, exp.clone(), *compute));
                stms.push(assert);
            }
            let assume = Spanned::new(exp.span.clone(), StmX::Assume(exp));
            stms.push(assume);
            Ok((stms, ret))
        }
        ExprX::If(expr0, expr1, None) => {
            let (stms0, e0) = expr_to_stm_opt(ctx, state, expr0)?;
            let (stms1, e1) = expr_to_stm_opt(ctx, state, expr1)?;
            let stms2 = vec![];
            let e2 = Maybe::Some(Value::ImplicitUnit(expr.span.clone()));
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
        ExprX::Loop { loop_isolation, is_for_loop, label, cond, body, invs, decrease } => {
            let is_for_loop = *is_for_loop;
            let loop_isolation = *loop_isolation;
            let id = state.loop_id_counter;
            state.loop_id_counter += 1;
            let invs = if is_for_loop && !loop_isolation {
                // The syntax macro doesn't have enough context to know whether ensures is needed,
                // so we have to fix up the invariants here.
                Arc::new(
                    invs.iter()
                        .filter_map(|inv| match inv.kind {
                            LoopInvariantKind::InvariantExceptBreak => Some(inv.clone()),
                            LoopInvariantKind::InvariantAndEnsures => Some(inv.clone()),
                            LoopInvariantKind::Ensures => None,
                        })
                        .collect(),
                )
            } else {
                invs.clone()
            };
            let has_break = loop_body_has_break(label, body);
            let simple_invs =
                invs.iter().all(|inv| inv.kind == LoopInvariantKind::InvariantAndEnsures);
            let simple_while = !has_break && simple_invs && cond.is_some() && loop_isolation;
            if !loop_isolation && !simple_invs {
                return Err(error(
                    &expr.span,
                    "loop invariants with 'loop_isolation(false)' cannot be invariant_except_break \
                        or ensures",
                ));
            }
            let mut cnd = if let Some(cond) = cond {
                let (stms0, e0) = expr_to_stm_opt(ctx, state, cond)?;
                let e0 = match e0 {
                    Maybe::Some(Value::Exp(e0)) => e0,
                    Maybe::Some(Value::ImplicitUnit(_)) => {
                        panic!("while loop condition doesn't return a bool expression");
                    }
                    Maybe::Never => {
                        // If the condition never returns (which would be odd, but it
                        // could happen) then the body of the while loop never gets to go at all.
                        return Ok((stms0, Maybe::Never));
                    }
                };
                let block0 = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(stms0)));
                Some((block0, e0))
            } else {
                None
            };
            if decrease.len() == 0
                && !ctx
                    .fun
                    .as_ref()
                    .map(|c| {
                        let function = &ctx.func_map[&c.current_fun];
                        function.x.attrs.exec_assume_termination
                            || function.x.attrs.exec_allows_no_decreases_clause
                    })
                    .unwrap_or(false)
            {
                return Err(error(&expr.span, "loop must have a decreases clause")
                    .help("to disable this check, use #[verifier::exec_allows_no_decreases_clause] on the function"));
            }

            let (mut stms1, _e1) = expr_to_stm_opt(ctx, state, body)?;
            let mut check_recommends: Vec<Stm> = Vec::new();
            let mut invs1: Vec<crate::sst::LoopInv> = Vec::new();
            for inv in invs.iter() {
                let (rec, exp) = expr_to_pure_exp_check(ctx, state, &inv.inv)?;
                let exp =
                    crate::heuristics::maybe_insert_auto_ext_equal(ctx, &exp, |x| x.invariant);
                check_recommends.extend(rec);
                let (at_entry, at_exit) = match inv.kind {
                    LoopInvariantKind::InvariantExceptBreak => (true, false),
                    LoopInvariantKind::InvariantAndEnsures => (true, true),
                    LoopInvariantKind::Ensures => (false, true),
                };
                let inv1 = crate::sst::LoopInv { inv: exp, at_entry, at_exit };
                invs1.push(inv1);
            }
            let mut decrease1: Vec<Exp> = Vec::new();
            for dec in decrease.iter() {
                let (rec, exp) = expr_to_pure_exp_check(ctx, state, dec)?;
                check_recommends.extend(rec);
                decrease1.push(exp);
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
            if !loop_isolation {
                // !loop_isolation handling expects a "loop", not a "while"
                assert!(cnd.is_none());
            }
            let pre_local_decls =
                crate::recursion::mk_decreases_at_entry_pre(ctx, Some(id), &decrease1)?;
            state.pre_local_decls.extend(pre_local_decls);
            let while_stm = Spanned::new(
                expr.span.clone(),
                StmX::Loop {
                    loop_isolation,
                    is_for_loop,
                    id,
                    label: label.clone(),
                    cond: cnd,
                    body: stms_to_one_stm(&body.span, stms1),
                    invs: Arc::new(invs1),
                    decrease: Arc::new(decrease1),
                    // These are filled in later, in sst_vars
                    typ_inv_vars: Arc::new(vec![]),
                    modified_vars: Arc::new(vec![]),
                },
            );
            if can_control_flow_reach_after_loop(expr) {
                let ret = Maybe::Some(Value::ImplicitUnit(expr.span.clone()));
                Ok((vec![while_stm], ret))
            } else {
                let stms = vec![while_stm, assume_false(&expr.span)];
                Ok((stms, Maybe::Never))
            }
        }
        ExprX::OpenInvariant(inv, binder, body, atomicity) => {
            // let inv_tmp = inv;
            // OpenInvariantBlock(inv_tmp.namespace(), {
            //   let mut inner = inner_tmp;
            //   assume(inv_tmp.inv(inner));
            //
            //   ...
            //
            //   assert(inv_tmp.inv(inner));
            // });

            // Evaluate `inv`
            let (mut stms0, big_inv_exp) = expr_to_stm_opt(ctx, state, inv)?;
            let big_inv_exp = to_exp_or_return_never!(big_inv_exp, stms0);

            // Assign it to a constant tmp variable to ensure it is constant
            // across the entire block. sst_to_air also relies on this.
            let (inv_tmp_id, inv_tmp_var) = state.declare_temp_assign(&big_inv_exp.span, &inv.typ);
            stms0.push(init_var(&big_inv_exp.span, &inv_tmp_id, &big_inv_exp));

            // Declare the inner_tmp variable
            let mut stms1 = vec![];
            let inner_typ = &binder.a;
            let (arb_id, arb_exp) = state.declare_temp_var_stm(
                &big_inv_exp.span,
                &inner_typ,
                PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::OpenInvariantInnerTemp)),
            );
            stms1.push(assume_has_typ(&arb_id, &inner_typ, &expr.span));

            // Assign to the bound variable
            let ident = state.get_var_unique_id(&binder.name);
            state.pre_local_decls.push(PreLocalDecl {
                ident: ident.clone(),
                typ: inner_typ.clone(),
                kind: PreLocalDeclKind::StmtLet,
            });
            stms1.push(init_var(&expr.span, &ident, &arb_exp));
            let inner_var = SpannedTyped::new(&expr.span, &inner_typ, ExpX::Var(ident));

            // Check that the invariant namespace is not already opened
            let typ_args = get_inv_typ_args(&big_inv_exp.typ);
            let ns_exp = call_namespace(ctx, &inv_tmp_var, &typ_args, *atomicity);

            if !state.checking_recommends(ctx) {
                for assertion in state.mask.as_ref().unwrap().contains(ctx, &ns_exp) {
                    stms1.push(Spanned::new(
                        expr.span.clone(),
                        StmX::Assert(state.next_assert_id(), Some(assertion.err), assertion.cond),
                    ))
                }
            }

            let mut inner_mask = Some(state.mask.as_ref().unwrap().remove(&ns_exp));

            // Assume the invariant
            let main_inv = call_inv(ctx, &inv_tmp_var, &inner_var, &typ_args, *atomicity);
            stms1.push(Spanned::new(expr.span.clone(), StmX::Assume(main_inv.clone())));

            // Process the body

            state.push_scope();
            std::mem::swap(&mut state.mask, &mut inner_mask);
            let (body_stms, body_e) = expr_to_stm_opt(ctx, state, body)?;
            std::mem::swap(&mut state.mask, &mut inner_mask);
            state.pop_scope();

            let body_stm = stms_to_one_stm(&expr.span, body_stms);
            stms1.push(body_stm);

            // Assert the invariant at the end

            match body_e.to_maybe_exp() {
                Maybe::Some(_e) => {
                    if !ctx.checking_spec_preconditions() {
                        let error =
                            error(&expr.span, "Cannot show invariant holds at end of block");
                        // Note, we re-use the `main_inv` exp here, but it contains a mutable
                        stms1.push(Spanned::new(
                            expr.span.clone(),
                            StmX::Assert(state.next_assert_id(), Some(error), main_inv),
                        ));
                    }
                }
                Maybe::Never => {
                    // It might be impossible to reach the end of the block
                    stms1.push(assume_false(&expr.span));
                }
            }

            let block_stm = stms_to_one_stm(&expr.span, stms1);
            stms0.push(Spanned::new(expr.span.clone(), StmX::OpenInvariant(block_stm)));
            return Ok((stms0, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))));
        }
        ExprX::Return(e1) => {
            let (mut stms, ret_exp) = match e1 {
                None => (vec![], sst_unit_value(&expr.span)),
                Some(e) => {
                    let (ret_stms, exp) = expr_to_stm_opt(ctx, state, e)?;
                    let exp = to_exp_or_return_never!(exp, ret_stms);

                    (ret_stms, exp)
                }
            };

            let containing_closure = state.containing_closure.clone();
            match &containing_closure {
                None => {
                    let base_error = error_with_secondary_label(
                        &expr.span,
                        crate::def::POSTCONDITION_FAILURE.to_string(),
                        "at this exit".to_string(),
                    );

                    stms.push(Spanned::new(
                        expr.span.clone(),
                        StmX::Return {
                            base_error,
                            ret_exp: Some(ret_exp),
                            inside_body: true,
                            assert_id: state.next_assert_id(),
                        },
                    ));
                }
                Some(closure_state) => {
                    closure_emit_postconditions(ctx, state, closure_state, &ret_exp, &mut stms);
                }
            }
            stms.push(assume_false(&expr.span));
            Ok((stms, Maybe::Never))
        }
        ExprX::BreakOrContinue { label, is_break } => {
            let stmx = StmX::BreakOrContinue { label: label.clone(), is_break: *is_break };
            let stm = Spanned::new(expr.span.clone(), stmx);
            Ok((vec![stm], Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::NeverToAny(e) => {
            let (mut stms, _e) = expr_to_stm_opt(ctx, state, e)?;
            stms.push(assume_false(&expr.span));
            Ok((stms, Maybe::Never))
        }
        ExprX::Ghost { .. } => {
            panic!("internal error: ExprX::Ghost should have been simplified by ast_simplify")
        }
        ExprX::ProofInSpec(e) => {
            let stms = if state.checking_spec_general(ctx) {
                let (stms, exp_opt) = expr_to_stm_opt(ctx, state, e)?;
                assert!(crate::ast_util::is_unit(&exp_opt.expect_exp().typ));
                stms
            } else {
                vec![]
            };
            Ok((stms, Maybe::Some(Value::ImplicitUnit(expr.span.clone()))))
        }
        ExprX::Block(stmts, body_opt) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut pre_local_decls: Vec<PreLocalDecl> = Vec::new();
            let mut binds: Vec<Bnd> = Vec::new();
            let mut is_pure_exp = true;
            let mut never_return = false;
            state.push_scope();
            for stmt in stmts.iter() {
                let (mut stms0, e0, decl_bnd_opt) = stmt_to_stm(ctx, state, stmt)?;
                match decl_bnd_opt {
                    Some((name, decl, bnd)) => {
                        state.push_scope();
                        pre_local_decls.push(decl.clone());
                        state.insert_var_maybe_exp(&name, &decl.ident);
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
                        if stms0.len() > 0 {
                            is_pure_exp = false;
                        }
                    }
                }
                stms.append(&mut stms0);
                match e0 {
                    Maybe::Never => {
                        is_pure_exp = false;
                        never_return = true;
                        // Don't process any of the later statements: they are unreachable.
                        break;
                    }
                    _ => {}
                }
            }
            let exp = if never_return {
                Maybe::Never
            } else if let Some(expr) = body_opt {
                let (mut stms1, exp) = expr_to_stm_opt(ctx, state, expr)?;
                if stms1.len() > 0 {
                    is_pure_exp = false;
                }
                stms.append(&mut stms1);
                exp
            } else {
                Maybe::Some(Value::ImplicitUnit(expr.span.clone()))
            };
            for _ in pre_local_decls.iter() {
                state.pop_scope();
            }
            state.pop_scope();
            match exp {
                Maybe::Some(Value::Exp(mut exp)) if is_pure_exp => {
                    // Pure expression: fold decls into Let bindings and return a single expression
                    for bnd in binds.iter().rev() {
                        let bnd = match &bnd.x {
                            BndX::Let(binders) => {
                                let binders = state.rename_delayed_to_exp_binders(binders);
                                bnd.new_x(BndX::Let(binders))
                            }
                            _ => panic!("expected BndX::Let for statement decl"),
                        };
                        exp = SpannedTyped::new(&expr.span, &exp.typ, ExpX::Bind(bnd, exp.clone()));
                    }
                    assert!(!never_return);
                    return Ok((vec![], Maybe::Some(Value::Exp(exp))));
                }
                _ => {
                    // Not pure: return statements + an expression
                    state.pre_local_decls.extend(pre_local_decls);
                    let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(stms)));
                    Ok((vec![block], exp))
                }
            }
        }
        ExprX::AirStmt(s) => {
            let stmt = Spanned::new(expr.span.clone(), StmX::Air(s.clone()));
            return Ok((vec![stmt], Maybe::Some(Value::ImplicitUnit(expr.span.clone()))));
        }
        ExprX::Nondeterministic => {
            let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::Nondeterministic));
            let (var_ident, exp) = state.declare_temp_var_stm(&expr.span, &expr.typ, kind);
            let stm = assume_has_typ(&var_ident, &expr.typ, &expr.span);
            Ok((vec![stm], Maybe::Some(Value::Exp(exp))))
        }
        ExprX::BorrowMut(_place) => {
            let (mut stms, bor_sst) = borrow_mut_to_sst(ctx, state, expr)?;
            match bor_sst {
                Maybe::Never => Ok((stms, Maybe::Never)),
                Maybe::Some(bor_sst) => {
                    let BorrowMutSst { phase2_stm, mut_ref_exp } = bor_sst;
                    stms.push(phase2_stm);
                    Ok((stms, Maybe::Some(Value::Exp(mut_ref_exp))))
                }
            }
        }
        ExprX::TwoPhaseBorrowMut(_place) => {
            panic!("TwoPhaseBorrowMut should have been handled by the parent node");
        }
        ExprX::ReadPlace(place, _read_type) => {
            let expr = place_to_expr(place);
            expr_to_stm_opt(ctx, state, &expr)
        }
        ExprX::UseLeftWhereRightCanHaveNoAssignments(e1, e2) => {
            let (mut stms, exp1) = expr_to_stm_opt(ctx, state, e1)?;
            let exp1 = to_exp_or_return_never!(exp1, stms);

            let (mut stms2, exp2) = expr_to_stm_opt(ctx, state, e2)?;
            let _exp2 = to_exp_or_return_never!(exp2, stms);

            stms.append(&mut stms2);
            Ok((stms, Maybe::Some(Value::Exp(exp1))))
        }
    }
}

/// Translate the given binary op given its two arguments as Exps.
/// This handles overflow-checking semantics, but it does NOT handle short-circuiting,
/// that must be handled by the caller.
fn binary_op_exp(
    ctx: &Ctx,
    state: &mut State,
    span: &Span,
    typ: &Typ,
    op: BinaryOp,
    e1: &Exp,
    e2: &Exp,
) -> (Vec<Stm>, Exp) {
    let pure_op = match op {
        BinaryOp::Arith(ArithOp::Add(_)) => BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow)),
        BinaryOp::Arith(ArithOp::Sub(_)) => BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Allow)),
        BinaryOp::Arith(ArithOp::Mul(_)) => BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Allow)),
        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => {
            BinaryOp::Arith(ArithOp::EuclideanDiv(Div0Behavior::Allow))
        }
        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => {
            BinaryOp::Arith(ArithOp::EuclideanMod(Div0Behavior::Allow))
        }
        BinaryOp::Index(kind, _) => BinaryOp::Index(kind, BoundsCheck::Allow),
        op => op,
    };
    let bin = SpannedTyped::new(span, typ, ExpX::Binary(pure_op, e1.clone(), e2.clone()));

    // Insert bounds check
    let check = match op {
        _ if state.view_as_spec => None,
        BinaryOp::Arith(arith) => match arith {
            ArithOp::Add(ob) | ArithOp::Sub(ob) | ArithOp::Mul(ob) => match ob {
                OverflowBehavior::Allow => None,
                OverflowBehavior::Truncate(_) => None,
                OverflowBehavior::Error(range) => {
                    let unary = UnaryOpr::HasType(Arc::new(TypX::Int(range)));
                    let has_type = ExpX::UnaryOpr(unary, bin.clone());
                    let has_type = SpannedTyped::new(span, &Arc::new(TypX::Bool), has_type);
                    Some((has_type, error(span, "possible arithmetic underflow/overflow")))
                }
            },
            ArithOp::EuclideanDiv(d0b) | ArithOp::EuclideanMod(d0b) => match d0b {
                Div0Behavior::Allow => None,
                Div0Behavior::Error => {
                    let zero = ExpX::Const(Constant::Int(BigInt::zero()));
                    let ne = ExpX::Binary(BinaryOp::Ne, e2.clone(), e2.new_x(zero));
                    let ne = SpannedTyped::new(span, &Arc::new(TypX::Bool), ne);
                    Some((ne, error(span, "possible division by zero")))
                }
            },
        },
        BinaryOp::Bitwise(bitwise, mode) => {
            match (mode, bitwise) {
                (BitshiftBehavior::Error, BitwiseOp::Shr(w) | BitwiseOp::Shl(w, _)) => {
                    // Add overflow checks for bit shifts
                    // For a shift `a << b` or `a >> b`, Rust requires that
                    //    0 <= b < (bitsize of a)
                    // However, for spec code, this is extended in the obvious way to
                    // integers outside the range (at least, for b >= 0).
                    // So we don't need to do a check for here spec code.

                    let zero = sst_int_literal(span, 0);
                    let bitwidth = sst_bitwidth(span, &w, &ctx.global.arch);

                    let assert_exp = sst_conjoin(
                        span,
                        &vec![sst_le(span, &zero, &e2), sst_lt(span, &e2, &bitwidth)],
                    );

                    let msg = "possible bit shift underflow/overflow";
                    Some((assert_exp, error(span, msg)))
                }
                (BitshiftBehavior::Allow, BitwiseOp::Shr(..) | BitwiseOp::Shl(..)) => None,
                (_, BitwiseOp::BitXor | BitwiseOp::BitAnd | BitwiseOp::BitOr) => {
                    // no overflow check needed
                    None
                }
            }
        }
        BinaryOp::Index(kind, bounds_check) => match bounds_check {
            BoundsCheck::Allow => None,
            BoundsCheck::Error => {
                Some(crate::place_preconditions::sst_index_bound(span, e1, e2, kind))
            }
        },
        _ => None,
    };

    let mut stms = vec![];

    if let Some((assert_exp, msg)) = check {
        if !state.checking_spec_preconditions(ctx) {
            let assert = StmX::Assert(state.next_assert_id(), Some(msg), assert_exp.clone());
            let assert = Spanned::new(span.clone(), assert);
            stms.push(assert);
        }

        let assume = StmX::Assume(assert_exp);
        let assume = Spanned::new(span.clone(), assume);
        stms.push(assume);
    }

    // Add truncation if necessary

    let trunc = if let BinaryOp::Arith(arith) = op {
        match arith {
            ArithOp::Add(ob) | ArithOp::Sub(ob) | ArithOp::Mul(ob) => match ob {
                OverflowBehavior::Allow => None,
                OverflowBehavior::Truncate(range) => Some(range),
                OverflowBehavior::Error(range) => Some(range),
            },
            _ => None,
        }
    } else {
        None
    };

    let bin = match trunc {
        Some(IntRange::Int) => bin,
        Some(range) => {
            let unary_op = UnaryOp::Clip { truncate: true, range };
            SpannedTyped::new(span, typ, ExpX::Unary(unary_op, bin))
        }
        None => bin,
    };

    (stms, bin)
}

/// Stms and Exps needed to execute a 2-phase borrow.
///
/// There's no phase1_stms field because it goes on the outside:
///  `(Vec<Stm>, Maybe<BorrowMutSst>)`
struct BorrowMutSst {
    /// Stm to execute "phase 2". It needs to be safe to delay this.
    phase2_stm: Stm,
    /// Exp representing the mutable borrow.
    /// This will always be a (non-mutable) temp variable.
    mut_ref_exp: Exp,
}

/// Given a mutable borrow expr (either BorrowMut or TwoPhaseBorrowMut), lowers it to the
/// SST semantics. The SST semantics include two phases:
///
///  - Phase 1: Evaluate the "place" and construct a mutable borrow such that
///    (mut_ref_current == the current value of the place) and mut_ref_future is arbitrary.
///
///  - Phase 2: Update the value of the "place" to be the mut_ref_future value.
///
/// For a "normal" borrow, these phases are executed together, and for a "two phase borrow",
/// they are executed apart. So for example, if we have a two-phase borrow in:
///
/// ```rust
/// let mut a = ...;
/// foo(&mut a, a.x); // imagine this is de-sugared from `a.foo(a.x)` or something that
///                   // actually creates a two-phase borrow
/// ```
///
/// The first phase would be the evaluation of `&mut a`, while the second phase (updating
/// the value of local variable `a`) would take place *after* the evaluation of `a.x`.
/// Thus, when `a.x` is executed, we correctly read the pre-borrow value of `a`.
fn borrow_mut_to_sst(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Maybe<BorrowMutSst>), VirErr> {
    let place = match &expr.x {
        ExprX::BorrowMut(p) => p,
        ExprX::TwoPhaseBorrowMut(p) => p,
        _ => panic!("borrow_mut_to_sst must be called for BorrowMut or TwoPhaseBorrowMut"),
    };

    let (stms, exps) = place_to_exp_pair(ctx, state, place)?;
    let (lhs_exp, normal_exp) = unwrap_or_return_never!(exps, stms);

    // phase 1
    let (var_ident, mut_ref_exp) = state.declare_temp_var_stm(
        &expr.span,
        &expr.typ,
        PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::BorrowMut)),
    );
    let has_typ_stm = assume_has_typ(&var_ident, &expr.typ, &expr.span);

    let cur_exp = sst_mut_ref_current(&expr.span, &mut_ref_exp);
    let equal = sst_equal(&expr.span, &cur_exp, &normal_exp);
    let assume_stm = Spanned::new(expr.span.clone(), StmX::Assume(equal));

    let mut phase1_stms = stms;
    phase1_stms.push(has_typ_stm);
    phase1_stms.push(assume_stm);

    // phase 2

    let sn = crate::ast::MutRefFutureSourceName::MutRefFuture;
    let future_expx = ExpX::Unary(UnaryOp::MutRefFuture(sn), mut_ref_exp.clone());
    let t = match &*expr.typ {
        TypX::MutRef(t) => t,
        _ => panic!("sst_mut_ref_future expected MutRef type"),
    };
    let future_exp = SpannedTyped::new(&expr.span, &t, future_expx);

    let assignx = StmX::Assign { lhs: Dest { dest: lhs_exp, is_init: false }, rhs: future_exp };
    let assign = Spanned::new(expr.span.clone(), assignx);

    Ok((phase1_stms, Maybe::Some(BorrowMutSst { phase2_stm: assign, mut_ref_exp })))
}

/// Use this when you need to both read and write to a given place
///
/// Returns two expressions:
/// (i) the place as sst "loc" (l-value) which MUST NOT depend on any mutable vars.
/// (ii) the evaluation of the place (by definition, this is dependent
/// on the mutable var in question, but it must not depend on any other mutable vars)
fn place_to_exp_pair(
    ctx: &Ctx,
    state: &mut State,
    place: &Place,
) -> Result<(Vec<Stm>, Maybe<(Exp, Exp)>), VirErr> {
    let mk_exp = |expx: ExpX| SpannedTyped::new(&place.span, &place.typ, expx);
    let (stms, exps) = place_to_exp_pair_rec(ctx, state, place)?;
    let exps = match exps {
        Maybe::Never => Maybe::Never,
        Maybe::Some((e1, e2)) => {
            let e1 = mk_exp(ExpX::Loc(e1));
            Maybe::Some((e1, e2))
        }
    };
    Ok((stms, exps))
}

fn place_to_exp_pair_rec(
    ctx: &Ctx,
    state: &mut State,
    place: &Place,
) -> Result<(Vec<Stm>, Maybe<(Exp, Exp)>), VirErr> {
    let mk_exp = |expx: ExpX| SpannedTyped::new(&place.span, &place.typ, expx);
    match &place.x {
        PlaceX::Field(field_opr, p) => {
            let (mut stms, exps) = place_to_exp_pair_rec(ctx, state, p)?;
            let (e1, e2) = unwrap_or_return_never!(exps, stms);

            let check = match field_opr.check {
                VariantCheck::Union => {
                    let (condition, msg) =
                        crate::place_preconditions::sst_field_check(&place.span, &e2, field_opr);
                    Some((condition, msg))
                }
                VariantCheck::None => None,
            };
            if let Some((condition, msg)) = check {
                if !state.checking_recommends(ctx) {
                    let assert = StmX::Assert(state.next_assert_id(), Some(msg), condition.clone());
                    let assert = Spanned::new(place.span.clone(), assert);
                    stms.push(assert);
                }
                let assume = StmX::Assume(condition);
                let assume = Spanned::new(place.span.clone(), assume);
                stms.push(assume);
            }

            let field_opr = FieldOpr { check: VariantCheck::None, ..field_opr.clone() };

            let e1 = mk_exp(ExpX::UnaryOpr(UnaryOpr::Field(field_opr.clone()), e1));
            let e2 = mk_exp(ExpX::UnaryOpr(UnaryOpr::Field(field_opr), e2));
            Ok((stms, Maybe::Some((e1, e2))))
        }
        PlaceX::DerefMut(p) => {
            let (stms, exps) = place_to_exp_pair_rec(ctx, state, p)?;
            let (e1, e2) = unwrap_or_return_never!(exps, stms);
            let e1 = mk_exp(ExpX::Unary(UnaryOp::MutRefCurrent, e1));
            let e2 = mk_exp(ExpX::Unary(UnaryOp::MutRefCurrent, e2));
            Ok((stms, Maybe::Some((e1, e2))))
        }
        PlaceX::Local(x) => {
            let unique_id = state.get_var_unique_id(&x);
            let e_l = mk_exp(ExpX::VarLoc(unique_id.clone()));
            let e_r = mk_exp(ExpX::Var(unique_id));
            let e_r = mk_exp(ExpX::Unary(UnaryOp::MustBeFinalized, e_r));
            Ok((vec![], Maybe::Some((e_l, e_r))))
        }
        PlaceX::Temporary(e) => {
            let (mut stms, v) = expr_to_stm_opt(ctx, state, e)?;
            let exp = to_exp_or_return_never!(v, stms);

            let (temp_id, temp_var) =
                state.declare_temp_var_stm(&exp.span, &exp.typ, PreLocalDeclKind::StmtLet);
            stms.push(init_var(&exp.span, &temp_id, &exp));

            let e_l = mk_exp(ExpX::VarLoc(temp_id.clone()));

            Ok((stms, Maybe::Some((e_l, temp_var))))
        }
        PlaceX::WithExpr(e, p) => {
            let (mut stms, v) = expr_to_stm_opt(ctx, state, e)?;
            let _e = unwrap_or_return_never!(v, stms);

            let (mut stms2, exps) = place_to_exp_pair_rec(ctx, state, p)?;
            stms.append(&mut stms2);

            Ok((stms, exps))
        }
        PlaceX::ModeUnwrap(p, _mode) => place_to_exp_pair_rec(ctx, state, p),
        PlaceX::Index(p, idx, kind, bounds_check) => {
            let (mut stms, exps) = place_to_exp_pair_rec(ctx, state, p)?;
            let exps = unwrap_or_return_never!(exps, stms);

            let (mut stms2, idx_v) = expr_to_stm_opt(ctx, state, idx)?;
            stms.append(&mut stms2);
            let idx_exp = to_exp_or_return_never!(idx_v, stms);

            let idx_exp = state.make_tmp_var_for_exp(&mut stms, idx_exp);

            match bounds_check {
                BoundsCheck::Allow => {}
                BoundsCheck::Error => {
                    let (condition, msg) = crate::place_preconditions::sst_index_bound(
                        &place.span,
                        &exps.1,
                        &idx_exp,
                        *kind,
                    );
                    if !state.checking_recommends(ctx) {
                        let stm = Spanned::new(
                            place.span.clone(),
                            StmX::Assert(state.next_assert_id(), Some(msg), condition.clone()),
                        );
                        stms.push(stm);
                    }
                    let stm = Spanned::new(place.span.clone(), StmX::Assume(condition));
                    stms.push(stm);
                }
            }

            let op = BinaryOp::Index(*kind, BoundsCheck::Allow);
            let e_l = mk_exp(ExpX::Binary(op, exps.0, idx_exp.clone()));
            let e_r = mk_exp(ExpX::Binary(op, exps.1, idx_exp));

            Ok((stms, Maybe::Some((e_l, e_r))))
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
) -> Result<(Vec<Stm>, Maybe<Value>, Option<(VarIdent, PreLocalDecl, Option<Bnd>)>), VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => {
            let (stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
            Ok((stms, exp, None))
        }
        StmtX::Decl { pattern, mode: _, init, els } => {
            if els.is_some() {
                panic!("let-else should be simplified in ast_simpllify {:?}.", stmt)
            }
            let (name, typ) = match &pattern.x {
                PatternX::Var(PatternBinding {
                    name,
                    user_mut: _,
                    by_ref: ByRef::No,
                    typ,
                    copy: _,
                }) => (name, typ),
                _ => panic!("internal error: Decl should have been simplified by ast_simplify"),
            };

            let rename = state.rename_var_maybe_exp(&name);
            let ident = rename.clone();
            let decl = PreLocalDecl { ident, typ: typ.clone(), kind: PreLocalDeclKind::StmtLet };

            let init = init.as_ref().map(|init| place_to_expr(init));

            // First check if the initializer needs to be translate to a Call instead
            // of an Exp. If so, translate it that way.
            if let Some(init) = &init {
                match expr_must_be_call_stm(ctx, state, Some(&typ), init)? {
                    Some((stms, Maybe::Never)) => {
                        return Ok((stms, Maybe::Never, None));
                    }
                    Some((
                        mut stms,
                        Maybe::Some(ReturnedCall {
                            fun,
                            resolved_method,
                            is_trait_default,
                            typs,
                            has_return: _,
                            args,
                        }),
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
                            is_trait_default,
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
                        let ret = Maybe::Some(Value::ImplicitUnit(stmt.span.clone()));
                        return Ok((stms, ret, Some((name.clone(), decl, None))));
                    }
                    None => {}
                }
            }

            // Otherwise, translate the initializer to an Exp.
            let (mut stms, exp) = match &init {
                None => (vec![], None),
                Some(init) => {
                    let (stms, exp) = expr_to_stm_opt(ctx, state, init)?;
                    let exp = match exp.to_maybe_exp() {
                        Maybe::Some(exp) => exp,
                        Maybe::Never => {
                            return Ok((stms, Maybe::Never, None));
                        }
                    };
                    (stms, Some(exp))
                }
            };

            // For a pure expression (i.e., one with no SST statements), return a binder
            let bnd = match &exp {
                Some(exp) if stms.len() == 0 => {
                    let binder = VarBinderX { name: rename.clone(), a: exp.clone() };
                    let bnd = BndX::Let(Arc::new(vec![Arc::new(binder)]));
                    Some(Spanned::new(stmt.span.clone(), bnd))
                }
                _ => None,
            };

            match &exp {
                None => {}
                Some(exp) => {
                    stms.push(init_var(&stmt.span, &decl.ident, exp));
                }
            }

            let ret = Maybe::Some(Value::ImplicitUnit(stmt.span.clone()));
            Ok((stms, ret, Some((name.clone(), decl, bnd))))
        }
    }
}

/// Handle the internal of a closure
fn exec_closure_body_stms(
    ctx: &Ctx,
    state: &mut State,
    params: &VarBinders<Typ>,
    ret: &VarBinder<Typ>,
    body: &Expr,
    requires: &Exprs,
    ensures: &Exprs,
) -> Result<(Vec<Stm>, Arc<Vec<(UniqueIdent, Typ)>>), VirErr> {
    let mut typ_inv_vars = vec![];

    state.push_scope();

    // Right now there is no way to specify an invariant mask on a closure function
    // All closure funcs are assumed to have mask set 'full'
    let mut mask = Some(MaskSet::full(&body.span));
    std::mem::swap(&mut state.mask, &mut mask);

    for param in params.iter() {
        // TODO(new_mut_ref): can't assume closure params are immutable anymore
        let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::ExecClosureParam));
        let uid = state.declare_var_stm(&param.name, &param.a, kind, false);
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

    let kind = PreLocalDeclKind::Immutable(Immutable(LocalDeclKind::ExecClosureRet));
    state.declare_var_stm(&ret.name, &ret.a, kind, false);
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

    match exp.to_maybe_exp() {
        Maybe::Some(e) => {
            // Post condition for the return-value expression

            let closure_state = containing_closure.as_ref().unwrap();
            closure_emit_postconditions(ctx, state, closure_state, &e, &mut stms);
        }
        Maybe::Never => { /* never-return case */ }
    }

    std::mem::swap(&mut state.mask, &mut mask);
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
            let er = error_with_secondary_label(
                &ret_value.span,
                "unable to prove post-condition of closure",
                "returning this expression",
            )
            .primary_label(&ens.span, crate::def::THIS_POST_FAILED);
            let stm = Spanned::new(
                ens.span.clone(),
                StmX::Assert(state.next_assert_id(), Some(er), ens.clone()),
            );
            stms.push(stm);
        }
    }
}

fn get_inv_typ_args(typ: &Typ) -> Typs {
    match &**typ {
        TypX::Datatype(_, typs, _) => typs.clone(),
        TypX::Decorate(_, _, typ) | TypX::Boxed(typ) => get_inv_typ_args(typ),
        _ => {
            panic!("get_inv_typ_args failed, expected some Invariant type");
        }
    }
}

fn call_inv(ctx: &Ctx, outer: &Exp, inner: &Exp, typ_args: &Typs, atomicity: InvAtomicity) -> Exp {
    let call_fun =
        CallFun::Fun(crate::def::fn_inv_name(&ctx.global.vstd_crate_name, atomicity), None);
    let expx = ExpX::Call(call_fun, typ_args.clone(), Arc::new(vec![outer.clone(), inner.clone()]));
    SpannedTyped::new(&outer.span, &Arc::new(TypX::Bool), expx)
}

fn call_namespace(ctx: &Ctx, arg: &Exp, typ_args: &Typs, atomicity: InvAtomicity) -> Exp {
    let call_fun =
        CallFun::Fun(crate::def::fn_namespace_name(&ctx.global.vstd_crate_name, atomicity), None);
    let expx = ExpX::Call(call_fun, typ_args.clone(), Arc::new(vec![arg.clone()]));
    SpannedTyped::new(&arg.span, &Arc::new(TypX::Int(IntRange::Int)), expx)
}

pub fn assert_assume_satisfies_user_defined_type_invariant(
    ctx: &Ctx,
    state: &mut State,
    exp: &Exp,
    stms: &mut Vec<Stm>,
    fun: &Fun,
    is_assume: bool,
) {
    let typs = match &*undecorate_typ(&exp.typ) {
        TypX::Datatype(_path, typs, ..) => typs.clone(),
        _ => panic!("assert_assume_satisfies_user_defined_type_invariant: expected datatype"),
    };
    let call_fun = CallFun::Fun(fun.clone(), None);
    let expx = ExpX::Call(call_fun, typs, Arc::new(vec![exp.clone()]));
    let exp = SpannedTyped::new(&exp.span, &Arc::new(TypX::Bool), expx);

    if state.checking_recommends(ctx) {
        stms.push(Spanned::new(exp.span.clone(), StmX::Assume(exp)));
    } else {
        let exp = state.make_tmp_var_for_exp(stms, exp);

        let function = ctx.func_map.get(fun).unwrap();
        let error = crate::messages::error(
            &exp.span,
            "constructed value may fail to meet its declared type invariant",
        )
        .secondary_label(&function.span, "type invariant declared here");
        if !is_assume {
            stms.push(Spanned::new(
                exp.span.clone(),
                StmX::Assert(state.next_assert_id(), Some(error), exp.clone()),
            ));
        }
        stms.push(Spanned::new(exp.span.clone(), StmX::Assume(exp)));
    }
}
