use crate::rustc_index::Idx;
use crate::thir::cx::ThirBuildCx;
use hir::HirId;
use itertools::Itertools;
use rustc_hir as hir;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::hir::place::{Place, Projection, ProjectionKind};
use rustc_middle::middle::region;
use rustc_middle::mir::FakeReadCause;
use rustc_middle::thir;
use rustc_middle::thir::{
    AdtExprBase, Arm, ArmId, Block, BlockId, BlockSafety, Expr, ExprId, ExprKind, LocalVarId, Pat,
    PatKind, Stmt, StmtId, StmtKind, TempLifetime,
};
use rustc_middle::ty;
use rustc_middle::ty::{
    Binder, BoundRegion, BoundRegionKind, BoundVar, BoundVarIndexKind, BoundVariableKind,
    CapturedPlace, GenericArg, Mutability, Ty, TyCtxt, TyKind, TypeSuperFoldable, UpvarCapture,
};
use rustc_middle::ty::{TypeFoldable, TypeFolder, UpvarArgs};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, RwLock};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VarErasure {
    Erase,
    Keep,
}

/// This type explains how we propagate the 'spec' status through a given node.
/// Yes = expect the argument to be spec
/// No = expect the argument to be non-spec
/// Propagate = expect the argument to be spec iff the node itself is spec.
///
/// ExpectSpec is for a single argument; ExpectSpecArgs is for argument lists.
///
/// Example: datatype constructor is propagate
/// Example: Function may have a mix of spec and proof arguments so
///          in general you may mix it up between Yes and No.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ExpectSpec {
    Yes,
    No,
    Propagate,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExpectSpecArgs {
    AllYes,
    AllNo,
    AllPropagate,
    PerArg(Arc<Vec<ExpectSpec>>),
}

/// Do we erase a given node (no bearing on whether we erase its subexpressions)
/// When we erase a node `call(x1, x2)` but not the subexpressions x1, x2, it will look like:
/// { x1; x2; arbitrary_ghost_value() }
/// This depends on the 'spec' status.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum NodeErase {
    Erase,
    Keep,
    WhenExpectingSpec,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CallErasure {
    /// Erase the call and ALL subexpressions. This can only be used when the node is guaranteed
    /// to have no proof code in the subtree (outer_mode = spec in modes.rs)
    EraseTree,
    Call(NodeErase, ExpectSpecArgs),
}

/// Information for a body (function or closure).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct BodyErasure {
    pub erase_body: bool,
    pub ret_spec: bool,
}

/// Global context with all information across the krate.
/// This is created after mode-checking and passed here via the VERUS_ERASURE_CTXT global.
#[derive(Debug)]
pub struct VerusErasureCtxt {
    /// For a given var (decl or use), should we erase it?
    /// Also includes patterns.
    pub vars: HashMap<HirId, VarErasure>,

    /// For a call, how do we handle it?
    /// This includes struct constructors as well. The "args" go in source order,
    /// i.e., same order as the fields on the Struct node.
    /// If there's a '..struct_tail' in the ctor, it's the last argument.
    pub calls: HashMap<HirId, CallErasure>,

    pub bodies: HashMap<LocalDefId, BodyErasure>,

    /// Conditions on 'if' statements and discriminants in 'match' statements
    pub condition_spec: HashMap<HirId, bool>,

    /// Some DefIds from builtin that we'll need to handle directly
    pub erased_ghost_value_fn_def_id: DefId,
    pub dummy_capture_struct_def_id: DefId,
}

/// Used to communicate the set of LocalDefIds that may require erasure.
static VERUS_AWARE_DEF_IDS: RwLock<Option<Arc<HashSet<LocalDefId>>>> = RwLock::new(None);

/// Used to communicate the VerusErasureCtxt
static VERUS_ERASURE_CTXT: RwLock<Option<Arc<VerusErasureCtxt>>> = RwLock::new(None);

pub fn set_verus_aware_def_ids(ids: Arc<HashSet<LocalDefId>>) {
    let v: &mut Option<Arc<HashSet<LocalDefId>>> = &mut VERUS_AWARE_DEF_IDS.write().unwrap();
    if v.is_some() {
        panic!("VERUS_AWARE_DEF_IDS has already been set");
    }
    *v = Some(ids);
}

pub fn set_verus_erasure_ctxt(erasure_ctxt: Arc<VerusErasureCtxt>) {
    let v: &mut Option<Arc<VerusErasureCtxt>> = &mut VERUS_ERASURE_CTXT.write().unwrap();
    if v.is_some() {
        panic!("VERUS_ERASURE_CTXT has already been set");
    }
    *v = Some(erasure_ctxt);
}

fn get_verus_erasure_ctxt() -> Arc<VerusErasureCtxt> {
    VERUS_ERASURE_CTXT
        .read()
        .unwrap()
        .as_ref()
        .expect("Expected VerusErasureCtxt for THIR modification pass")
        .clone()
}

fn get_verus_erasure_ctxt_option() -> Option<Arc<VerusErasureCtxt>> {
    VERUS_ERASURE_CTXT.read().unwrap().clone()
}

/// Our erasure scheme will fail if this query runs too early, before we initialize the
/// VerusErasureCtxt. However, there are some items where this happens
/// intentionally (e.g., for consts, which may be evaluated during type-checking).
///
/// rust_verify needs to follow the scheme:
///
///  1. Compute the set of LocalDefIds that require erasure, and initialize the VERUS_AWARE_DEF_IDS
///  2. Run hir_typeck, compute mode info
///  3. initialize the VERUS_ERASURE_CTXT
///  4. Run lifetime checking
///
/// As a result, thir_body is able to sanity check we're in a consistent state.
/// If the VERUS_ERASURE_CTXT hasn't been initialized yet, we check that the given
/// item is one that doesn't need it.
pub(crate) fn check_this_query_isnt_running_early(local_def_id: LocalDefId) {
    if get_verus_erasure_ctxt_option().is_none() {
        match VERUS_AWARE_DEF_IDS.read().unwrap().clone() {
            Some(m) => {
                if m.contains(&local_def_id) {
                    panic!(
                        "Internal Verus Error: The thir_body query is running for item {:?} which may require erasure, but the VerusErasureCtxt has not been initialized. Please file a github issue for this error and consider using `--no-lifetime` as a temperary measure to work around the issue.",
                        local_def_id
                    );
                }
            }
            None => {
                panic!(
                    "Internal Verus Error: The thir_body query is running for item {:?}, but the VerusAwareDefIds map has not been initialized. Please file a github issue for this error and consider using `--no-lifetime` as a temporary measure to work around the issue.",
                    local_def_id
                );
            }
        }
    }
}

/// Per-body context (i.e., one for each function or closure).
pub(crate) struct VerusThirBuildCtxt {
    ctxt: Option<Arc<VerusErasureCtxt>>,
    closure_overrides: HashMap<LocalDefId, ClosureOverrides>,
    pub(crate) expr_is_spec: HashMap<HirId, bool>,
    local_def_id: LocalDefId,
}

impl VerusThirBuildCtxt {
    pub(crate) fn new<'tcx>(_tcx: TyCtxt<'tcx>, local_def_id: LocalDefId) -> Self {
        VerusThirBuildCtxt {
            ctxt: get_verus_erasure_ctxt_option(),
            closure_overrides: HashMap::new(),
            expr_is_spec: HashMap::new(),
            local_def_id,
        }
    }

    pub(crate) fn ret_spec<'tcx>(&self) -> bool {
        match &self.ctxt {
            None => false,
            Some(ctxt) => match ctxt.bodies.get(&self.local_def_id) {
                Some(b) => b.ret_spec,
                None => false,
            },
        }
    }

    pub(crate) fn condition_spec<'tcx>(&self, expr: &hir::Expr<'tcx>) -> bool {
        match &self.ctxt {
            None => false,
            Some(ctxt) => matches!(ctxt.condition_spec.get(&expr.hir_id), Some(true)),
        }
    }

    pub(crate) fn var_spec<'tcx>(&self, hir_id: HirId) -> bool {
        match &self.ctxt {
            None => false,
            Some(ctxt) => matches!(ctxt.vars.get(&hir_id), Some(VarErasure::Erase)),
        }
    }

    pub(crate) fn skip_closure<'tcx>(&self, local_def_id: LocalDefId) -> bool {
        match &self.ctxt {
            None => false,
            Some(ctxt) => match ctxt.bodies.get(&local_def_id) {
                Some(b) => b.erase_body,
                None => false,
            },
        }
    }
}

impl NodeErase {
    pub(crate) fn should_erase(&self, spec: bool) -> bool {
        match self {
            NodeErase::Erase => true,
            NodeErase::Keep => false,
            NodeErase::WhenExpectingSpec => spec,
        }
    }
}

impl ExpectSpec {
    pub(crate) fn apply(&self, spec: bool) -> bool {
        match self {
            ExpectSpec::Yes => true,
            ExpectSpec::No => false,
            ExpectSpec::Propagate => spec,
        }
    }
}

impl CallErasure {
    pub fn keep_all() -> Self {
        CallErasure::Call(NodeErase::Keep, ExpectSpecArgs::AllNo)
    }

    pub(crate) fn should_erase(&self, spec: bool) -> bool {
        match self {
            CallErasure::EraseTree => panic!("EraseTree should be handled by mirror_expr_opt"),
            CallErasure::Call(node_erase, _spec_args) => node_erase.should_erase(spec),
        }
    }
}

impl ExpectSpecArgs {
    pub fn get(&self, i: usize) -> ExpectSpec {
        match self {
            ExpectSpecArgs::AllNo => ExpectSpec::No,
            ExpectSpecArgs::AllYes => ExpectSpec::Yes,
            ExpectSpecArgs::AllPropagate => ExpectSpec::Propagate,
            ExpectSpecArgs::PerArg(args) => args[i],
        }
    }

    pub fn last(&self) -> ExpectSpec {
        match self {
            ExpectSpecArgs::AllNo => ExpectSpec::No,
            ExpectSpecArgs::AllYes => ExpectSpec::Yes,
            ExpectSpecArgs::AllPropagate => ExpectSpec::Propagate,
            ExpectSpecArgs::PerArg(args) => *args.last().unwrap(),
        }
    }
}

pub(crate) fn handle_call<'tcx>(
    verus_ctxt: &VerusThirBuildCtxt,
    expr: &'tcx hir::Expr<'tcx>,
) -> CallErasure {
    let Some(erasure_ctxt) = verus_ctxt.ctxt.clone() else {
        return CallErasure::keep_all();
    };

    match erasure_ctxt.calls.get(&expr.hir_id) {
        None => CallErasure::keep_all(),
        Some(call_erasure) => call_erasure.clone(),
    }
}

pub(crate) fn should_erase_var(verus_ctxt: &VerusThirBuildCtxt, var_hir_id: HirId) -> bool {
    let Some(erasure_ctxt) = verus_ctxt.ctxt.clone() else {
        return false;
    };
    matches!(erasure_ctxt.vars.get(&var_hir_id), Some(VarErasure::Erase))
}

pub(crate) fn handle_var<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    _var_hir_id: HirId,
    spec: bool,
) -> Option<ExprKind<'tcx>> {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return None;
    };
    if !spec && matches!(erasure_ctxt.vars.get(&expr.hir_id), None | Some(VarErasure::Keep)) {
        return None;
    }
    let ty = cx.typeck_results.expr_ty(expr);
    Some(erased_ghost_value_kind(cx, &erasure_ctxt, expr.hir_id, expr.span, ty))
}

pub(crate) fn expr_id_from_kind<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    kind: ExprKind<'tcx>,
    hir_id: HirId,
    span: Span,
    ty: Ty<'tcx>,
) -> ExprId {
    let (temp_lifetime, backwards_incompatible) =
        cx.rvalue_scopes.temporary_scope(cx.region_scope_tree, hir_id.local_id);
    let e = Expr {
        temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible },
        ty,
        span: span,
        kind,
    };
    cx.thir.exprs.push(e)
}

/// erase_tree
/// This erases the expression and all HIR subexpressions.
/// (Mostly. It also keeps expressions that need pattern-exhaustiveness checking.)

pub(crate) fn erase_tree<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
) -> ExprId {
    let kind = erase_tree_kind(cx, hir_expr);
    let ty = cx.typeck_results.expr_ty(hir_expr);

    let (temp_lifetime, backwards_incompatible) =
        cx.rvalue_scopes.temporary_scope(cx.region_scope_tree, hir_expr.hir_id.local_id);
    let expr = Expr {
        temp_lifetime: TempLifetime { temp_lifetime, backwards_incompatible },
        ty,
        span: hir_expr.span,
        kind,
    };

    let expr_scope =
        region::Scope { local_id: hir_expr.hir_id.local_id, data: region::ScopeData::Node };
    let expr = Expr {
        temp_lifetime: expr.temp_lifetime,
        ty: expr.ty,
        span: hir_expr.span,
        kind: ExprKind::Scope {
            region_scope: expr_scope,
            value: cx.thir.exprs.push(expr),
            lint_level: rustc_middle::thir::LintLevel::Explicit(hir_expr.hir_id),
        },
    };
    cx.thir.exprs.push(expr)
}

pub(crate) fn erase_tree_kind<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> ExprKind<'tcx> {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        panic!("erased_expr_id_from_expr called without erasure ctxt");
    };

    // We have to preserve all match statements
    let pat_exprs = get_all_stmts_with_pattern_checking(cx, &erasure_ctxt, expr);

    let ty = cx.typeck_results.expr_ty(expr);
    erased_ghost_value_kind_with_args(cx, &erasure_ctxt, expr.hir_id, expr.span, ty, pat_exprs)
}

/// erase_node
/// This erases a single node but not the children.
/// We create a value `erased_ghost_value::<T>::((args...))` where `args` contains anything
/// that needs checking from the subexpressions.

/// Erase the node; use the unadjusted type of the hir_expr
pub(crate) fn maybe_erase_node_unadjusted<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    kind: ExprKind<'tcx>,
    erase: bool,
) -> ExprKind<'tcx> {
    if erase { erase_node_unadjusted(cx, hir_expr, kind) } else { kind }
}

/// Erase the node; use the given type (this is useful for adjusted expressions)
pub(crate) fn maybe_erase_node<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    ty: Ty<'tcx>,
    kind: ExprKind<'tcx>,
    erase: bool,
) -> ExprKind<'tcx> {
    if erase { erase_node(cx, hir_expr, ty, kind) } else { kind }
}

pub(crate) fn erase_node_unadjusted<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    kind: ExprKind<'tcx>,
) -> ExprKind<'tcx> {
    let ty = cx.typeck_results.expr_ty(hir_expr);
    erase_node(cx, hir_expr, ty, kind)
}

pub(crate) fn erase_node<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    ty: Ty<'tcx>,
    kind: ExprKind<'tcx>,
) -> ExprKind<'tcx> {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        panic!("erase_node called for const value");
    };

    let expr_ids = match kind {
        ExprKind::Call { ty: _, fun, args, from_hir_call: _, fn_span: _ } => {
            let mut v = vec![];
            v.push(fun);
            for arg in args.iter() {
                v.push(*arg);
            }
            v
        }
        ExprKind::Adt(adt) => {
            let mut v = vec![];
            for f in adt.fields.iter() {
                v.push(f.expr);
            }
            match adt.base {
                AdtExprBase::None => {}
                AdtExprBase::Base(fru) => {
                    v.push(fru.base);
                }
                AdtExprBase::DefaultFields(_tys) => {}
            }
            v
        }
        ExprKind::Borrow { borrow_kind: _, arg } => {
            vec![arg]
        }
        ExprKind::Deref { arg } => {
            vec![arg]
        }
        ExprKind::Field { lhs, variant_index: _, name: _ } => {
            vec![lhs]
        }
        _ => {
            panic!("erase_node got unexpected kind");
        }
    };

    let expr_ids = expr_ids
        .iter()
        .map(|e| {
            erased_ghost_value_remove_type_if_possible(
                cx,
                &erasure_ctxt,
                *e,
                hir_expr.hir_id,
                hir_expr.span,
            )
            .unwrap_or(*e)
        })
        .collect::<Vec<_>>();

    erased_ghost_value_kind_with_args(
        cx,
        &erasure_ctxt,
        hir_expr.hir_id,
        hir_expr.span,
        ty,
        expr_ids,
    )
}

/// We have to be careful to not emit any `erased_ghost_value::<T>(...)` expressions where `T`
/// is unsized. An example of where this matters is in something like `&*"abc"`.
/// Note here that:
///     "abc" is &str
///     *"abc" is str
///     &*"abc" is &str
/// The middle one is problematic. Luckily, whenever this happens, it will always be as
/// the intermediary in some expression like this. i.e., if *"abc" is getting erased,
/// then &*"abc" is getting erased too (or something like it).
/// Thus, we can resolve this issue by always erasing the type on any intermediary.
/// So, for example, if we are creating `erased_ghost_value::<T>()` where one of the arguments is
/// `erased_ghost_value::<S>()`, we replace the latter with `erased_ghost_value::<()>()`.
/// The type param only matters for the return value anyway, which doesn't matter in this
/// context.

fn erased_ghost_value_remove_type_if_possible<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    e: ExprId,
    hir_id: HirId,
    span: Span,
) -> Option<ExprId> {
    match &cx.thir.exprs[e].kind {
        ExprKind::Call { fun, args, .. } => match cx.thir.exprs[*fun].ty.kind() {
            TyKind::FnDef(fn_def_id, _)
                if *fn_def_id == erasure_ctxt.erased_ghost_value_fn_def_id =>
            {
                let tup_arg = args[0];
                let args = match &cx.thir.exprs[tup_arg].kind {
                    ExprKind::Tuple { fields } => fields.clone().into_vec(),
                    _ => {
                        panic!(
                            "erased_ghost_value should only be constructed with a tuple argument"
                        );
                    }
                };
                Some(erased_ghost_value_with_args(
                    cx,
                    erasure_ctxt,
                    hir_id,
                    span,
                    Ty::new_tup(cx.tcx, &[]),
                    args,
                ))
            }
            _ => None,
        },
        ExprKind::Scope { region_scope, lint_level, value } => {
            let region_scope = *region_scope;
            let lint_level = *lint_level;
            let value = *value;
            let value =
                erased_ghost_value_remove_type_if_possible(cx, erasure_ctxt, value, hir_id, span);
            match value {
                Some(v) => {
                    let mut expr = cx.thir.exprs[e].clone();
                    expr.kind = ExprKind::Scope { region_scope, lint_level, value: v };
                    expr.ty = cx.thir.exprs[v].ty;
                    Some(cx.thir.exprs.push(expr))
                }
                None => None,
            }
        }
        _ => None,
    }
}

/// Produce an expression `builtin::erased_ghost_value::<T>(())`
/// The hir_id is used for the scope so it needs to correspond to something that will
/// get a scope in the final THIR.
fn erased_ghost_value<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    ty: Ty<'tcx>,
) -> ExprId {
    let kind = erased_ghost_value_kind(cx, erasure_ctxt, hir_id, span, ty);
    expr_id_from_kind(cx, kind, hir_id, span, ty)
}

fn erased_ghost_value_kind<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    ty: Ty<'tcx>,
) -> ExprKind<'tcx> {
    erased_ghost_value_kind_with_args(cx, erasure_ctxt, hir_id, span, ty, vec![])
}

/// Produce an expression `builtin::erased_ghost_value::<T>((args...))`
/// The args are packaged as a tuple.
fn erased_ghost_value_with_args<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    ty: Ty<'tcx>,
    expr_args: Vec<ExprId>,
) -> ExprId {
    let kind = erased_ghost_value_kind_with_args(cx, erasure_ctxt, hir_id, span, ty, expr_args);
    expr_id_from_kind(cx, kind, hir_id, span, ty)
}

fn erased_ghost_value_kind_with_args<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    ty: Ty<'tcx>,
    expr_args: Vec<ExprId>,
) -> ExprKind<'tcx> {
    let tup_tys = expr_args.iter().map(|e| cx.thir.exprs[*e].ty).collect::<Vec<_>>();
    let tup_ty = Ty::new_tup(cx.tcx, &tup_tys);

    let arg1 = GenericArg::from(tup_ty);
    let arg2 = GenericArg::from(ty);
    let args = cx.tcx.mk_args(&[arg1, arg2]);
    let fn_def_id = erasure_ctxt.erased_ghost_value_fn_def_id;
    let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));

    let fun_expr_kind = ExprKind::ZstLiteral { user_ty: None };
    let fun_expr = expr_id_from_kind(cx, fun_expr_kind, hir_id, span, fn_ty);

    let arg_expr_kind = ExprKind::Tuple { fields: expr_args.into_boxed_slice() };
    let arg_expr = expr_id_from_kind(cx, arg_expr_kind, hir_id, span, tup_ty);

    ExprKind::Call {
        ty: fn_ty,
        fun: fun_expr,
        args: Box::new([arg_expr]),
        from_hir_call: false,
        fn_span: span,
    }
}

pub(crate) fn erase_body<'tcx>(cx: &mut ThirBuildCx<'tcx>, local_def_id: LocalDefId) -> bool {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return false;
    };
    matches!(erasure_ctxt.bodies.get(&local_def_id), Some(BodyErasure { erase_body: true, .. }))
}

pub(crate) fn erase_closure_body_for_closure_captures<'tcx>(local_def_id: LocalDefId) -> bool {
    let erasure_ctxt = get_verus_erasure_ctxt();
    matches!(erasure_ctxt.bodies.get(&local_def_id), Some(BodyErasure { erase_body: true, .. }))
}

pub(crate) fn erase_var_for_closure_captures<'tcx>(hir_id: HirId) -> bool {
    let erasure_ctxt = get_verus_erasure_ctxt();
    matches!(erasure_ctxt.vars.get(&hir_id), Some(VarErasure::Erase))
}

/// Remove all ghost-variable binders from the pattern
pub(crate) fn erase_pat<'tcx>(cx: &mut ThirBuildCx<'tcx>, pat: Box<Pat<'tcx>>) -> Box<Pat<'tcx>> {
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return pat;
    };

    let mut p = pat;
    erase_pat_rec(&PatBindingEraserMode::EraseGhost(erasure_ctxt), &mut p);
    p
}

/// Remove ALL binders from the pattern
pub(crate) fn erase_pat_all_binders<'tcx>(pat: Box<Pat<'tcx>>) -> Box<Pat<'tcx>> {
    let mut p = pat;
    erase_pat_rec(&PatBindingEraserMode::EraseAll, &mut p);
    p
}

enum PatBindingEraserMode {
    EraseAll,
    EraseGhost(Arc<VerusErasureCtxt>),
}

fn erase_pat_rec<'tcx>(emode: &PatBindingEraserMode, p: &mut Pat<'tcx>) {
    match &mut p.kind {
        PatKind::Missing => {}
        PatKind::Wild => {}
        PatKind::AscribeUserType { ascription: _, subpattern } => {
            erase_pat_rec(emode, subpattern);
        }
        PatKind::Binding {
            name: _,
            mode: _,
            var,
            ty: _,
            subpattern,
            is_primary: _,
            is_shorthand: _,
        } => {
            if let Some(subpat) = subpattern {
                erase_pat_rec(emode, subpat);
            }

            let erase_binder = match emode {
                PatBindingEraserMode::EraseAll => true,
                PatBindingEraserMode::EraseGhost(erasure_ctxt) => {
                    matches!(erasure_ctxt.vars.get(&var.0), Some(VarErasure::Erase))
                }
            };

            if erase_binder {
                // To remove the binder:
                //  - If there's a subpattern, just return the subpattern.
                //  - If there is no subpattern, return a wildcard.
                if subpattern.is_some() {
                    let mut subpat = None;
                    std::mem::swap(subpattern, &mut subpat);
                    let subpat = *subpat.unwrap();
                    *p = subpat;
                } else {
                    p.kind = PatKind::Wild;
                }
            }
        }
        PatKind::Variant { adt_def: _, args: _, variant_index: _, subpatterns }
        | PatKind::Leaf { subpatterns } => {
            for field_pat in subpatterns.iter_mut() {
                erase_pat_rec(emode, &mut field_pat.pattern);
            }
        }
        PatKind::Deref { subpattern } => {
            erase_pat_rec(emode, subpattern);
        }
        PatKind::DerefPattern { subpattern, borrow: _ } => {
            erase_pat_rec(emode, subpattern);
        }
        PatKind::Constant { value: _ } => {}
        PatKind::ExpandedConstant { def_id: _, subpattern } => {
            erase_pat_rec(emode, subpattern);
        }
        PatKind::Range(_pat_range) => {}
        PatKind::Slice { prefix, slice, suffix } | PatKind::Array { prefix, slice, suffix } => {
            for p in prefix.iter_mut() {
                erase_pat_rec(emode, p);
            }
            if let Some(sl) = slice {
                erase_pat_rec(emode, sl);
            }
            for p in suffix.iter_mut() {
                erase_pat_rec(emode, p);
            }
        }
        PatKind::Or { pats } => {
            for p in pats.iter_mut() {
                erase_pat_rec(emode, p);
            }
        }
        PatKind::Never => {}
        PatKind::Error(_error_guaranteed) => {}
    }
}

/// Get all nodes that need pattern checking (match expressions and let stmts)
fn get_all_stmts_with_pattern_checking<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    expr: &'tcx hir::Expr<'tcx>,
) -> Vec<ExprId> {
    let root_hir_id = expr.hir_id;
    let mut vis = VisitTreeForPats { cx, erasure_ctxt, root_hir_id, output_exprs: vec![] };
    use crate::rustc_hir::intravisit::Visitor;
    vis.visit_expr(expr);
    vis.output_exprs
}

struct VisitTreeForPats<'a, 'tcx> {
    cx: &'a mut ThirBuildCx<'tcx>,
    erasure_ctxt: &'a VerusErasureCtxt,
    root_hir_id: HirId,
    output_exprs: Vec<ExprId>,
}

impl<'a, 'tcx> rustc_hir::intravisit::Visitor<'tcx> for VisitTreeForPats<'a, 'tcx> {
    // Don't recurse into other items or closure bodies
    type NestedFilter = rustc_hir::intravisit::nested_filter::None;

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        match &expr.kind {
            hir::ExprKind::Match(..) => {
                self.output_exprs.push(erase_match_for_pattern_checking(
                    self.cx,
                    self.erasure_ctxt,
                    self.root_hir_id,
                    expr,
                ));
            }
            hir::ExprKind::Block(_block, _) => {
                if let Some(b) = erase_block_for_pattern_checking(
                    self.cx,
                    self.erasure_ctxt,
                    self.root_hir_id,
                    expr,
                ) {
                    self.output_exprs.push(b);
                }
            }
            _ => {}
        }

        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

fn erase_block_for_pattern_checking<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    root_hir_id: HirId,
    expr: &'tcx hir::Expr<'tcx>,
) -> Option<ExprId> {
    let hir::ExprKind::Block(block, _) = expr.kind else {
        unreachable!();
    };

    let mut stmts = vec![];
    for stmt in block.stmts.iter() {
        match &stmt.kind {
            hir::StmtKind::Let(..) => {
                stmts.push(erase_let_for_pattern_checking(
                    cx,
                    erasure_ctxt,
                    root_hir_id,
                    stmt,
                    block.hir_id.local_id,
                    stmts.len(),
                ));
            }
            _ => {}
        }
    }

    if stmts.len() == 0 {
        None
    } else {
        let block = Block {
            targeted_by_break: false,
            region_scope: region::Scope {
                local_id: block.hir_id.local_id,
                data: region::ScopeData::Node,
            },
            span: block.span,
            stmts: stmts.into_boxed_slice(),
            expr: None,
            safety_mode: BlockSafety::Safe,
        };
        let block = cx.thir.blocks.push(block);
        let kind = ExprKind::Block { block };
        Some(expr_id_from_kind(cx, kind, expr.hir_id, expr.span, Ty::new_tup(cx.tcx, &[])))
    }
}

fn erase_let_for_pattern_checking<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    root_hir_id: HirId,
    stmt: &'tcx hir::Stmt<'tcx>,
    block_id: hir::ItemLocalId,
    index: usize,
) -> StmtId {
    let hir::StmtKind::Let(local) = stmt.kind else {
        unreachable!();
    };
    let rustc_hir::LetStmt { super_: _, pat, ty: _, init, els, hir_id, span, source: _ } = local;
    if els.is_some() {
        panic!("erase_let_for_pattern_checking: let-else statement not expected in erased code");
    }

    let pattern = erase_pat_all_binders(crate::thir::pattern::pat_from_hir(
        cx.tcx,
        cx.typing_env,
        cx.typeck_results,
        pat,
    ));

    let init_ty = cx.typeck_results.node_type(pat.hir_id);
    let init =
        init.map(|init| erased_ghost_value(cx, erasure_ctxt, root_hir_id, init.span, init_ty));

    let remainder_scope = region::Scope {
        local_id: block_id,
        data: region::ScopeData::Remainder(region::FirstStatementIndex::new(index)),
    };
    let stmt = Stmt {
        kind: StmtKind::Let {
            remainder_scope,
            init_scope: region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node },
            pattern,
            initializer: init,
            else_block: None,
            lint_level: rustc_middle::thir::LintLevel::Explicit(local.hir_id),
            span: *span,
        },
    };
    cx.thir.stmts.push(stmt)
}

fn erase_match_for_pattern_checking<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    root_hir_id: HirId,
    expr: &'tcx hir::Expr<'tcx>,
) -> ExprId {
    let hir::ExprKind::Match(discr, arms, match_source) = expr.kind else {
        unreachable!();
    };

    let scrutinee_ty = cx.typeck_results.expr_ty_adjusted(discr);
    let match_ty = cx.typeck_results.expr_ty(expr);

    let scrutinee = erased_ghost_value(cx, erasure_ctxt, root_hir_id, discr.span, scrutinee_ty);

    let kind = ExprKind::Match {
        scrutinee,
        arms: arms
            .iter()
            .map(|a| erase_arm_for_pattern_checking(cx, erasure_ctxt, root_hir_id, a, match_ty))
            .collect(),
        match_source,
    };
    expr_id_from_kind(cx, kind, expr.hir_id, expr.span, match_ty)
}

fn erase_arm_for_pattern_checking<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    root_hir_id: HirId,
    arm: &'tcx hir::Arm<'tcx>,
    match_ty: Ty<'tcx>,
) -> ArmId {
    let pattern = erase_pat_all_binders(crate::thir::pattern::pat_from_hir(
        cx.tcx,
        cx.typing_env,
        cx.typeck_results,
        &arm.pat,
    ));
    let guard = arm.guard.map(|guard| {
        let bool_ty = cx.tcx.mk_ty_from_kind(TyKind::Bool);
        erased_ghost_value(cx, erasure_ctxt, root_hir_id, guard.span, bool_ty)
    });

    let body = erased_ghost_value(cx, erasure_ctxt, root_hir_id, arm.body.span, match_ty);

    let arm = Arm {
        pattern,
        guard,
        body,
        lint_level: rustc_middle::thir::LintLevel::Explicit(arm.hir_id),
        scope: region::Scope { local_id: arm.hir_id.local_id, data: region::ScopeData::Node },
        span: arm.span,
    };
    cx.thir.arms.push(arm)
}

/*////// Closures

Welcome to closure handling.

The tricky thing about closures is that erasure might change the *capture set* for the closure.
For example, if we have:

|| {
    proof { assert(foo(x)); }
    let y = &x.a;
}

then Rust would ordinarily infer a capture set of { MOVE x }. Whereas what we actually want,
i.e., post-erasure, is the capture set of { REF x.a }.

To make matters worse, Rust computes the capture set *during type checking*
(i.e., in rustc_hir_typeck). This is because the capture set influences the types:
the types of captured variables all go into the closure type, which then influences
marker traits, FnOnce/FnMut/Fn, etc.

See:

 - https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/ty/struct.ClosureArgs.html

Now, we're going to just leave the types as-is since changing them at this point is basically
impossible. That means if Rust decides the closure needs to capture a variable which is !Sync,
and then Verus decides it doesn't really need to be captured, then ... oh well.

However, we still want to make sure variables used in ghost code don't affect *lifetime checking*.
So we need to do two things:

 1. Compute the "post-erasure" capture set. (We'll call this the "Verus capture set" in contrast
    to the "Rust capture set"

 2. Generate well-formed THIR/MIR that uses the Verus capture set instead of the Rust capture set.

Both of these things are somewhat nontrivial.
*/

// Step 1: Get the Verus capture set
pub(crate) fn get_closure_captures_accounting_for_ghost<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    closure_expr: &'tcx hir::Expr<'tcx>,
    closure_def_id: LocalDefId,
) -> (
    &'tcx rustc_middle::ty::List<&'tcx CapturedPlace<'tcx>>,
    Vec<Ty<'tcx>>,
    Vec<(rustc_middle::hir::place::Place<'tcx>, rustc_middle::mir::FakeReadCause, HirId)>,
) {
    let tcx = cx.tcx;
    let capture_results = crate::upvar::compute_captures_accounting_for_ghost(
        tcx,
        cx.typing_env.param_env,
        closure_expr,
        closure_def_id,
        cx.typeck_results,
    );

    let closure_min_captures = capture_results.closure_min_captures;
    let closure_min_captures = Box::leak(Box::new(closure_min_captures));
    let closure_min_captures = closure_min_captures.values().flat_map(|v| v.iter());

    let captures = tcx.mk_captures_from_iter(closure_min_captures);

    (captures, capture_results.upvar_tys, capture_results.fake_reads)
}

/*
Generating the THIR using the Verus capture set:

Normally what happens, is that we pass the captures as arguments to the closure expression.
e.g., if the closure captures x.a by reference, then we'd pass &x.a as an argument.
We're in the situation where the closure expression expects certain arguments (determined
by its type, which is pre-determined by the Rust capture set), but the arguments we *want*
to pass in are determined by the Verus capture set.

We only want to lifetime-check this code, not run it, which simplifies our work greatly.
This allows us to create nonsense conversions that aren't implementable as long as they have
the right type signature.

However, it's important that this coercion propagates lifetime variables correctly.
So for example if the Rust capture set is { t: T<'a> }
and the Verus capture set is { t: T<'a> }, we need to make
sure these are actually hooked up to each other, and that we aren't just coercing from
T<'a> to T<'b> for some other lifetime <'b>.

This gets more complicated when we consider projections. Maybe Rust captures { t: T<'a> } while
Verus captures something more precise, { t.a: S<'a> }. This isn't difficult to handle because
we can substitute args to compute the type of the projections.

Now, the gist of what we're going to do is:
 - Make a fake function with a synthesized type signature which
   is quantified over some lifetime variables
 - Pass all the Verus-captures as input to the function
 - Take the output of that function call and pass it to the closure.

Again, we don't need to implement the function, we just need the desired signature and
then we can conjure the function out of nowhere.

There are a few annoying corner cases. The main one is when the Verus capture set contains a reference
that the Rust capture doesn't contain. For example:

|| {
    proof { assert(foo(x)); }
    let y = &x;
}

Rust capture set: { MOVE x }
Verus capture set: { REF x }

Thus, we need to coerce &x of type &T to type T. The problem is that &x has a lifetime variable
(&'a x) that has nowhere to go. To resolve this, we make sure every closure always captures
at least one variable with a lifetime parameter. We call this the "dummy capture". Specifically,
the syntax macro encodes the closure like this:

```
{
    let _verus_internal_dummy_capture = ::builtin::dummy_capture_new();
    || {
        ::builtin::dummy_capture_consume(_verus_internal_dummy_capture);
        // ...
    }
}
```

The _verus_internal_dummy_capture has type DummyCapture<'a>. Thus, we can always map the
lifetime variable of the reference to some lifetime parameter that the closure is bounded by,
which then makes sure the reference does actually outlive the closure.

So if we take this example again:

```
{
    let _verus_internal_dummy_capture = ::builtin::dummy_capture_new();
    || {
        ::builtin::dummy_capture_consume(_verus_internal_dummy_capture);
        proof { assert(foo(x)); }
        let y = &x;
    }
}
```

The Rust capture set will be [ MOVE _verus_internal_dummy_capture, MOVE x ] while
the Verus capture set will be [ REF x ]. If x has type T<'b>, then we're going to synthesize
a coercion function:

MAGIC_COERCION: for<'a, 'b> (&'a T<'b>) -> (DummyCapture<'a>, T<'b>)

It may seem a little dodgy that we lose the implict ('b: 'a) bound as a result of splitting up the
&'a T<'b> type. However, this is actually fine, since there is no way to "destruct" the closure
or access its innards except from within, and this requires all its type variables to be live
(i.e., both 'a and 'b').

Now, the resulting THIR looks like this:

```
{
    let _tmp = MAGIC_COERCION(&x);
    CLOSURE(_tmp.0, _tmp.1)
}
```

(We reuse the _verus_internal_dummy_capture local ID in the _tmp variable for convenience,
but of course this variable is going to have a different type than the original source.)
*/

type ClosureOverrides = (Box<[ExprId]>, Vec<(ExprId, FakeReadCause, HirId)>);

pub(crate) fn set_override_closure_kind<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    local_def_id: LocalDefId,
    overrides: ClosureOverrides,
) {
    cx.verus_ctxt.closure_overrides.insert(local_def_id, overrides);
}

pub(crate) fn get_override_closure_kind<'tcx>(
    cx: &ThirBuildCx<'tcx>,
    local_def_id: LocalDefId,
) -> Option<ClosureOverrides> {
    cx.verus_ctxt.closure_overrides.get(&local_def_id).cloned()
}

// Utility to replace Region::ReErased with bound regions

struct ReErasedReplacer<'tcx> {
    tcx: TyCtxt<'tcx>,
    current_index: rustc_middle::ty::DebruijnIndex,
    current_var: usize,
}

impl<'tcx> ReErasedReplacer<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        ReErasedReplacer { tcx, current_index: rustc_middle::ty::INNERMOST, current_var: 0 }
    }
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for ReErasedReplacer<'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T: TypeFoldable<TyCtxt<'tcx>>>(
        &mut self,
        t: rustc_middle::ty::Binder<'tcx, T>,
    ) -> rustc_middle::ty::Binder<'tcx, T> {
        self.current_index.shift_in(1);
        let t = t.super_fold_with(self);
        self.current_index.shift_out(1);
        t
    }

    fn fold_region(&mut self, r: rustc_middle::ty::Region<'tcx>) -> rustc_middle::ty::Region<'tcx> {
        match r.kind() {
            rustc_middle::ty::ReErased => {
                let var = self.current_var;
                self.current_var += 1;

                rustc_middle::ty::Region::new_bound(
                    self.tcx,
                    self.current_index,
                    BoundRegion { var: BoundVar::from_usize(var), kind: BoundRegionKind::Anon },
                )
            }
            rustc_middle::ty::ReBound(BoundVarIndexKind::Bound(debruijn), _br) => {
                assert!(debruijn < self.current_index);
                r
            }
            _ => r,
        }
    }
}

enum VerusCaptureKind<'tcx> {
    DummyCapture,
    ArgToMagicFn,
    FakeRead((Place<'tcx>, FakeReadCause, HirId)),
}

/// Create the type signature of the 'magic coercion function' described above
fn mk_closure_magic_coercion_fn<'tcx, 'a>(
    tcx: TyCtxt<'tcx>,
    rust_captured_places: &[&CapturedPlace<'tcx>],
    verus_captured_places: &[&CapturedPlace<'tcx>],
    rust_fake_reads: &Vec<(Place<'tcx>, FakeReadCause, HirId)>,
    expected_tys: &[Ty<'tcx>],
    upvar_dc_idx: usize,
    ty_dc_idx: usize,
) -> (Ty<'tcx>, Vec<VerusCaptureKind<'tcx>>) {
    // The general form of the type signature is going to be
    // for<'a, 'b, ...> fn(A, B, ...) -> (X, Y, ...)
    // where the inputs corresponds to Verus captures (minus the DummyCapture)
    // and the outputs correspond to Rust captures

    // Go through the types of each Rust capture and replace free region variables
    // with bound variables.
    let mut replacer = ReErasedReplacer::new(tcx);
    let mut output_tys = vec![];
    for ty in expected_tys.iter() {
        let t = ty.fold_with(&mut replacer);
        output_tys.push(t);
    }

    // As explained above, we may need to use the lifetime variable of the dummy capture argument
    let dc_default_region = match output_tys[ty_dc_idx].kind() {
        TyKind::Ref(region, _, _) => *region,
        TyKind::Adt(_, args) => args[0].as_region().unwrap(),
        _ => panic!("ty_dc_idx should have given DummyCapture type"),
    };

    let mut input_tys = vec![];
    let mut kinds = vec![];
    for (i, verus_captured_place) in verus_captured_places.iter().enumerate() {
        if i == upvar_dc_idx {
            kinds.push(VerusCaptureKind::DummyCapture);
            continue;
        }

        // For each input, find the corresponding output, which should be some ancestor.
        // E.g., if the input is `x.a.b.c`, the corresponding output might be `x.a`.
        //
        // Since Verus captures can only be more precise than Rust captures, the corresponding
        // Rust capture should always exist UNLESS it was a fake read in the Rust capture set.

        let idx_opt = rust_captured_places.iter().position(|rust_captured_place| {
            is_ancestor(&rust_captured_place.place, &verus_captured_place.place)
        });
        if let Some(idx) = idx_opt {
            // Case: we found the ancestor in the capture set

            let output_ty = output_tys[idx];
            let rust_captured_place = &rust_captured_places[idx];

            // Now apply the projections to get the input type.

            let output_uses_ref = match rust_captured_place.info.capture_kind {
                UpvarCapture::ByRef(_borrow_kind) => true,
                _ => false,
            };
            let (output_ty_no_ref, region_opt) = if output_uses_ref {
                match output_ty.kind() {
                    TyKind::Ref(r, t, _mutability) => (*t, Some(*r)),
                    _ => panic!("Expected type to be a reference"),
                }
            } else {
                (output_ty, None)
            };

            let mut input_ty = output_ty_no_ref;
            for proj in verus_captured_place.place.projections
                [rust_captured_place.place.projections.len()..]
                .iter()
            {
                input_ty = apply_projection(tcx, proj, input_ty);
            }

            let input_ty = match &verus_captured_place.info.capture_kind {
                UpvarCapture::ByValue | UpvarCapture::ByUse => input_ty,
                UpvarCapture::ByRef(kind) => {
                    let region = match region_opt {
                        Some(r) => r,
                        None => dc_default_region,
                    };
                    Ty::new_ref(tcx, region, input_ty, kind.to_mutbl_lossy())
                }
            };

            kinds.push(VerusCaptureKind::ArgToMagicFn);
            input_tys.push(input_ty);
        } else {
            // Case: we didn't find any ancestor in the capture set.
            // In this case there should be a fake read from the Rust capture set.

            // Check this assumption:
            let found_fake_read = rust_fake_reads
                .iter()
                .position(|(place, _, _)| is_ancestor(place, &verus_captured_place.place));
            if found_fake_read.is_none() {
                panic!(
                    "Verus captured place doesn't correspond to Rust captured place or fake read"
                );
            }
            let idx = found_fake_read.unwrap();
            let (_, cause, hir_id) = rust_fake_reads[idx];

            kinds.push(VerusCaptureKind::FakeRead((
                verus_captured_place.place.clone(),
                cause,
                hir_id,
            )));
        }
    }

    // Wrap it all up into a FnPtr type

    let output_ty = Ty::new_tup(tcx, &output_tys);
    let inputs_and_output =
        tcx.mk_type_list_from_iter(input_tys.iter().cloned().chain(std::iter::once(output_ty)));

    let mut bound_var_kinds = vec![];
    for _i in 0..replacer.current_var {
        bound_var_kinds.push(BoundVariableKind::Region(BoundRegionKind::Anon));
    }
    let bound_var_kinds = tcx.mk_bound_variable_kinds(&bound_var_kinds);

    let fnty = tcx.mk_ty_from_kind(TyKind::FnPtr(
        Binder::bind_with_vars(rustc_middle::ty::FnSigTys { inputs_and_output }, bound_var_kinds),
        rustc_middle::ty::FnHeader {
            c_variadic: false,
            safety: rustc_hir::Safety::Safe,
            abi: rustc_abi::ExternAbi::Rust,
        },
    ));

    (fnty, kinds)
}

pub(crate) fn apply_projection<'tcx>(
    tcx: TyCtxt<'tcx>,
    projection: &Projection<'tcx>,
    ty: Ty<'tcx>,
) -> Ty<'tcx> {
    match &projection.kind {
        ProjectionKind::Deref => match ty.kind() {
            TyKind::Ref(_, ty, _) => *ty,
            TyKind::Adt(adt, args) if Some(adt.did()) == tcx.lang_items().owned_box() => {
                args[0].as_type().unwrap()
            }
            _ => {
                panic!("apply_projection: unexpected type");
            }
        },
        ProjectionKind::Field(field_idx, variant_idx) => match ty.kind() {
            TyKind::Tuple(tys) => tys[field_idx.as_usize()],
            TyKind::Adt(adt, args) => adt.variant(*variant_idx).fields[*field_idx].ty(tcx, args),
            _ => {
                panic!("apply_projection: unexpected type");
            }
        },
        _ => {
            panic!("apply_projection: unexpected projection");
        }
    }
}

pub(crate) fn is_ancestor<'tcx>(p1: &Place<'tcx>, p2: &Place<'tcx>) -> bool {
    let Place { base_ty: _, base: b1, projections: proj1 } = p1;
    let Place { base_ty: _, base: b2, projections: proj2 } = p2;
    b1 == b2 && proj1.len() <= proj2.len() && proj1[..] == proj2[..proj1.len()]
}

pub(crate) fn possibly_handle_complex_closure_block<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    block: &'tcx hir::Block<'tcx>,
) -> Option<BlockId> {
    // Check if this block has the form
    // { let _verus_internal_dummy_capture = ::builtin::dummy_capture_new(); || { ... } }

    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return None;
    };

    if !(block.stmts.len() == 1 && block.expr.is_some()) {
        return None;
    }
    let rustc_hir::StmtKind::Let(let_stmt) = &block.stmts[0].kind else {
        return None;
    };
    let Some(let_stmt_init) = &let_stmt.init else {
        return None;
    };

    let let_ty = cx.typeck_results.expr_ty(let_stmt_init);
    if !ty_is_dummy_capture(&erasure_ctxt, let_ty) {
        return None;
    }

    let expr = get_closure_expr(&block.expr.unwrap());
    let rustc_hir::ExprKind::Closure(_closure) = &expr.kind else {
        return None;
    };

    let tcx = cx.tcx;

    let closure_ty = cx.typeck_results.expr_ty(expr);
    let (def_id, args, _movability) = match *closure_ty.kind() {
        ty::Closure(def_id, args) => (def_id, UpvarArgs::Closure(args), None),
        ty::Coroutine(def_id, args) => {
            (def_id, UpvarArgs::Coroutine(args), Some(tcx.coroutine_movability(def_id)))
        }
        ty::CoroutineClosure(def_id, args) => (def_id, UpvarArgs::CoroutineClosure(args), None),
        _ => {
            panic!("closure expr w/o closure type: {:?}", closure_ty);
        }
    };
    let def_id = def_id.expect_local();

    // generate the coercion

    let rust_closure_captures = cx.tcx.closure_captures(def_id);
    let emp = vec![];
    let rust_fake_reads = cx.typeck_results.closure_fake_reads.get(&def_id).unwrap_or(&emp);
    let rust_upvar_tys = args.upvar_tys();

    let (verus_closure_captures, verus_upvar_tys, verus_fake_reads) =
        crate::verus::get_closure_captures_accounting_for_ghost(cx, expr, def_id);
    assert!(verus_fake_reads.len() == 0);

    let verus_upvars = verus_closure_captures
        .iter()
        .zip_eq(verus_upvar_tys.iter())
        .map(|(captured_place, ty)| {
            let upvars = cx.capture_upvar(expr, captured_place, *ty);
            cx.thir.exprs.push(upvars)
        })
        .collect::<Vec<_>>();

    let upvar_dc_idx = get_upvar_dummy_capture_idx(cx, &erasure_ctxt, &verus_upvars);
    let ty_dc_idx = get_ty_dummy_capture_idx(&erasure_ctxt, rust_upvar_tys);

    let (coercion_fn_ty, verus_capture_kinds) = mk_closure_magic_coercion_fn(
        cx.tcx,
        rust_closure_captures,
        verus_closure_captures,
        rust_fake_reads,
        &rust_upvar_tys,
        upvar_dc_idx,
        ty_dc_idx,
    );

    let mut magic_fn_args = vec![];
    let mut verus_fake_reads_final = vec![];
    for (i, k) in verus_capture_kinds.iter().enumerate() {
        match k {
            VerusCaptureKind::DummyCapture => {}
            VerusCaptureKind::ArgToMagicFn => {
                magic_fn_args.push(verus_upvars[i]);
            }
            VerusCaptureKind::FakeRead((place, cause, hir_id)) => {
                let expr = cx.convert_captured_hir_place(expr, place.clone());
                let fake_read = (cx.thir.exprs.push(expr), *cause, *hir_id);
                verus_fake_reads_final.push(fake_read);
            }
        }
    }

    let rust_upvar_tys_tuple = Ty::new_tup(tcx, &rust_upvar_tys);
    let call_result = make_fake_call(
        cx,
        &erasure_ctxt,
        expr.hir_id,
        expr.span,
        coercion_fn_ty,
        magic_fn_args,
        rust_upvar_tys_tuple,
    );
    let (dc_id, stmt) = make_let(cx, &block.stmts[0], block.hir_id.local_id, call_result);

    let mut forged_upvars = vec![];
    for i in 0..rust_upvar_tys.len() {
        forged_upvars.push(make_dc_tuple_index(
            cx,
            expr.span,
            expr.hir_id,
            rust_upvar_tys_tuple,
            rust_upvar_tys[i],
            dc_id,
            i,
        ));
    }

    // Store the computed ClosureKind in a map, then recurse.
    // The walk will pick up the new ClosureKind when we get there
    set_override_closure_kind(
        cx,
        def_id,
        (forged_upvars.into_boxed_slice(), verus_fake_reads_final),
    );
    cx.verus_ctxt.prep_expr(block.expr.unwrap(), false);
    let expr = cx.mirror_expr(block.expr.unwrap());

    let block = Block {
        targeted_by_break: false,
        region_scope: region::Scope {
            local_id: block.hir_id.local_id,
            data: region::ScopeData::Node,
        },
        span: block.span,
        stmts: vec![stmt].into_boxed_slice(),
        expr: Some(expr),
        safety_mode: BlockSafety::Safe,
    };

    Some(cx.thir.blocks.push(block))
}

pub(crate) fn get_closure_expr<'tcx>(e: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
    match &e.kind {
        hir::ExprKind::Closure(_) => e,
        hir::ExprKind::Call(_f, args) => get_closure_expr(&args[0]),
        _ => panic!("get_closure_expr failed"),
    }
}

// Generate a fake function call by using 'erased_ghost_value' to create the *function*
// then call the function.
pub(crate) fn make_fake_call<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    fn_ty: Ty<'tcx>,
    args: Vec<ExprId>,
    result_ty: Ty<'tcx>,
) -> ExprId {
    let f = erased_ghost_value(cx, erasure_ctxt, hir_id, span, fn_ty);

    let kind = ExprKind::Call {
        ty: fn_ty,
        fun: f,
        args: args.into_boxed_slice(),
        from_hir_call: false,
        fn_span: span,
    };
    expr_id_from_kind(cx, kind, hir_id, span, result_ty)
}

pub(crate) fn make_let<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    stmt: &rustc_hir::Stmt,
    block_id: hir::ItemLocalId,
    e: ExprId,
) -> (LocalVarId, StmtId) {
    let hir::StmtKind::Let(let_stmt) = &stmt.kind else {
        panic!("expected Let");
    };
    let ident = match &let_stmt.pat.kind {
        hir::PatKind::Binding(_, _, ident, _) => ident,
        _ => panic!("expected Binding"),
    };

    let ty = cx.thir.exprs[e].ty;
    let var = LocalVarId(let_stmt.pat.hir_id);
    let pattern = Box::new(Pat {
        ty: ty,
        span: stmt.span,
        kind: PatKind::Binding {
            name: ident.name,
            mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, Mutability::Not),
            var,
            ty,
            subpattern: None,
            is_primary: true,
            is_shorthand: false,
        },
    });

    let remainder_scope = region::Scope {
        local_id: block_id,
        data: region::ScopeData::Remainder(region::FirstStatementIndex::new(0)),
    };
    let stmt = Stmt {
        kind: StmtKind::Let {
            remainder_scope,
            init_scope: region::Scope {
                local_id: stmt.hir_id.local_id,
                data: region::ScopeData::Node,
            },
            pattern,
            initializer: Some(e),
            else_block: None,
            lint_level: thir::LintLevel::Explicit(let_stmt.hir_id),
            span: stmt.span,
        },
    };
    let stmt = cx.thir.stmts.push(stmt);
    (var, stmt)
}

pub(crate) fn make_dc_tuple_index<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    span: Span,
    hir_id: HirId,
    tup_ty: Ty<'tcx>,
    my_ty: Ty<'tcx>,
    id: LocalVarId,
    idx: usize,
) -> ExprId {
    let kind = ExprKind::VarRef { id };
    let e = expr_id_from_kind(cx, kind, hir_id, span, tup_ty);

    let kind = ExprKind::Field {
        lhs: e,
        variant_index: rustc_abi::VariantIdx::from_usize(0),
        name: rustc_abi::FieldIdx::from_usize(idx),
    };
    expr_id_from_kind(cx, kind, hir_id, span, my_ty)
}

fn ty_is_dummy_capture<'tcx>(erasure_ctxt: &VerusErasureCtxt, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => {
            if adt_def.did() == erasure_ctxt.dummy_capture_struct_def_id {
                return true;
            }
        }
        _ => {}
    }
    false
}

fn ty_is_dummy_capture_or_ref<'tcx>(erasure_ctxt: &VerusErasureCtxt, ty: Ty<'tcx>) -> bool {
    let ty = match ty.kind() {
        TyKind::Ref(_region, ty, _mutability) => *ty,
        _ => ty,
    };
    ty_is_dummy_capture(erasure_ctxt, ty)
}

fn get_upvar_dummy_capture_idx<'tcx>(
    cx: &ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    upvars: &Vec<ExprId>,
) -> usize {
    for i in 0..upvars.len() {
        let ty = cx.thir.exprs[upvars[i]].ty;
        if ty_is_dummy_capture_or_ref(erasure_ctxt, ty) {
            return i;
        }
    }
    panic!("MISSING DummyCapture (upvar)");
}

fn get_ty_dummy_capture_idx<'tcx>(erasure_ctxt: &VerusErasureCtxt, tys: &'tcx [Ty<'tcx>]) -> usize {
    for i in 0..tys.len() {
        let ty = tys[i];
        if ty_is_dummy_capture_or_ref(erasure_ctxt, ty) {
            return i;
        }
    }
    panic!("MISSING DummyCapture (ty)");
}
