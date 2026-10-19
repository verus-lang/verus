/*! Verus: const evaluation uses MIR built in "full erasure" mode.

Verus keeps ghost code (spec and proof code) in the Rust source that rustc type-checks.
Since rustc may need to evaluate consts (and const fns) during type-checking, the MIR
that the const evaluator runs must have all ghost code erased. This is done by the
"full erasure" mode of the rustc_mir_build fork (see `FullErasureCtxt` there).

Meanwhile, the query system (`mir_built`, `mir_for_ctfe`, `promoted_mir`, etc.) continues to
return MIR built with Verus's normal erasure, which is used for lifetime checking.
Therefore, instead of calling `tcx.mir_for_ctfe` and `tcx.promoted_mir`, the const evaluator
calls the functions here, which build the MIR manually (without the query system)
and then run the passes that rustc would run to produce `mir_for_ctfe` and `promoted_mir`.
*/

use std::collections::HashMap;
use std::sync::Mutex;

use rustc_hir as hir;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::mir::{
    AnalysisPhase, Body, CallSource, ConstOperand, ConstValue, LocalDecl, MirPhase, Operand, Place,
    ProjectionElem, Promoted, Rvalue, SourceInfo, Statement, StatementKind, TerminatorKind,
    WithRetag,
};
use rustc_middle::ty::{self, GlobalCtxt, Ty, TyCtxt};
use rustc_span::{DUMMY_SP, Spanned, sym};

use crate::ctfe_limit::CtfeLimit;
use crate::promote_consts::PromoteTemps;
use crate::required_consts::RequiredConstsVisitor;

/// Minimal version of the `MirPass` trait from rustc_mir_transform,
/// needed by the files we copy from rustc_mir_transform.
pub(crate) trait MirPass<'tcx> {
    #[allow(dead_code)]
    fn policy(&self, sess: &rustc_session::Session) -> PassPolicy;

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>);
}

/// Copied from rustc_mir_transform, needed by the files we copy from rustc_mir_transform.
#[allow(dead_code)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum PassPolicy {
    Required,
    Optional { generally_enabled: bool, optimization: bool },
}

impl PassPolicy {
    pub(crate) fn optional_non_optimization(condition: bool) -> Self {
        Self::Optional { generally_enabled: condition, optimization: false }
    }
}

/// Returns the LocalDefId if we should use full-erasure MIR for the given item.
fn full_erasure_def_id<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<LocalDefId> {
    let local_def_id = def_id.as_local()?;
    rustc_mir_build_verus::verus::get_full_erasure_ctxt()?;
    if tcx.is_constructor(def_id) {
        return None;
    }
    tcx.hir_body_const_context(local_def_id)?;
    Some(local_def_id)
}

/// Replacement for `tcx.mir_for_ctfe(def_id)`
pub(crate) fn mir_for_ctfe<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx Body<'tcx> {
    match full_erasure_def_id(tcx, def_id) {
        Some(local_def_id) => {
            if let Some(entry) = cache_lookup(tcx, local_def_id)
                && let Some(body) = entry.body
            {
                return body;
            }
            build_mir_for_ctfe(tcx, local_def_id).0
        }
        None => tcx.mir_for_ctfe(def_id),
    }
}

/// Replacement for `tcx.promoted_mir(def_id)`
pub(crate) fn promoted_mir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> &'tcx IndexVec<Promoted, Body<'tcx>> {
    match full_erasure_def_id(tcx, def_id) {
        Some(local_def_id) => {
            if let Some(entry) = cache_lookup(tcx, local_def_id) {
                return entry.promoted;
            }
            build_mir_for_ctfe(tcx, local_def_id).1
        }
        None => tcx.promoted_mir(def_id),
    }
}

/// Replacement for `tcx.trivial_const(def_id)`
/// (The `trivial_const` query is computed from `mir_built`, which we need to avoid.)
pub(crate) fn trivial_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Option<(ConstValue, Ty<'tcx>)> {
    match full_erasure_def_id(tcx, def_id) {
        Some(_) => None,
        None => tcx.trivial_const(def_id),
    }
}

/// Arena-allocated MIR for an item.
/// The promoted bodies are finished (and cached) before the main body, because the passes
/// on the main body (specifically, the KnownPanicsLint) may evaluate the promoteds.
struct CacheEntry<'tcx> {
    promoted: &'tcx IndexVec<Promoted, Body<'tcx>>,
    body: Option<&'tcx Body<'tcx>>,
}

/// Cache of CacheEntry for each item, with the pointers stored as usize.
/// Since the pointers are only valid for a given GlobalCtxt, we also record the address
/// of the GlobalCtxt, and we reset the cache if the GlobalCtxt changes.
static FULL_ERASURE_MIR_CACHE: Mutex<Option<(usize, HashMap<LocalDefId, (usize, Option<usize>)>)>> =
    Mutex::new(None);

fn gcx_id<'tcx>(tcx: TyCtxt<'tcx>) -> usize {
    let gcx: &GlobalCtxt<'tcx> = *tcx;
    gcx as *const GlobalCtxt<'tcx> as usize
}

fn entry_from_ptrs<'tcx>((promoted, body): (usize, Option<usize>)) -> CacheEntry<'tcx> {
    // SAFETY: these pointers were allocated in the arena of the GlobalCtxt
    // whose address is recorded in the cache, so they live as long as 'tcx.
    unsafe {
        CacheEntry {
            promoted: &*(promoted as *const IndexVec<Promoted, Body<'tcx>>),
            body: body.map(|body| &*(body as *const Body<'tcx>)),
        }
    }
}

fn cache_lookup<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Option<CacheEntry<'tcx>> {
    let gcx_id = gcx_id(tcx);
    let cache = FULL_ERASURE_MIR_CACHE.lock().unwrap();
    match &*cache {
        Some((id, map)) if *id == gcx_id => map.get(&def).map(|ptrs| entry_from_ptrs(*ptrs)),
        _ => None,
    }
}

/// Insert into the cache. If some other thread got there first, use its result,
/// so that all callers see the same bodies.
fn cache_insert<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    promoted: &'tcx IndexVec<Promoted, Body<'tcx>>,
    body: Option<&'tcx Body<'tcx>>,
) -> CacheEntry<'tcx> {
    let gcx_id = gcx_id(tcx);
    let mut cache = FULL_ERASURE_MIR_CACHE.lock().unwrap();
    if !matches!(&*cache, Some((id, _)) if *id == gcx_id) {
        *cache = Some((gcx_id, HashMap::new()));
    }
    let (_, map) = cache.as_mut().unwrap();
    let promoted_ptr = promoted as *const IndexVec<Promoted, Body<'tcx>> as usize;
    let body_ptr = body.map(|body| body as *const Body<'tcx> as usize);
    let ptrs = map.entry(def).or_insert((promoted_ptr, None));
    if ptrs.1.is_none() {
        ptrs.1 = body_ptr;
    }
    entry_from_ptrs(*ptrs)
}

/// Build the full-erasure MIR, then follow the steps of the following queries in
/// rustc_mir_transform: `mir_built`, `mir_promoted`, `promoted_mir`,
/// `mir_drops_elaborated_and_const_checked`, and `mir_for_ctfe`.
/// We skip lints and checks (which are handled by the normal compilation pipeline).
/// Don't hold the cache lock while building, since building may recursively
/// evaluate other consts.
fn build_mir_for_ctfe<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> (&'tcx Body<'tcx>, &'tcx IndexVec<Promoted, Body<'tcx>>) {
    let mut body = rustc_mir_build_verus::builder::verus_builder::build_mir_full_erasure(tcx, def);

    // mir_promoted
    RequiredConstsVisitor::compute_required_consts(&mut body);
    let promote_pass = PromoteTemps::default();
    promote_pass.run_pass(tcx, &mut body);
    body.phase = MirPhase::Analysis(AnalysisPhase::Initial);
    let mut promoted = promote_pass.promoted_fragments.into_inner();

    // promoted_mir
    for body in &mut promoted {
        rustc_mir_transform::run_analysis_to_runtime_passes(tcx, body);
    }
    let promoted = cache_insert(tcx, def, tcx.arena.alloc(promoted), None).promoted;

    // mir_drops_elaborated_and_const_checked
    rustc_mir_transform::run_analysis_to_runtime_passes(tcx, &mut body);

    // mir_for_ctfe
    let always = matches!(
        tcx.hir_body_const_context(def),
        Some(hir::ConstContext::Const { .. } | hir::ConstContext::Static(_))
    );
    let mut body = remap_mir_for_const_eval_select(tcx, body, hir::Constness::Const { always });
    CtfeLimit.run_pass(tcx, &mut body);

    let entry = cache_insert(tcx, def, promoted, Some(tcx.arena.alloc(body)));
    (entry.body.unwrap(), entry.promoted)
}

// Copied from rustc_mir_transform/src/lib.rs
fn remap_mir_for_const_eval_select<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut body: Body<'tcx>,
    context: hir::Constness,
) -> Body<'tcx> {
    for bb in body.basic_blocks.as_mut().iter_mut() {
        let terminator = bb.terminator.as_mut().expect("invalid terminator");
        match terminator.kind {
            TerminatorKind::Call {
                func: Operand::Constant(ConstOperand { ref const_, .. }),
                ref mut args,
                destination,
                target,
                unwind,
                fn_span,
                ..
            } if let ty::FnDef(def_id, _) = *const_.ty().kind()
                && tcx.is_intrinsic(def_id, sym::const_eval_select) =>
            {
                let Ok([tupled_args, called_in_const, called_at_rt]) = take_array(args) else {
                    unreachable!()
                };
                let ty = tupled_args.node.ty(&body.local_decls, tcx);
                let fields = ty.tuple_fields();
                let num_args = fields.len();
                let func = match context {
                    // Using `const_eval_select` in always-const code is useful when used in macros
                    // that you don't know whether they are going to be used in `const fn` or in `const` items.
                    hir::Constness::Const { .. } => called_in_const,
                    hir::Constness::NotConst => called_at_rt,
                };
                let (method, place): (fn(Place<'tcx>) -> Operand<'tcx>, Place<'tcx>) =
                    match tupled_args.node {
                        Operand::Constant(_) | Operand::RuntimeChecks(_) => {
                            // There is no good way of extracting a tuple arg from a constant
                            // (const generic stuff) so we just create a temporary and deconstruct
                            // that.
                            let local = body.local_decls.push(LocalDecl::new(ty, fn_span));
                            bb.statements.push(Statement::new(
                                SourceInfo::outermost(fn_span),
                                StatementKind::Assign(Box::new((
                                    local.into(),
                                    Rvalue::Use(tupled_args.node.clone(), WithRetag::Yes),
                                ))),
                            ));
                            (Operand::Move, local.into())
                        }
                        Operand::Move(place) => (Operand::Move, place),
                        Operand::Copy(place) => (Operand::Copy, place),
                    };
                let place_elems = place.projection;
                let arguments = (0..num_args)
                    .map(|x| {
                        let mut place_elems = place_elems.to_vec();
                        place_elems.push(ProjectionElem::Field(x.into(), fields[x]));
                        let projection = tcx.mk_place_elems(&place_elems);
                        let place = Place { local: place.local, projection };
                        Spanned { node: method(place), span: DUMMY_SP }
                    })
                    .collect();
                terminator.kind = TerminatorKind::Call {
                    func: func.node,
                    args: arguments,
                    destination,
                    target,
                    unwind,
                    call_source: CallSource::Misc,
                    fn_span,
                };
            }
            _ => {}
        }
    }
    body
}

// Copied from rustc_mir_transform/src/lib.rs
fn take_array<T, const N: usize>(b: &mut Box<[T]>) -> Result<[T; N], Box<[T]>> {
    let b: Box<[T; N]> = std::mem::take(b).try_into()?;
    Ok(*b)
}
