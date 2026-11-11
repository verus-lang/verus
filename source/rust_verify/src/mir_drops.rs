//! Check the implicit `drop` calls of verified exec functions against what
//! Verus assumes about them, using rustc's drop-elaborated MIR.
//!
//! Verus's encoding does not see implicit drops: a value that goes out of scope runs its
//! `Drop` impl (and the impls in its drop glue) at a point rustc decides. Verus assumes about
//! each such drop what it knows about the `Drop` impls that Verus checks: they are `no_unwind`
//! and `opens_invariants none`. Unchecked code can break those assumptions in three ways:
//!
//! - (a) a drop that unwinds, in a `no_unwind` function;
//! - (b) a drop that unwinds, in an invariant block (atomic or local), which then exits
//!   early with the invariant not restored;
//! - (c) any drop that is not one atomic step, in an atomic function or an atomic invariant
//!   block.
//!
//! rustc's MIR after drop elaboration has one `Drop` terminator for each drop that can run,
//! and this pass checks those on non-cleanup paths. Arguments moved into a callee that Verus
//! does not check count as dropped too, since the callee may drop them (std's `unwrap_or`
//! drops its unused default); a callee Verus checks is checked for its own drops.
//!
//! For each dropped value, the pass walks its drop glue for the `Drop` impls it can run:
//!
//! - in an atomic context (c), running any `Drop` impl is a step of its own, so every impl
//!   in the drop glue is reported, whoever wrote it (`Drop` impls cannot be marked
//!   `#[verifier::atomic]`, as no trait method can);
//! - otherwise (a, b), an impl of this crate that Verus knows (verified, or `external_body`)
//!   is fine: Verus requires `Drop` impls to be `no_unwind`. An impl of this crate that Verus
//!   doesn't know (an unverified impl, or the impl of a type given an
//!   `external_type_specification`) may unwind. Impls of other crates (std's, a dependency's)
//!   are trusted not to unwind, as before; they are listed with `VERUS_CHECK_DROPS_VERBOSE=1`;
//! - drop glue the pass cannot see (that of a type parameter, a `dyn` type, an unnormalized
//!   projection, or a coroutine) is not checked; such drops are listed with
//!   `VERUS_CHECK_DROPS_VERBOSE=1`. This is a known gap: `fn f<T>(x: T) no_unwind {}` passes,
//!   though `f` may be called with a `T` whose `Drop` impl unwinds. It cannot simply be
//!   rejected here: the MIR this pass reads is the one Verus builds for lifetime checking,
//!   which still contains the tracked (ghost) values, and drops of those (often of a type
//!   parameter, as in vstd's `atomic_with_ghost!`) do not happen in the compiled program.
//!
//! Invariant blocks are found in the MIR itself: a block starts at a call to
//! `open_atomic_invariant_begin` or `open_local_invariant_begin` and ends at the matching call
//! to `open_invariant_end`. The bodies of closures defined in verified functions are checked
//! for invariant blocks too.
//!
//! `--no-check-drops` turns the check off.

use crate::external::{CrateItems, VerifOrExternal};
use crate::verus_items::{OpenInvariantBlockItem, VerusItem, VerusItems};
use rustc_hir::OwnerId;
use rustc_hir::def::DefKind;
use rustc_middle::mir::{BasicBlock, Body, Operand, START_BLOCK, TerminatorKind};
use rustc_middle::ty::{Instance, Ty, TyCtxt, TyKind, TypingEnv, Unnormalized};
use rustc_span::def_id::DefId;
use std::collections::{HashMap, HashSet};
use vir::ast::{Krate, UnwindSpec};

/// What dropping a value can run, as far as this pass can tell
enum DropGlue<'tcx> {
    /// the `Drop` impl of `ty` (its `drop` method)
    Impl(Ty<'tcx>, DefId),
    /// drop glue of `ty` that this pass cannot see
    Unknown(Ty<'tcx>),
}

/// The drop glue of `ty`
fn drop_glue_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    seen: &mut HashSet<Ty<'tcx>>,
    out: &mut Vec<DropGlue<'tcx>>,
) {
    if !seen.insert(ty) || !ty.needs_drop(tcx, typing_env) {
        return;
    }
    let mut walk =
        |t: Ty<'tcx>, out: &mut Vec<DropGlue<'tcx>>| drop_glue_of(tcx, typing_env, t, seen, out);
    match ty.kind() {
        // no drop glue (`needs_drop` is false for these; listed for exhaustiveness)
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never
        | TyKind::Foreign(_)
        | TyKind::FnDef(..)
        | TyKind::FnPtr(..)
        | TyKind::RawPtr(..)
        | TyKind::Ref(..) => {}
        TyKind::Adt(adt, args) => {
            if let Some(d) = tcx.adt_destructor(adt.did()) {
                out.push(DropGlue::Impl(ty, d.did));
            }
            for v in adt.variants() {
                for f in v.fields.iter() {
                    match tcx.try_normalize_erasing_regions(typing_env, f.ty(tcx, args)) {
                        Ok(t) => walk(t, out),
                        Err(_) => out.push(DropGlue::Unknown(f.ty(tcx, args).skip_normalization())),
                    }
                }
            }
            // container types (`Vec<T>`, `Box<T>`, ...) drop their elements through raw
            // pointers, which the field walk does not see: walk the type arguments too
            for a in args.types() {
                walk(a, out);
            }
        }
        TyKind::Tuple(ts) => {
            for t in ts.iter() {
                walk(t, out);
            }
        }
        TyKind::Array(t, _) | TyKind::Slice(t) | TyKind::Pat(t, _) => walk(*t, out),
        TyKind::Closure(_, args) => {
            for t in args.as_closure().upvar_tys() {
                walk(t, out);
            }
        }
        TyKind::CoroutineClosure(_, args) => {
            for t in args.as_coroutine_closure().upvar_tys() {
                walk(t, out);
            }
        }
        TyKind::Alias(..) => {
            match tcx.try_normalize_erasing_regions(typing_env, Unnormalized::new_wip(ty)) {
                Ok(t) if t != ty && !matches!(t.kind(), TyKind::Alias(..)) => walk(t, out),
                _ => out.push(DropGlue::Unknown(ty)),
            }
        }
        // the drop glue depends on a type this pass does not know (a type parameter, the type
        // behind a `dyn`), or on state it does not model (a coroutine's saved locals)
        TyKind::Param(_)
        | TyKind::Dynamic(..)
        | TyKind::Coroutine(..)
        | TyKind::CoroutineWitness(..)
        | TyKind::UnsafeBinder(_)
        | TyKind::Bound(..)
        | TyKind::Placeholder(_)
        | TyKind::Infer(_)
        | TyKind::Error(_) => out.push(DropGlue::Unknown(ty)),
    }
}

pub(crate) struct DropFinding {
    pub span: rustc_span::Span,
    pub msg: String,
}

/// For each basic block that is not on a cleanup path, the invariant blocks open when it runs
/// (innermost last; `true` for an atomic invariant). `None` for blocks not reached, and for
/// every block if the begin and end calls do not nest properly, in which case the caller
/// must assume the worst.
fn open_invariants<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    verus_items: &VerusItems,
) -> Option<HashMap<BasicBlock, Vec<bool>>> {
    let item = |func: &Operand<'tcx>| match func.ty(body, tcx).kind() {
        TyKind::FnDef(d, _) => match verus_items.id_to_name.get(d) {
            Some(VerusItem::OpenInvariantBlock(i)) => Some(*i),
            _ => None,
        },
        _ => None,
    };
    let mut state: HashMap<BasicBlock, Vec<bool>> = HashMap::new();
    let mut work = vec![(START_BLOCK, vec![])];
    while let Some((bb, open)) = work.pop() {
        if body.basic_blocks[bb].is_cleanup {
            continue; // already unwinding
        }
        match state.get(&bb) {
            Some(prev) if *prev == open => continue,
            Some(_) => return None, // reached with different invariants open
            None => {}
        }
        state.insert(bb, open.clone());
        let term = body.basic_blocks[bb].terminator();
        let mut after = open;
        if let TerminatorKind::Call { func, .. } = &term.kind {
            match item(func) {
                Some(OpenInvariantBlockItem::OpenAtomicInvariantBegin) => after.push(true),
                Some(OpenInvariantBlockItem::OpenLocalInvariantBegin) => after.push(false),
                Some(OpenInvariantBlockItem::OpenInvariantEnd) => {
                    after.pop()?;
                }
                None => {}
            }
        }
        for s in term.successors() {
            work.push((s, after.clone()));
        }
    }
    Some(state)
}

pub(crate) fn check_drops<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &Krate,
    crate_items: &CrateItems,
    verus_items: &VerusItems,
    def_id_to_vir_path: impl Fn(DefId) -> vir::ast::Path,
    verbose: bool,
) -> Vec<DropFinding> {
    // the verified exec functions that need checking: whether each is no_unwind and atomic,
    // and whether it (or a closure in it) has an invariant block. The MIR of other functions
    // is not built here: building it may evaluate constants that only Verus's own pipeline
    // can evaluate.
    let mut verified: HashMap<vir::ast::Path, (bool, bool, bool)> = HashMap::new();
    // the functions Verus knows (verified or external_body)
    let mut known: HashSet<vir::ast::Path> = HashSet::new();
    for f in krate.functions.iter() {
        known.insert(f.x.name.path.clone());
        if f.x.mode != vir::ast::Mode::Exec || f.x.attrs.is_external_body || f.x.body.is_none() {
            continue;
        }
        let no_unwind = matches!(f.x.unwind_spec, Some(UnwindSpec::NoUnwind));
        let has_block = std::cell::Cell::new(false);
        let _ = vir::ast_visitor::map_expr_visitor(f.x.body.as_ref().unwrap(), &|e| {
            if let vir::ast::ExprX::OpenInvariant(..) = &e.x {
                has_block.set(true);
            }
            Ok(e.clone())
        });
        let has_block = has_block.get();
        if no_unwind || f.x.attrs.atomic || has_block {
            verified.insert(f.x.name.path.clone(), (no_unwind, f.x.attrs.atomic, has_block));
        }
    }
    let verified_local_fn = |did: DefId| -> bool {
        let Some(local) = did.as_local() else { return false };
        let owner = tcx.local_def_id_to_hir_id(local).owner;
        let impl_owner = tcx.parent(did);
        let item = crate_items.map.get(&owner).or_else(|| {
            impl_owner.as_local().and_then(|l| crate_items.map.get(&OwnerId { def_id: l }))
        });
        matches!(item, Some(VerifOrExternal::VerusAware { external_body: false, .. }))
    };

    let mut findings = vec![];
    let mut trusted: HashSet<String> = HashSet::new();
    let mut unchecked: HashSet<String> = HashSet::new();
    for local in tcx.hir_body_owners() {
        let did: DefId = local.to_def_id();
        // a closure is checked for invariant blocks if its enclosing function is verified
        let (no_unwind, atomic) = match tcx.def_kind(did) {
            DefKind::Fn | DefKind::AssocFn => match verified.get(&def_id_to_vir_path(did)) {
                Some((no_unwind, atomic, _)) => (*no_unwind, *atomic),
                None => continue,
            },
            DefKind::Closure => {
                let root = tcx.typeck_root_def_id(did);
                if !matches!(tcx.def_kind(root), DefKind::Fn | DefKind::AssocFn)
                    || !matches!(verified.get(&def_id_to_vir_path(root)), Some((_, _, true)))
                {
                    continue;
                }
                (false, false)
            }
            _ => continue,
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(local);
        let body = body.borrow();
        let typing_env = body.typing_env(tcx);
        let open = open_invariants(tcx, &body, verus_items);
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue; // already unwinding
            }
            // invariants open at this block; if the blocks don't nest, assume an atomic one
            let (in_block, in_atomic_block) = match &open {
                Some(m) => match m.get(&bb) {
                    Some(o) => (!o.is_empty(), o.contains(&true)),
                    None => continue, // unreachable
                },
                None => (true, true),
            };
            let need_no_unwind = no_unwind || in_block;
            let need_atomic = atomic || in_atomic_block;
            if !need_no_unwind && !need_atomic {
                continue;
            }
            let context = if atomic {
                "an atomic function"
            } else if in_atomic_block {
                "an atomic invariant block"
            } else if in_block {
                "an invariant block"
            } else {
                "a `no_unwind` function"
            };

            // the values this block's terminator may drop
            let term = data.terminator();
            let mut dropped: Vec<Ty<'tcx>> = vec![];
            match &term.kind {
                TerminatorKind::Drop { place, .. } => dropped.push(place.ty(&*body, tcx).ty),
                TerminatorKind::Call { func, args, .. }
                | TerminatorKind::TailCall { func, args, .. } => {
                    let callee = match func.ty(&*body, tcx).kind() {
                        TyKind::FnDef(d, fargs) => {
                            // a trait method call names the trait's method: resolve it to the
                            // impl that runs, which may be one Verus checks
                            let resolved = fargs.no_bound_vars().and_then(|fargs| {
                                Instance::try_resolve(tcx, typing_env, *d, fargs).ok().flatten()
                            });
                            Some(resolved.map_or(*d, |instance| instance.def_id()))
                        }
                        _ => None, // a call through a function pointer or closure value
                    };
                    let checked = callee.is_some_and(|d| {
                        verified_local_fn(d) || verus_items.id_to_name.contains_key(&d)
                    });
                    if !checked {
                        for a in args.iter() {
                            if let Operand::Move(p) = &a.node {
                                dropped.push(p.ty(&*body, tcx).ty);
                            }
                        }
                    }
                }
                // these drop nothing
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::UnwindResume
                | TerminatorKind::UnwindTerminate(_)
                | TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Yield { .. }
                | TerminatorKind::CoroutineDrop
                | TerminatorKind::FalseEdge { .. }
                | TerminatorKind::FalseUnwind { .. }
                | TerminatorKind::InlineAsm { .. } => {}
            }

            for ty in dropped {
                let mut glue = vec![];
                drop_glue_of(tcx, typing_env, ty, &mut HashSet::new(), &mut glue);
                for g in glue {
                    let problem = match g {
                        DropGlue::Impl(dty, drop_fn) => {
                            if need_atomic {
                                // whatever the impl does, running it is a step of its own
                                format!(
                                    "this may drop a `{dty}` in {context}, but running its `Drop` \
                                     impl is not one atomic step (move the value out)"
                                )
                            } else if !drop_fn.is_local() {
                                trusted.insert(format!("{dty}"));
                                continue;
                            } else if !known.contains(&def_id_to_vir_path(drop_fn)) {
                                format!(
                                    "this may drop a `{dty}`, whose `Drop` impl is not verified, \
                                     in {context}; the impl may unwind or open invariants \
                                     (verify the `Drop` impl, or move the value out)"
                                )
                            } else {
                                continue;
                            }
                        }
                        DropGlue::Unknown(uty) => {
                            unchecked.insert(format!("{uty}"));
                            continue;
                        }
                    };
                    findings.push(DropFinding { span: term.source_info.span, msg: problem });
                }
            }
        }
    }
    if verbose {
        for (what, set) in
            [("trusts the Drop impls of", trusted), ("does not check drops of", unchecked)]
        {
            if !set.is_empty() {
                let mut t: Vec<_> = set.into_iter().collect();
                t.sort();
                eprintln!("note: --check-drops {what}: {}", t.join(", "));
            }
        }
    }
    findings
}
