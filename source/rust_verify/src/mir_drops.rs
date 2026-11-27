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
//! knows nothing about (e.g. called through a function pointer) count as dropped too, since
//! the callee may drop them; a callee Verus checks is checked for its own drops, and Verus
//! relies on the specification of one it does not check (as for its other effects).
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
//! - drop glue the pass cannot see is reported (that of a `dyn` type, an unnormalized
//!   projection, or a coroutine: it may run any `Drop` impl), except that of a type
//!   parameter. Rejecting every drop of a type parameter's value would reject much of vstd
//!   (`PCell::write` drops the old value). Instead, where Verus relies on a callee being
//!   `no_unwind`, the types it is called with are checked for `Drop` impls that may unwind
//!   (the callee may drop values of them). This leaves gaps: drops of type parameters' values
//!   are not checked for atomicity, and a function that drops such a value inside its own
//!   invariant block relies on its callers, which are only checked where they rely on it being
//!   `no_unwind`. They are listed with `VERUS_CHECK_DROPS_VERBOSE=1`.
//!
//! The MIR this pass reads is the one Verus builds for lifetime checking. It has no drops of
//! tracked or ghost variables, of ghost temporaries, or of the shadow copies time-travel
//! prevention makes of exec variables (#3512), none of which the compiled program has. Its
//! drops are the compiled program's.
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
    // and whether it (or a closure in it) has an invariant block. Only their MIR is built.
    let mut verified: HashMap<vir::ast::Path, (bool, bool, bool)> = HashMap::new();
    // the functions Verus knows (verified, external_body or with an assumed specification,
    // of any crate), and whether each is no_unwind and atomic
    let mut known: HashMap<vir::ast::Path, (bool, bool)> = HashMap::new();
    for f in krate.functions.iter() {
        let no_unwind = matches!(f.x.unwind_spec, Some(UnwindSpec::NoUnwind));
        known.insert(f.x.name.path.clone(), (no_unwind, f.x.attrs.atomic));
        if f.x.mode != vir::ast::Mode::Exec || f.x.attrs.is_external_body || f.x.body.is_none() {
            continue;
        }
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
            // each with the callee it is passed to, if it is a type argument of a callee
            let mut dropped: Vec<(Ty<'tcx>, Option<DefId>)> = vec![];
            match &term.kind {
                TerminatorKind::Drop { place, .. } => {
                    dropped.push((place.ty(&*body, tcx).ty, None))
                }
                TerminatorKind::Call { func, args, .. }
                | TerminatorKind::TailCall { func, args, .. } => {
                    let callee = match func.ty(&*body, tcx).kind() {
                        TyKind::FnDef(d, fargs) => {
                            // a trait method call names the trait's method: resolve it to the
                            // impl that runs, which may be one Verus checks
                            let resolved = fargs.no_bound_vars().and_then(|fargs| {
                                Instance::try_resolve(tcx, typing_env, *d, fargs).ok().flatten()
                            });
                            Some(
                                resolved
                                    .map_or((*d, fargs.skip_binder()), |i| (i.def_id(), i.args)),
                            )
                        }
                        _ => None, // a call through a function pointer or closure value
                    };
                    let spec = callee.and_then(|(d, _)| known.get(&def_id_to_vir_path(d)));
                    let checked = callee.is_some_and(|(d, _)| {
                        verified_local_fn(d) || verus_items.id_to_name.contains_key(&d)
                    }) || spec.is_some();
                    if !checked {
                        // the callee may drop the arguments moved into it
                        for a in args.iter() {
                            if let Operand::Move(p) = &a.node {
                                dropped.push((p.ty(&*body, tcx).ty, None));
                            }
                        }
                    } else if let (Some((d, fargs)), Some((callee_no_unwind, callee_atomic))) =
                        (callee, spec)
                    {
                        // The callee's drops of values of its type parameters are not checked
                        // in the callee (see `DropGlue::Unknown` below). Where Verus relies on
                        // the callee being `no_unwind` or atomic, check that the types it is
                        // called with have no `Drop` impl that may unwind.
                        if need_no_unwind && (*callee_no_unwind || *callee_atomic) {
                            // (a value of an unsized type, such as the `Self` of a method call
                            // on a `dyn` reference, cannot be passed or held by value)
                            for t in fargs.types().filter(|t| t.is_sized(tcx, typing_env)) {
                                dropped.push((t, Some(d)));
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

            for (ty, via) in dropped {
                let mut glue = vec![];
                drop_glue_of(tcx, typing_env, ty, &mut HashSet::new(), &mut glue);
                let what = |dty: Ty<'tcx>| match via {
                    None => format!("this may drop a `{dty}`"),
                    Some(d) => format!(
                        "this calls `{}` with a type whose values it may drop, `{dty}`",
                        tcx.def_path_str(d)
                    ),
                };
                for g in glue {
                    let problem = match g {
                        DropGlue::Impl(dty, drop_fn) => {
                            if need_atomic && via.is_none() {
                                // whatever the impl does, running it is a step of its own
                                format!(
                                    "{} in {context}, but running its `Drop` impl is not one \
                                     atomic step (move the value out)",
                                    what(dty)
                                )
                            } else if !drop_fn.is_local() {
                                trusted.insert(format!("{dty}"));
                                continue;
                            } else if !known.contains_key(&def_id_to_vir_path(drop_fn)) {
                                format!(
                                    "{}, whose `Drop` impl is not verified, in {context}; the \
                                     impl may unwind or open invariants (verify the `Drop` impl, \
                                     or move the value out)",
                                    what(dty)
                                )
                            } else {
                                continue;
                            }
                        }
                        DropGlue::Unknown(uty) if matches!(uty.kind(), TyKind::Param(_)) => {
                            // The drop glue of a type parameter is not checked here: rejecting
                            // every such drop would reject much of vstd (`PCell::write` drops
                            // the old value), and the types a function is called with are only
                            // partly checked, at its call sites (above)
                            unchecked.insert(format!("{uty}"));
                            continue;
                        }
                        DropGlue::Unknown(uty) => {
                            // a type parameter, `dyn` type or opaque type may have any `Drop` impl
                            format!(
                                "{} in {context}, whose drop glue is not known here: it may run \
                                 a `Drop` impl that unwinds{atomic} (move the value out, or drop \
                                 it outside)",
                                what(uty),
                                atomic =
                                    if need_atomic { " or is not one atomic step" } else { "" }
                            )
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
