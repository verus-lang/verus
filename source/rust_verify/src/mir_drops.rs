//! Check the implicit `drop` calls of verified exec functions against what
//! Verus assumes about them, using rustc's drop-elaborated MIR.
//!
//! Verus's encoding does not see implicit drops: a value that goes out of scope runs its
//! `Drop` impl (and the impls of its fields) at a point rustc decides. Verus assumes that such
//! a call neither unwinds nor opens an invariant. That holds for `Drop` impls Verus verifies
//! (they must be marked `no_unwind` and `opens_invariants none`, and their bodies are checked
//! against that), but not for unverified ones (an external impl, or an
//! `external_type_specification` of a type with a `Drop` impl): #2949 (a `no_unwind`
//! function whose drop panics) and #778 (a drop inside an atomic function).
//!
//! rustc's MIR after drop elaboration has one `Drop` terminator for each drop that can run.
//! For each verified exec function that is `no_unwind` or atomic, this pass finds the `Drop`
//! terminators on non-cleanup paths, the types with a `Drop` impl in the dropped value's drop
//! glue, and reports the impls that are local to the crate but not verified. `Drop` impls of
//! other crates (std's, or a dependency's) are trusted, as before; they are listed with
//! `VERUS_CHECK_DROPS_VERBOSE=1`. `--no-check-drops` turns the check off.
//!
//! The same applies inside `open_atomic_invariant!` blocks of any verified exec function:
//! the block must be one atomic step, and an unverified drop inside it is arbitrary code.
//! Those drops are found by span: a `Drop` terminator (or a moving call to an unverified
//! callee) whose span lies in the body of an atomic `OpenInvariant`.

use crate::external::{CrateItems, VerifOrExternal};
use rustc_hir::OwnerId;
use rustc_hir::def::DefKind;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::ty::{Ty, TyCtxt, TyKind, TypingEnv};
use rustc_span::def_id::{DefId, LocalDefId};
use std::collections::{HashMap, HashSet};
use vir::ast::{Krate, UnwindSpec};

/// The `Drop` impls (the `drop` method's DefId) that dropping a value of type `ty` can run.
fn drop_impls_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    seen: &mut HashSet<Ty<'tcx>>,
    out: &mut Vec<(Ty<'tcx>, DefId)>,
) {
    if !seen.insert(ty) || !ty.needs_drop(tcx, typing_env) {
        return;
    }
    match ty.kind() {
        TyKind::Adt(adt, args) => {
            if let Some(d) = tcx.adt_destructor(adt.did()) {
                out.push((ty, d.did));
            }
            if adt.is_box() {
                drop_impls_of(tcx, typing_env, args.type_at(0), seen, out);
                return;
            }
            for v in adt.variants() {
                for f in v.fields.iter() {
                    drop_impls_of(tcx, typing_env, f.ty(tcx, args).skip_norm_wip(), seen, out);
                }
            }
            // container types (Vec<T>, ...) drop their elements through raw pointers, which
            // the field walk does not see: walk the type arguments too
            for a in args.types() {
                drop_impls_of(tcx, typing_env, a, seen, out);
            }
        }
        TyKind::Tuple(ts) => {
            for t in ts.iter() {
                drop_impls_of(tcx, typing_env, t, seen, out);
            }
        }
        TyKind::Array(t, _) | TyKind::Slice(t) => drop_impls_of(tcx, typing_env, *t, seen, out),
        TyKind::Closure(_, args) => {
            for t in args.as_closure().upvar_tys() {
                drop_impls_of(tcx, typing_env, t, seen, out);
            }
        }
        _ => {}
    }
}

pub(crate) struct DropFinding {
    pub span: rustc_span::Span,
    pub msg: String,
}

pub(crate) fn check_drops<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &Krate,
    crate_items: &CrateItems,
    def_id_to_vir_path: impl Fn(DefId) -> vir::ast::Path,
    verbose: bool,
) -> Vec<DropFinding> {
    // which VIR functions need checking: exec with body, no_unwind or atomic, or containing
    // atomic invariant blocks (whose body spans are collected)
    let mut wanted: HashMap<vir::ast::Path, (bool, bool)> = HashMap::new();
    let mut atomic_blocks: HashMap<vir::ast::Path, Vec<rustc_span::Span>> = HashMap::new();
    for f in krate.functions.iter() {
        if f.x.mode != vir::ast::Mode::Exec || f.x.attrs.is_external_body {
            continue;
        }
        let Some(fbody) = &f.x.body else { continue };
        let no_unwind = matches!(f.x.unwind_spec, Some(UnwindSpec::NoUnwind));
        let atomic = f.x.attrs.atomic;
        let blocks = std::cell::RefCell::new(vec![]);
        let _ = vir::ast_visitor::map_expr_visitor(fbody, &|e: &vir::ast::Expr| {
            if let vir::ast::ExprX::OpenInvariant(_, _, b, vir::ast::InvAtomicity::Atomic) = &e.x {
                if let Some(sp) = crate::spans::from_raw_span(&b.span.raw_span) {
                    blocks.borrow_mut().push(sp);
                }
            }
            Ok(e.clone())
        });
        let blocks = blocks.into_inner();
        if no_unwind || atomic || !blocks.is_empty() {
            wanted.insert(f.x.name.path.clone(), (no_unwind, atomic));
        }
        if !blocks.is_empty() {
            atomic_blocks.insert(f.x.name.path.clone(), blocks);
        }
    }
    let verified_local = |did: DefId| -> bool {
        let Some(local) = did.as_local() else { return false };
        // the `drop` method's owner is the impl item
        let owner = tcx.local_def_id_to_hir_id(local).owner;
        let impl_owner = tcx.parent(did);
        let item = crate_items.map.get(&owner).or_else(|| {
            impl_owner.as_local().and_then(|l| crate_items.map.get(&OwnerId { def_id: l }))
        });
        matches!(item, Some(VerifOrExternal::VerusAware { external_body: false, .. }))
    };
    let mut findings = vec![];
    let mut trusted: HashSet<String> = HashSet::new();
    for local in tcx.hir_body_owners() {
        let did: DefId = local.to_def_id();
        if !matches!(tcx.def_kind(did), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let path = def_id_to_vir_path(did);
        let Some((no_unwind, atomic)) = wanted.get(&path).copied() else { continue };
        let blocks: &[rustc_span::Span] = atomic_blocks.get(&path).map_or(&[], |v| &v[..]);
        let in_atomic_block = |sp: rustc_span::Span| {
            let sp = sp.source_callsite();
            blocks.iter().any(|b| b.contains(sp) || b.source_callsite().contains(sp))
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(local);
        let body = body.borrow();
        let typing_env = body.typing_env(tcx);
        for bb in body.basic_blocks.iter() {
            if bb.is_cleanup {
                continue; // already unwinding
            }
            // the values this block's terminator may drop: a `Drop` terminator's place, or the
            // arguments moved into a callee that is not verified (std's `unwrap_or` drops its
            // unused default, #2949); a verified callee's drops are checked there
            let mut dropped: Vec<Ty<'tcx>> = vec![];
            match &bb.terminator().kind {
                TerminatorKind::Drop { place, .. } => dropped.push(place.ty(&*body, tcx).ty),
                TerminatorKind::Call { func, args, .. } => {
                    let callee = match func.ty(&*body, tcx).kind() {
                        TyKind::FnDef(d, _) => Some(*d),
                        _ => None,
                    };
                    let callee_verified = callee.map_or(false, |d| {
                        d.as_local().map_or(false, |l| {
                            let owner = tcx.local_def_id_to_hir_id(l).owner;
                            matches!(
                                crate_items.map.get(&owner),
                                Some(VerifOrExternal::VerusAware { external_body: false, .. })
                            )
                        })
                    });
                    if !callee_verified {
                        for a in args.iter() {
                            if let rustc_middle::mir::Operand::Move(p) = &a.node {
                                dropped.push(p.ty(&*body, tcx).ty);
                            }
                        }
                    }
                }
                _ => continue,
            }
            let term_span = bb.terminator().source_info.span;
            let block_only = !no_unwind && !atomic;
            if block_only && !in_atomic_block(term_span) {
                continue;
            }
            for ty in dropped {
                let mut impls = vec![];
                drop_impls_of(tcx, typing_env, ty, &mut HashSet::new(), &mut impls);
                for (dty, drop_fn) in impls {
                    if verified_local(drop_fn) {
                        continue; // checked no_unwind / opens_invariants none
                    }
                    if !drop_fn.is_local() {
                        trusted.insert(format!("{dty}"));
                        continue;
                    }
                    let span = bb.terminator().source_info.span;
                    let what = match (no_unwind, atomic) {
                        (_, true) => "an atomic function",
                        (true, _) => "a `no_unwind` function",
                        _ => "an atomic invariant block",
                    };
                    findings.push(DropFinding {
                    span,
                    msg: format!(
                        "this may drop a `{dty}`, whose `Drop` impl is not verified, in {what}; \
                         Verus assumes that implicit drops do not unwind and open no invariants \
                         (verify the `Drop` impl, or move the value out)"
                    ),
                });
                }
            }
        }
        let _ = local as LocalDefId;
    }
    if verbose && !trusted.is_empty() {
        let mut t: Vec<_> = trusted.into_iter().collect();
        t.sort();
        eprintln!("note: --check-drops trusts the Drop impls of: {}", t.join(", "));
    }
    findings
}
