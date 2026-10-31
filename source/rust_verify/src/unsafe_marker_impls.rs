//! Check user-written `unsafe impl Send` and `unsafe impl Sync`.
//!
//! An `unsafe impl Send for X<Args> where W` is accepted if the built-in auto-trait rule
//! could derive it, i.e., if (assuming `W`, and coinductively assuming `X<Args>: Send`)
//! the type of every field of `X` is `Send`.
//! We extend Rust's rules with the following hypotheses, which hold in Verus
//! (a raw pointer can only be used along with a permission token, whose own
//! `Send`/`Sync` impls are what matter):
//!   - `*mut T: Send + Sync`
//!   - `*const T: Send + Sync`
//!   - `PhantomData<T>: Send + Sync`
//! We only recurse into the fields of datatypes that are transparent to Verus
//! (relative to the module containing the impl); everything else is handed
//! to rustc's trait solver unchanged.
//!
//! See `rust_verify/unsafe_marker_impls_notes.md` for a description of
//! how rustc handles auto traits, and the corner cases considered here.

use crate::context::Context;
use crate::util::err_span_bare;
use rustc_hir::Mutability;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::{ParamEnv, Ty, TyCtxt, TyKind, TypeVisitableExt, TypingMode, Unnormalized};
use rustc_span::Span;
use rustc_trait_selection::traits::ObligationCtxt;
use std::collections::{HashMap, HashSet};
use vir::ast::{Datatype, Path, VirErr};

pub(crate) struct UnsafeMarkerImpl {
    pub(crate) impl_def_id: LocalDefId,
    pub(crate) module_path: Path,
    pub(crate) span: Span,
}

/// Why a goal `ty: trait` could not be proven
struct Failure<'tcx> {
    trait_def_id: DefId,
    ty: Ty<'tcx>,
    overflow: bool,
    /// (span, label) for local fields on the way from the impl's self type to the failure
    labels: Vec<(Span, String)>,
    /// textual description of other steps on the way from the impl's self type to the failure
    notes: Vec<String>,
}

struct Checker<'a, 'tcx> {
    ctxt: &'a Context<'tcx>,
    tcx: TyCtxt<'tcx>,
    datatypes: &'a HashMap<Path, Datatype>,
    module_path: &'a Path,
    impl_def_id: LocalDefId,
    param_env: ParamEnv<'tcx>,
    send: DefId,
    sync: DefId,
    /// Goals that are proven or in progress (coinductively assumed).
    /// Since every goal has at most one applicable rule, there is no backtracking,
    /// and any failure fails the whole check, so a single set suffices.
    visited: HashSet<(DefId, Ty<'tcx>)>,
    depth_limit: usize,
}

impl<'a, 'tcx> Checker<'a, 'tcx> {
    fn trait_name(&self, trait_def_id: DefId) -> String {
        self.tcx.item_name(trait_def_id).to_string()
    }

    fn fail(&self, trait_def_id: DefId, ty: Ty<'tcx>) -> Failure<'tcx> {
        Failure { trait_def_id, ty, overflow: false, labels: vec![], notes: vec![] }
    }

    fn is_transparent(&self, adt_def_id: DefId) -> bool {
        let path = self.ctxt.def_id_to_vir_path(adt_def_id);
        match self.datatypes.get(&path) {
            Some(dt) => vir::datatype_to_air::is_datatype_transparent(self.module_path, dt),
            None => false,
        }
    }

    /// Does an explicit impl (positive or negative) exist for the root of `ty`?
    /// If so, rustc does not use the built-in auto impl for any instance of the root type.
    fn has_relevant_impl(&self, trait_def_id: DefId, ty: Ty<'tcx>) -> bool {
        let mut has = false;
        self.tcx.for_each_relevant_impl(trait_def_id, ty, |_| has = true);
        has
    }

    /// Ask rustc's trait solver (without our extra hypotheses) whether `ty: trait` holds
    /// in the impl's ParamEnv, including any region constraints.
    fn rustc_proves(&self, trait_def_id: DefId, ty: Ty<'tcx>) -> bool {
        let infcx = self.tcx.infer_ctxt().build(TypingMode::non_body_analysis());
        let ocx = ObligationCtxt::new(&infcx);
        ocx.register_bound(ObligationCause::dummy(), self.param_env, ty, trait_def_id);
        if ocx.evaluate_obligations_error_on_ambiguity().has_errors() {
            return false;
        }
        let Ok(wf_tys) = ocx.assumed_wf_types(self.param_env, self.impl_def_id) else {
            return false;
        };
        ocx.resolve_regions(self.impl_def_id, self.param_env, wf_tys).is_empty()
    }

    fn rustc_goal(&self, trait_def_id: DefId, ty: Ty<'tcx>) -> Result<(), Failure<'tcx>> {
        if self.rustc_proves(trait_def_id, ty) { Ok(()) } else { Err(self.fail(trait_def_id, ty)) }
    }

    /// Try to normalize an alias type to a different, fully-known type
    fn try_normalize(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        let infcx = self.tcx.infer_ctxt().build(TypingMode::non_body_analysis());
        let ocx = ObligationCtxt::new(&infcx);
        let norm =
            ocx.normalize(&ObligationCause::dummy(), self.param_env, Unnormalized::new_wip(ty));
        if ocx.evaluate_obligations_error_on_ambiguity().has_errors() {
            return None;
        }
        let norm = infcx.resolve_vars_if_possible(norm);
        if norm.has_infer() || norm == ty { None } else { Some(norm) }
    }

    /// Recurse into all fields of all variants of an ADT
    fn prove_fields(
        &mut self,
        trait_def_id: DefId,
        ty: Ty<'tcx>,
        depth: usize,
    ) -> Result<(), Failure<'tcx>> {
        let TyKind::Adt(adt_def, args) = ty.kind() else { unreachable!() };
        for field in adt_def.all_fields() {
            let field_ty = field.ty(self.tcx, args).skip_norm_wip();
            if let Err(mut failure) = self.prove(trait_def_id, field_ty, depth + 1) {
                let step = format!(
                    "field `{}` of `{}` has type `{}`, which must be `{}`",
                    field.name,
                    ty,
                    field_ty,
                    self.trait_name(trait_def_id)
                );
                if let Some(local) = field.did.as_local() {
                    failure.labels.push((self.tcx.def_span(local), step));
                } else {
                    failure.notes.push(step);
                }
                return Err(failure);
            }
        }
        Ok(())
    }

    fn prove_inner(
        &mut self,
        trait_def_id: DefId,
        ty: Ty<'tcx>,
        inner_trait_def_id: DefId,
        inner_ty: Ty<'tcx>,
        depth: usize,
    ) -> Result<(), Failure<'tcx>> {
        self.prove(inner_trait_def_id, inner_ty, depth + 1).map_err(|mut failure| {
            failure.notes.push(format!(
                "`{}: {}` requires `{}: {}`",
                ty,
                self.trait_name(trait_def_id),
                inner_ty,
                self.trait_name(inner_trait_def_id)
            ));
            failure
        })
    }

    fn prove(
        &mut self,
        trait_def_id: DefId,
        ty: Ty<'tcx>,
        depth: usize,
    ) -> Result<(), Failure<'tcx>> {
        if !self.visited.insert((trait_def_id, ty)) {
            // Already proven, or in progress (coinduction)
            return Ok(());
        }
        if depth > self.depth_limit {
            let mut failure = self.fail(trait_def_id, ty);
            failure.overflow = true;
            return Err(failure);
        }
        match ty.kind() {
            // Extra hypotheses, not part of Rust's rules:
            TyKind::RawPtr(..) => Ok(()),
            TyKind::Adt(adt_def, _) if adt_def.is_phantom_data() => Ok(()),

            // Built-in auto impl for ADTs transparent to Verus
            TyKind::Adt(adt_def, _)
                if self.is_transparent(adt_def.did())
                    && !self.has_relevant_impl(trait_def_id, ty)
                    && !ty.has_unsafe_fields() =>
            {
                self.prove_fields(trait_def_id, ty, depth)
            }

            // unsafe impl<T: Sync + ?Sized> Send for &T {}
            TyKind::Ref(_, inner, Mutability::Not) if trait_def_id == self.send => {
                self.prove_inner(trait_def_id, ty, self.sync, *inner, depth)
            }

            // Built-in auto impls for structural types
            TyKind::Ref(_, inner, _)
            | TyKind::Array(inner, _)
            | TyKind::Slice(inner)
            | TyKind::Pat(inner, _)
                if !self.has_relevant_impl(trait_def_id, ty) =>
            {
                self.prove_inner(trait_def_id, ty, trait_def_id, *inner, depth)
            }
            TyKind::Tuple(tys) if !self.has_relevant_impl(trait_def_id, ty) => {
                for inner in tys.iter() {
                    self.prove_inner(trait_def_id, ty, trait_def_id, inner, depth)?;
                }
                Ok(())
            }

            TyKind::Alias(..) => match self.try_normalize(ty) {
                Some(norm) => self.prove_inner(trait_def_id, ty, trait_def_id, norm, depth),
                None => self.rustc_goal(trait_def_id, ty),
            },

            // Everything else (opaque datatypes, datatypes with explicit impls,
            // type parameters, primitive types, dyn, closures, function pointers, ...)
            _ => self.rustc_goal(trait_def_id, ty),
        }
    }

    fn check_impl(&mut self, imp: &UnsafeMarkerImpl, trait_def_id: DefId) -> Result<(), VirErr> {
        let tcx = self.tcx;
        let trait_ref = tcx.impl_trait_ref(imp.impl_def_id).instantiate_identity().skip_norm_wip();
        let self_ty = trait_ref.self_ty();
        let trait_name = self.trait_name(trait_def_id);
        let header = format!("cannot verify `unsafe impl {} for {}`", trait_name, self_ty);
        let TyKind::Adt(adt_def, _) = self_ty.kind() else {
            return Err(err_span_bare(
                imp.span,
                format!("{header}: Verus only supports `unsafe impl {trait_name}` for datatypes"),
            ));
        };
        if !self.is_transparent(adt_def.did()) {
            return Err(err_span_bare(
                imp.span,
                format!("{header}: the type `{self_ty}` must be transparent to Verus in this module"),
            )
            .help("the datatype must be declared inside `verus!`, not `external_body`, and its fields must be visible to the module containing the impl"));
        }
        if self_ty.has_unsafe_fields() {
            return Err(err_span_bare(
                imp.span,
                format!("{header}: the type `{self_ty}` has unsafe fields"),
            ));
        }

        // Coinductive hypothesis: assume the goal itself
        self.visited.insert((trait_def_id, self_ty));
        match self.prove_fields(trait_def_id, self_ty, 0) {
            Ok(()) => Ok(()),
            Err(failure) => {
                let goal = format!("`{}: {}`", failure.ty, self.trait_name(failure.trait_def_id));
                let msg = if failure.overflow {
                    format!("{header}: recursion limit reached while checking {goal}")
                } else {
                    format!("{header}: could not prove {goal}")
                };
                let mut err = err_span_bare(imp.span, msg);
                for (span, label) in failure.labels.iter().rev() {
                    err = err.secondary_label(&crate::spans::err_air_span(*span), label.clone());
                }
                let mut chain = failure.notes.clone();
                chain.reverse();
                if chain.len() > 0 {
                    err = err.help(chain.join("\n"));
                }
                err = err.help(format!(
                    "in addition to Rust's built-in rules, Verus assumes `*mut T`, `*const T`, and `PhantomData<T>` are `{trait_name}`; datatypes that are not transparent to Verus are not inspected"
                ));
                Err(err)
            }
        }
    }
}

pub(crate) fn check_unsafe_marker_impls<'tcx>(
    ctxt: &Context<'tcx>,
    datatypes: &HashMap<Path, Datatype>,
    impls: &[UnsafeMarkerImpl],
) -> Result<(), Vec<VirErr>> {
    let tcx = ctxt.tcx;
    let send = tcx.get_diagnostic_item(rustc_span::sym::Send).expect("Send");
    let sync = tcx.lang_items().sync_trait().expect("Sync");
    let mut errors = vec![];
    for imp in impls.iter() {
        let trait_def_id = tcx.impl_trait_ref(imp.impl_def_id).skip_binder().def_id;
        assert!(trait_def_id == send || trait_def_id == sync);
        let mut checker = Checker {
            ctxt,
            tcx,
            datatypes,
            module_path: &imp.module_path,
            impl_def_id: imp.impl_def_id,
            param_env: tcx.param_env(imp.impl_def_id),
            send,
            sync,
            visited: HashSet::new(),
            depth_limit: tcx.recursion_limit().0,
        };
        if let Err(err) = checker.check_impl(imp, trait_def_id) {
            errors.push(err);
        }
    }
    if errors.is_empty() { Ok(()) } else { Err(errors) }
}
