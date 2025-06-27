use rustc_middle::ty::{TyCtxt, TypingEnv};
use rustc_hir::def_id::LocalDefId;
use rustc_hir as hir;
use rustc_middle::hir::place::{Place, PlaceBase, PlaceWithHirId, Projection, ProjectionKind};
use rustc_middle::mir::FakeReadCause;
use rustc_hir::HirId;
use rustc_hir_typeck::expr_use_visitor as euv;
use rustc_middle::ty::{
    self, BorrowKind, ClosureSizeProfileData, Ty, TypeVisitableExt as _, TypeckResults,
    UpvarArgs, UpvarCapture,
};
use rustc_span::Span;

struct FnCtxt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub typing_env: TypingEnv<'tcx>,
    pub closure_def_id: LocalDefId,
    pub typeck_results: &'tcx TypeckResults<'tcx>,
}

pub struct CaptureResults<'tcx> {
    pub fake_reads: Vec<(Place<'tcx>, FakeReadCause, HirId)>,
    pub closure_min_captures: Option<rustc_middle::ty::RootVariableMinCaptureList<'tcx>>,
    pub upvar_tys: Vec<Ty<'tcx>>,
}

/// Intermediate format to store a captured `Place` and associated `ty::CaptureInfo`
/// during capture analysis. Information in this map feeds into the minimum capture
/// analysis pass.
type InferredCaptureInformation<'tcx> = Vec<(Place<'tcx>, ty::CaptureInfo)>;

impl<'tcx> FnCtxt<'tcx> {
    pub(crate) fn analyze_closure(
        &self,
        closure_hir_id: HirId,
        span: Span,
        body_id: hir::BodyId,
        body: &'tcx hir::Body<'tcx>,
        capture_clause: hir::CaptureBy,
    ) -> CaptureResults<'tcx> {
        let ty = self.node_ty(closure_hir_id);

        let (closure_def_id, args, infer_kind) = match *ty.kind() {
            ty::Closure(def_id, args) => {
                (def_id, UpvarArgs::Closure(args), self.closure_kind(ty).is_none())
            }
            // Note(travis): coroutine closures may need additional work
            /*ty::CoroutineClosure(def_id, args) => {
                (def_id, UpvarArgs::CoroutineClosure(args), self.closure_kind(ty).is_none())
            }
            ty::Coroutine(def_id, args) => (def_id, UpvarArgs::Coroutine(args), false),
            ty::Error(_) => {
                // #51714: skip analysis when we have already encountered type errors
                return;
            }*/
            _ => {
                panic!("analyze_closure expected Closure");
            }
        };

        let closure_def_id = closure_def_id.expect_local();

        assert_eq!(self.tcx.hir_body_owner_def_id(body.id()), closure_def_id);

        let mut delegate = InferBorrowKind {
            closure_def_id,
            capture_information: Default::default(),
            fake_reads: Default::default(),
        };

        let _ = euv::ExprUseVisitor::new(
            &*self,
            &mut delegate,
        )
        .consume_body(body);

        delegate.handle_recurive_closures();

        // NOTE(travis): A bunch of coroutine-specific logic was cut here

        let (capture_information, closure_kind, origin) = self
            .process_collected_capture_information(capture_clause, &delegate.capture_information);

        let mut closure_min_captures =
            self.compute_min_captures(closure_def_id, capture_information, span);

        let closure_hir_id = self.tcx.local_def_id_to_hir_id(closure_def_id);

        // NOTE(travis): I considered cutting this, but on reflection I think it IS necessary
        // for soundness. Consider something like:
        //
        // ```rust
        // let foo = || {
        //     let capture = a.x;
        // };
        //
        // drop(foo);
        //
        // do_something_with(a.y.points_to);
        // ```
        //
        // If the edition is < 2021, then the closure will capture a.y, which will be dropped
        // when foo is dropped. 
        if !enable_precise_capture(span) {
            let mut capture_information: InferredCaptureInformation<'tcx> = Default::default();

            if let Some(upvars) = self.tcx.upvars_mentioned(closure_def_id) {
                for var_hir_id in upvars.keys() {
                    let place = self.place_for_root_variable(closure_def_id, *var_hir_id);

                    //debug!("seed place {:?}", place);

                    let capture_kind = self.init_capture_kind_for_place(&place, capture_clause);
                    let fake_info = ty::CaptureInfo {
                        capture_kind_expr_id: None,
                        path_expr_id: None,
                        capture_kind,
                    };

                    capture_information.push((place, fake_info));
                }
            }

            // This will update the min captures based on this new fake information.
            closure_min_captures =
                self.compute_min_captures(closure_def_id, capture_information, span);
        }

        // NOTE(travis): More coroutine-specific stuff cut here

        let final_upvar_tys = self.final_upvar_tys(closure_def_id);

        return CaptureResults {
            upvar_tys: final_upvar_tys,
            fake_reads: delegate.fake_reads,
            closure_min_captures,
        };
    }

    pub(crate) fn node_ty(&self, hir_id: HirId) -> Ty<'tcx> {
        self.typeck_results.node_type(hir_id)
    }

    pub(crate) fn closure_kind(&self, closure_ty: Ty<'tcx>) -> Option<rustc_middle::ty::ClosureKind> {
        if let rustc_middle::ty::TyKind::Closure(_def_id, args) = closure_ty.kind() {
            Some(args.as_closure().kind())
        } else {
            panic!("closure_kind failed");
        }
    }
}

struct InferBorrowKind<'tcx> {
    // The def-id of the closure whose kind and upvar accesses are being inferred.
    closure_def_id: LocalDefId,

    /// For each Place that is captured by the closure, we track the minimal kind of
    /// access we need (ref, ref mut, move, etc) and the expression that resulted in such access.
    ///
    /// Consider closure where s.str1 is captured via an ImmutableBorrow and
    /// s.str2 via a MutableBorrow
    ///
    /// ```rust,no_run
    /// struct SomeStruct { str1: String, str2: String };
    ///
    /// // Assume that the HirId for the variable definition is `V1`
    /// let mut s = SomeStruct { str1: format!("s1"), str2: format!("s2") };
    ///
    /// let fix_s = |new_s2| {
    ///     // Assume that the HirId for the expression `s.str1` is `E1`
    ///     println!("Updating SomeStruct with str1={0}", s.str1);
    ///     // Assume that the HirId for the expression `*s.str2` is `E2`
    ///     s.str2 = new_s2;
    /// };
    /// ```
    ///
    /// For closure `fix_s`, (at a high level) the map contains
    ///
    /// ```ignore (illustrative)
    /// Place { V1, [ProjectionKind::Field(Index=0, Variant=0)] } : CaptureKind { E1, ImmutableBorrow }
    /// Place { V1, [ProjectionKind::Field(Index=1, Variant=0)] } : CaptureKind { E2, MutableBorrow }
    /// ```
    capture_information: InferredCaptureInformation<'tcx>,
    fake_reads: Vec<(Place<'tcx>, FakeReadCause, HirId)>,
}

impl<'tcx> euv::Delegate<'tcx> for InferBorrowKind<'tcx> {
    fn fake_read(
        &mut self,
        place_with_id: &PlaceWithHirId<'tcx>,
        cause: FakeReadCause,
        diag_expr_id: HirId,
    ) {
        if self.is_closure(diag_expr_id) {
            return;
        }

        let PlaceBase::Upvar(_) = place_with_id.place.base else { return };

        // We need to restrict Fake Read precision to avoid fake reading unsafe code,
        // such as deref of a raw pointer.
        let dummy_capture_kind = ty::UpvarCapture::ByRef(ty::BorrowKind::Immutable);

        let (place, _) =
            restrict_capture_precision(place_with_id.place.clone(), dummy_capture_kind);

        let (place, _) = restrict_repr_packed_field_ref_capture(place, dummy_capture_kind);
        self.fake_reads.push((place, cause, diag_expr_id));
    }

    fn consume(&mut self, place_with_id: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        if self.is_closure(diag_expr_id) {
            return;
        }

        let PlaceBase::Upvar(upvar_id) = place_with_id.place.base else { return };
        assert_eq!(self.closure_def_id, upvar_id.closure_expr_id);

        self.capture_information.push((
            place_with_id.place.clone(),
            ty::CaptureInfo {
                capture_kind_expr_id: Some(diag_expr_id),
                path_expr_id: Some(diag_expr_id),
                capture_kind: ty::UpvarCapture::ByValue,
            },
        ));
    }

    fn use_cloned(&mut self, place_with_id: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        if self.is_closure(diag_expr_id) {
            return;
        }

        let PlaceBase::Upvar(upvar_id) = place_with_id.place.base else { return };
        assert_eq!(self.closure_def_id, upvar_id.closure_expr_id);

        self.capture_information.push((
            place_with_id.place.clone(),
            ty::CaptureInfo {
                capture_kind_expr_id: Some(diag_expr_id),
                path_expr_id: Some(diag_expr_id),
                capture_kind: ty::UpvarCapture::ByUse,
            },
        ));
    }

    fn borrow(
        &mut self,
        place_with_id: &PlaceWithHirId<'tcx>,
        diag_expr_id: HirId,
        bk: ty::BorrowKind,
    ) {
        if self.is_closure(diag_expr_id) {
            return;
        }

        let PlaceBase::Upvar(upvar_id) = place_with_id.place.base else { return };
        assert_eq!(self.closure_def_id, upvar_id.closure_expr_id);

        // The region here will get discarded/ignored
        let capture_kind = ty::UpvarCapture::ByRef(bk);

        // We only want repr packed restriction to be applied to reading references into a packed
        // struct, and not when the data is being moved. Therefore we call this method here instead
        // of in `restrict_capture_precision`.
        let (place, mut capture_kind) =
            restrict_repr_packed_field_ref_capture(place_with_id.place.clone(), capture_kind);

        // Raw pointers don't inherit mutability
        if place_with_id.place.deref_tys().any(Ty::is_raw_ptr) {
            capture_kind = ty::UpvarCapture::ByRef(ty::BorrowKind::Immutable);
        }

        self.capture_information.push((
            place,
            ty::CaptureInfo {
                capture_kind_expr_id: Some(diag_expr_id),
                path_expr_id: Some(diag_expr_id),
                capture_kind,
            },
        ));
    }

    fn mutate(&mut self, assignee_place: &PlaceWithHirId<'tcx>, diag_expr_id: HirId) {
        if self.is_closure(diag_expr_id) {
            return;
        }

        self.borrow(assignee_place, diag_expr_id, ty::BorrowKind::Mutable);
    }
}

impl<'tcx> InferBorrowKind<'tcx> {
    fn is_closure(_diag_expr_id: HirId) -> bool {
        false
    }
}

/// Truncates `place` to have up to `len` projections.
/// `curr_mode` is the current required capture kind for the place.
/// Returns the truncated `place` and the updated required capture kind.
///
/// Note: Capture kind changes from `MutBorrow` to `UniqueImmBorrow` if the truncated part of the `place`
/// contained `Deref` of `&mut`.
fn truncate_place_to_len_and_update_capture_kind<'tcx>(
    place: &mut Place<'tcx>,
    curr_mode: &mut ty::UpvarCapture,
    len: usize,
) {
    let is_mut_ref = |ty: Ty<'_>| matches!(ty.kind(), ty::Ref(.., hir::Mutability::Mut));

    // If the truncated part of the place contains `Deref` of a `&mut` then convert MutBorrow ->
    // UniqueImmBorrow
    // Note that if the place contained Deref of a raw pointer it would've not been MutBorrow, so
    // we don't need to worry about that case here.
    match curr_mode {
        ty::UpvarCapture::ByRef(ty::BorrowKind::Mutable) => {
            for i in len..place.projections.len() {
                if place.projections[i].kind == ProjectionKind::Deref
                    && is_mut_ref(place.ty_before_projection(i))
                {
                    *curr_mode = ty::UpvarCapture::ByRef(ty::BorrowKind::UniqueImmutable);
                    break;
                }
            }
        }

        ty::UpvarCapture::ByRef(..) => {}
        ty::UpvarCapture::ByValue | ty::UpvarCapture::ByUse => {}
    }

    place.projections.truncate(len);
}


/// Truncate the capture so that the place being borrowed is in accordance with RFC 1240,
/// which states that it's unsafe to take a reference into a struct marked `repr(packed)`.
fn restrict_repr_packed_field_ref_capture<'tcx>(
    mut place: Place<'tcx>,
    mut curr_borrow_kind: ty::UpvarCapture,
) -> (Place<'tcx>, ty::UpvarCapture) {
    let pos = place.projections.iter().enumerate().position(|(i, p)| {
        let ty = place.ty_before_projection(i);

        // Return true for fields of packed structs.
        match p.kind {
            ProjectionKind::Field(..) => match ty.kind() {
                ty::Adt(def, _) if def.repr().packed() => {
                    // We stop here regardless of field alignment. Field alignment can change as
                    // types change, including the types of private fields in other crates, and that
                    // shouldn't affect how we compute our captures.
                    true
                }

                _ => false,
            },
            _ => false,
        }
    });

    if let Some(pos) = pos {
        truncate_place_to_len_and_update_capture_kind(&mut place, &mut curr_borrow_kind, pos);
    }

    (place, curr_borrow_kind)
}


/// Truncate `place` so that an `unsafe` block isn't required to capture it.
/// - No projections are applied to raw pointers, since these require unsafe blocks. We capture
///   them completely.
/// - No projections are applied on top of Union ADTs, since these require unsafe blocks.
fn restrict_precision_for_unsafe(
    mut place: Place<'_>,
    mut curr_mode: ty::UpvarCapture,
) -> (Place<'_>, ty::UpvarCapture) {
    if place.base_ty.is_raw_ptr() {
        truncate_place_to_len_and_update_capture_kind(&mut place, &mut curr_mode, 0);
    }

    if place.base_ty.is_union() {
        truncate_place_to_len_and_update_capture_kind(&mut place, &mut curr_mode, 0);
    }

    for (i, proj) in place.projections.iter().enumerate() {
        if proj.ty.is_raw_ptr() {
            // Don't apply any projections on top of a raw ptr.
            truncate_place_to_len_and_update_capture_kind(&mut place, &mut curr_mode, i + 1);
            break;
        }

        if proj.ty.is_union() {
            // Don't capture precise fields of a union.
            truncate_place_to_len_and_update_capture_kind(&mut place, &mut curr_mode, i + 1);
            break;
        }
    }

    (place, curr_mode)
}

/// Truncate projections so that following rules are obeyed by the captured `place`:
/// - No Index projections are captured, since arrays are captured completely.
/// - No unsafe block is required to capture `place`
/// Returns the truncated place and updated capture mode.
fn restrict_capture_precision(
    place: Place<'_>,
    curr_mode: ty::UpvarCapture,
) -> (Place<'_>, ty::UpvarCapture) {
    let (mut place, mut curr_mode) = restrict_precision_for_unsafe(place, curr_mode);

    if place.projections.is_empty() {
        // Nothing to do here
        return (place, curr_mode);
    }

    for (i, proj) in place.projections.iter().enumerate() {
        match proj.kind {
            ProjectionKind::Index | ProjectionKind::Subslice => {
                // Arrays are completely captured, so we drop Index and Subslice projections
                truncate_place_to_len_and_update_capture_kind(&mut place, &mut curr_mode, i);
                return (place, curr_mode);
            }
            ProjectionKind::Deref => {}
            ProjectionKind::OpaqueCast => {}
            ProjectionKind::Field(..) => {} // ignore
        }
    }

    (place, curr_mode)
}

/// Precise capture is enabled if user is using Rust Edition 2021 or higher.
/// `span` is the span of the closure.
fn enable_precise_capture(span: Span) -> bool {
    // We use span here to ensure that if the closure was generated by a macro with a different
    // edition.
    span.at_least_rust_2021()
}
