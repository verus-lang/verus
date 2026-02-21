use super::prelude::*;
use crate::cell::CellId;
use crate::pcm::*;
use core::sync::atomic::Ordering;
use std::marker::PhantomData;

verus! {

// Location = CellId
// Timestamp = nat
/// Represents "simple" view
pub ghost struct View(pub Map<CellId, nat>);

impl View {
    /// True when `other` is contained in this View
    pub open spec fn contains(self, other: Self) -> bool {
        other.0.submap_of(self.0)
    }

    pub open spec fn join(self, other: Self) -> Self {
        View(Map::new(
            |k: CellId| self.0.dom().contains(k) || other.0.dom().contains(k),
            |k: CellId| if self.0.dom().contains(k) {
                if other.0.dom().contains(k) {
                    if self.0[k] >= other.0[k] { self.0[k] } else { other.0[k] }
                } else {
                    self.0[k]
                }
            } else {
                other.0[k]
            },
        ))
    }

    pub open spec fn empty() -> Self {
        Self ( Map::<CellId, nat>::empty() )
    }

    pub open spec fn singleton(loc: CellId, timestamp: nat) -> Self {
        Self ( map![loc => timestamp] )
    }
}

pub ghost struct History<T>(pub Map<nat, (T, Option<View>)>);

impl<T> History<T> {
    /// True when `other` is contained in this History
    pub open spec fn contains(self, other: Self) -> bool {
        other.0.submap_of(self.0)
    }

    pub open spec fn join(self, other: Self) -> History<T> 
        recommends
            self.contains(other) || other.contains(self)
    {
        History(self.0.union_prefer_right(other.0))
    }

    pub open spec fn contains_timestamp(&self, timestamp: nat) -> bool {
        self.0.dom().contains(timestamp)
    }

    pub open spec fn is_max_timestamp(&self, timestamp: nat) -> bool
    {
        &&& self.contains_timestamp(timestamp)
        &&& forall |t| #[trigger] self.contains_timestamp(t) ==> t <= timestamp
    }

    pub open spec fn max_timestamp(&self) -> nat 
        recommends
            self.0.len() > 0
    {
        self.0.dom().to_seq().map(|i, t| t as int).max() as nat
    }

    pub open spec fn singleton(timestamp: nat, val: T, view: Option<View>) -> Self {
        History(map![timestamp => (val, view)])
    }

    pub open spec fn is_singleton(&self, timestamp: nat, val: T, view: Option<View>) -> bool {
        self == Self::singleton(timestamp, val, view)
    }

    pub open spec fn has_view(&self, timestamp: nat) -> bool 
        recommends
            self.contains_timestamp(timestamp)
    {
        self.0[timestamp].1.is_some()
    }

    pub open spec fn view(&self, timestamp: nat) -> View
        recommends
            self.has_view(timestamp)
    {
        self.0[timestamp].1.unwrap()
    }

    pub open spec fn value(&self, timestamp: nat) -> T
        recommends
            self.contains_timestamp(timestamp)
    {
        self.0[timestamp].0
    }
}

pub ghost struct HistorySingleton<T> {
    timestamp: nat,
    value: T,
    view: Option<View>,
}

impl<T> HistorySingleton<T> {
    pub closed spec fn timestamp(&self) -> nat {
        self.timestamp
    }

    pub closed spec fn value(&self) -> T {
        self.value
    }

    pub closed spec fn has_view(&self) -> bool {
        self.view.is_some()
    }

    pub closed spec fn view(&self) -> View
        recommends
            self.has_view(),
    {
        self.view.unwrap()
    }
}

// Fence modalities
pub tracked struct Release<T> {
    _phantom: PhantomData<T>
}

impl<T> Release<T> {
    pub uninterp spec fn value(&self) -> T;
}

pub tracked struct Acquire<T> {
    _phantom: PhantomData<T>
}

impl<T> Acquire<T> {
    pub uninterp spec fn value(&self) -> T;
}

// Note 8.11
unsafe impl<T> Objective for Release<T> {}
unsafe impl<T> Objective for Acquire<T> {}

#[verifier::external_body]
// HOARE-REL-FENCE
pub fn rel_fence<T>(Tracked(rsrc): Tracked<T>) -> (out: Tracked<Release<T>>)
    ensures
        rsrc == out@.value(),
{
    core::sync::atomic::fence(Ordering::Release);
    Tracked(proof_from_false())
}

#[verifier::external_body]
// HOARE-ACQ-FENCE
pub fn acq_fence<T>(Tracked(rsrc): Tracked<Acquire<T>>) -> (out: Tracked<T>)
    ensures
        out@ == rsrc.value(),
{
    core::sync::atomic::fence(Ordering::Acquire);
    Tracked(proof_from_false())
}

/// Release modality rules

// skip - RELMOD-MONO
// NOTE skipping RELMOD-PURE (what does owning a pure proposition mean in Verus?)
// skip - RELMOD-AND
// skip - RELMOD-OR. in theory we could encode this rule for all enums, but maybe not necssasry
// NOTE skipping RELMOD-FORALL and RELMOD-EXIST for now
// NOTE skipping RELMOD-LATER-INTRO and RELMOD-UNOPS

impl<T> Release<T> {
    // This is only sound if the goal is a WP, where Release<T> is known to be interpreted under the release view, and T is known to be interpreted under the current view which includes the release view.
    // HOARE-REL-FENCE-ELIM
    pub axiom fn to_inner(tracked self) -> (tracked out: T)
        ensures
            out == self.value(),
    ;

    // RELMOD-SEP -|
    pub axiom fn join<U>(tracked self, tracked other: Release<U>) -> (tracked out: Release<(T, U)>)
        ensures
            out.value() == (self.value(), other.value()),
        ;
}

impl<T, U> Release<(T, U)> {
    // RELMOD-SEP |-
    pub axiom fn split(tracked self) -> (tracked out: (Release<T>, Release<U>))
        ensures
            out.0.value() == self.value().0,
            out.1.value() == self.value().1,
        ;
}

impl<P: PCM> Release<Resource<P>> {
    // GHOST-RELMOD
    pub proof fn as_release(tracked rsrc: Resource<P>) -> (tracked out: Self)
        ensures
            out.value() == rsrc,
    {
        objective_as_release(rsrc)
    }
}

// NOTE The specs seem weak
// RELMOD-WAND
pub axiom fn apply_release_fn<P, Q>(
    tracked f: Release<proof_fn[Once](tracked p: P) -> tracked Q>, 
    tracked rsrc: Release<P>,
) -> (tracked out: Release<Q>)
        requires
            f.value().requires((rsrc.value(),))
        ensures
            f.value().ensures((rsrc.value(),), out.value())
       ;

/// Acquire modality rules

// skip - ACQMOD-MONO

// skip - ACQMOD-OR

impl<T> Acquire<T> {
    // See note on HOARE-REL-FENCE-ELIM
    // HOARE-ACQ-FENCE-INTRO
    pub axiom fn as_acquire(tracked rsrc: T) -> (tracked out: Self)
        ensures
            out.value() == rsrc,
    ;

    // ACQMOD-SEP -|
    pub axiom fn join<U>(tracked self, tracked other: Acquire<U>) -> (tracked out: Acquire<(T, U)>)
        ensures
            out.value() == (self.value(), other.value()),
        ;
}

impl<T, U> Acquire<(T, U)> {
    // ACQMOD-SEP |-
    pub axiom fn split(tracked rsrc: Self) -> (tracked out: (Acquire<T>, Acquire<U>))
        ensures
            out.0.value() == rsrc.value().0,
            out.1.value() == rsrc.value().1,
        ;
}

impl<P: PCM> Acquire<Resource<P>> {
    // ACQMOD-GHOST
    pub proof fn to_inner(tracked self) -> (tracked out: Resource<P>)
        ensures
            out == self.value(),
    {
        objective_from_acquire(self)
    }
}

// ACQMOD-WAND
pub axiom fn apply_acquire_fn<P, Q>(
    tracked f: Acquire<proof_fn[Once](tracked p: P) -> tracked Q>, 
    tracked rsrc: Acquire<P>,
) -> (tracked out: Acquire<Q>)
        requires
            f.value().requires((rsrc.value(),))
        ensures
            f.value().ensures((rsrc.value(),), out.value())
       ;

// Objective
/// This trait should be implemented on types P such that objective(P) holds
pub unsafe trait Objective {}

// GHOST-OBJ 
// todo: what other ghost state can be marked Objective?
unsafe impl<P: PCM> Objective for Resource<P> {}

// implement Objective on primitive types -- these are trivially objective
macro_rules! declare_primitive_is_objective {
    ($($a:ty),*) => {
        verus! {
            $(unsafe impl Objective for $a {})*
        }
    }
}

declare_primitive_is_objective!(bool, char, (), u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, int, nat, str);

// implement Objective on tuples of Objective types
// todo: could we support automatically implementing Objective on structs and enums whose fields are all Objective? (but where would we need this though?)
macro_rules! declare_tuple_is_objective {
    ($($($a:ident)*),*) => {
        verus! {
            $(unsafe impl<$($a: Objective, )*> Objective for ($($a, )*) {})*
        }
    }
}

// could declare for longer tuples as well
declare_tuple_is_objective!(T0, T0 T1, T0 T1 T2, T0 T1 T2 T3);

// note: the fact that tuples are Objective (above) suffices for OBJMOD-SEP

// OBJ with wand update
unsafe impl<'a, P: Objective, Q: Objective, F: ProofFnOnce> Objective for proof_fn<'a, F>(tracked p: P) -> tracked Q {}

// OBJMOD-RELMOD-INTRO
pub axiom fn objective_as_release<T: Objective>(tracked v: T) -> (tracked out: Release<T>)
    ensures
        v == out.value(),
;

// RELMOD-OBJMOD-ELIM
pub axiom fn objective_from_release<T: Objective>(tracked r: Release<T>) -> (tracked out: T)
    ensures
        r.value() == out,
;

// OBJMOD-ACQMOD-INTRO
pub axiom fn objective_as_acquire<T: Objective>(tracked v: T) -> (tracked out: Acquire<T>)
    ensures
        v == out.value(),
;

// ACQMOD-OBJMOD-ELIM
pub axiom fn objective_from_acquire<T: Objective>(tracked a: Acquire<T>) -> (tracked out: T)
    ensures
        a.value() == out,
;

// skip - timeless

// todo - can the tracked types be Send/Sync? Should either impl Send or !Send

// Explicit views
#[derive(Clone, Copy)]
pub tracked struct ViewSeen;

impl ViewSeen {
    pub uninterp spec fn view(&self) -> View;

    // VS_BOT
    pub axiom fn empty() -> (tracked out: ViewSeen)
        ensures
            out.view() == View::empty(),
    ;

    // VS-JOIN |-
    pub axiom fn split(tracked self, v1: View, v2: View) -> (tracked out: (Self, Self))
        requires
            self.view() == v1.join(v2)
        ensures
            out.0.view() == v1,
            out.1.view() == v2
        ;
    
    // VS-JOIN -|
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        ensures
            out.view() == self.view().join(other.view())
        ;

    // VS-MONO
    pub axiom fn restrict(tracked self, v: View) -> (tracked out: Self)
        requires
            self.view().contains(v)
        ensures
            out.view() == v
        ;
}

#[derive(Clone, Copy)]
pub tracked struct EmptyViewSeen;

unsafe impl Objective for EmptyViewSeen {}

impl EmptyViewSeen {
    pub axiom fn from_view_seen(tracked v: ViewSeen) -> (tracked out: Self)
        requires
            v.view() == View::empty()
        ;

    pub axiom fn as_view_seen(tracked self) -> (tracked out: ViewSeen)
        ensures
            out.view() == View::empty()
        ;
}

// ViewAt<T> is persistent when T is persistent
// the #[derive] attribute will ensure that ViewAt<T>: Copy only when T: Copy
#[derive(Copy)]
pub tracked struct ViewAt<T> {
    _phantom: PhantomData<T>,
}

impl<T: Clone> Clone for ViewAt<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self { unimplemented!() }
}

unsafe impl<T> Objective for ViewAt<T> {}

// skipped --
// VA-VS - I'm not sure if this is used anywhere in program proofs?
// VA-IDEMP
impl<T> ViewAt<T> {
    pub uninterp spec fn view(&self) -> View;

    pub uninterp spec fn value(&self) -> T;

    // VA-INTRO
    pub axiom fn new(tracked t: T) -> (tracked out: (Self, ViewSeen))
        ensures
            out.0.value() == t,
            out.0.view() == out.1.view(), 
        ;

    // VA-INTRO-INCL
    pub axiom fn new_incl(tracked t: T, tracked sn: &ViewSeen) -> (tracked out: (Self, ViewSeen))
        ensures
            out.0.value() == t,
            out.0.view() == out.1.view(),
            out.1.view().contains(sn.view())
        ;

    // VA-ELIM
    pub axiom fn into_inner(tracked self, tracked sn: ViewSeen) -> (tracked out: T)
        requires
            self.view() == sn.view() // could be sn.view().contains(self.view())
        ensures
            out == self.value()
        ;

    // this is encoding view monotonicity
    pub axiom fn weaken(tracked self, v: View) -> (tracked out: Self)
        requires
            v.contains(self.view())
        ensures
            out.view() == v,
            out.value() == self.value()
        ;

    // VA-MONO, VA-WAND, VA-UNOPS with update -- we are encoding all of these as the below rule.
    // strictly speaking, this rule models a wand update.
    pub axiom fn apply_fn<U>(
        tracked self,
        tracked f: ViewAt<proof_fn[Once](tracked v1: T) -> tracked U>,
    ) -> (tracked out: ViewAt<U>)
            requires
                f.value().requires((self.value(),)),
                f.view() == self.view()
            ensures
                f.value().ensures((self.value(),), out.value()),
                out.view() == self.view()
        ;
}

impl<T: Objective> ViewAt<T> {
    // VA-OBJ |-
    pub axiom fn new_objective(tracked t: T) -> (tracked out: Self)
        ensures
            out.value() == t
        ;

    // VA-OBJ -|
    pub axiom fn into_inner_objective(tracked self) -> (tracked out: T)
        ensures
            out == self.value()
        ;
}

#[derive(Copy)]
pub tracked struct ViewJoin<T> {
    _phantom: PhantomData<T>,
}

impl<T: Clone> Clone for ViewJoin<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self { unimplemented!() }
}

unsafe impl<T> Objective for ViewJoin<T> {}

// I am skipping a lot of rules for now. If we don't use raw invariants, I am not sure how much we will use view joins
// skip - VJ-JOIN, VA-VJ, VJ-VA, VJ-VA-ACC, VJ-BOPS (including wand), VJ-UNOPS
impl<T> ViewJoin<T> {
    pub uninterp spec fn view(&self) -> View;

    pub uninterp spec fn value(&self) -> T;

    // this is encoding view monotonicity
    pub axiom fn weaken(tracked self, v: View) -> (tracked out: Self)
        requires
            v.contains(self.view())
        ensures
            out.view() == v,
            out.value() == self.value()
        ;

    // VJ-INTRO-NOW
    pub axiom fn new(tracked t: T) -> (tracked out: Self)
        ensures
            out.value() == t
        ;

    // this is kind of like VJ-UNFOLD |-
    // this isn't an exact encoding, but perhaps this would work fine in practice
    pub proof fn new_incl(tracked t: T, tracked sn: &ViewSeen) -> (tracked out: Self)
        ensures
            out.value() == t,
            out.view().contains(sn.view())
    {
        let tracked (at, _) = ViewAt::new_incl(t, sn);
        Self::from_view_at(at)
    }

    // VJ-ELIM
    // this is kind of also encoding VJ-UNFOLD -|, but not exactly
    pub axiom fn into_inner(tracked self, tracked sn: ViewSeen) -> (tracked out: T)
        requires
            self.view() == sn.view()
        ensures
            out == self.value()
        ;

    // VA-TO-VJ
    pub axiom fn from_view_at(tracked at: ViewAt<T>) -> (tracked out: Self)
        ensures
            out.view() == at.view(),
            out.value() == at.value()
        ;

    // VJ-ELIM-VA
    pub axiom fn as_view_at(tracked self, tracked sn: ViewSeen) -> (tracked out: (ViewSeen, ViewAt<T>))
        ensures
            out.0.view().contains(sn.view()),
            out.1.view() == out.0.view().join(self.view()),
            out.1.value() == self.value()
        ;
}

// Non-Atomic Points-To
pub tracked struct PrimitiveNonAtomicPointsTo<T> {
    _phantom: PhantomData<T>,
}

impl<T> PrimitiveNonAtomicPointsTo<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> HistorySingleton<T>;

    pub closed spec fn timestamp(&self) -> nat {
        self.hist().timestamp()
    }

    pub closed spec fn value(&self) -> T {
        self.hist().value()
    }

    pub closed spec fn has_view(&self) -> bool {
        self.hist().has_view()
    }

    pub closed spec fn view(&self) -> View
        recommends
            self.has_view(),
    {
        self.hist().view()
    }
}

pub tracked struct NonAtomicPointsTo<T> {
    _phantom: PhantomData<T>
}

impl<T> NonAtomicPointsTo<T> {
    pub uninterp spec fn seen(&self) -> Option<ViewSeen>;

    pub uninterp spec fn prim(&self) -> PrimitiveNonAtomicPointsTo<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        (!self.prim().has_view() && self.seen().is_none()) || (self.prim().view()
            == self.seen().unwrap().view())
    }

    pub closed spec fn loc(&self) -> CellId {
        self.prim().loc()
    }

    pub closed spec fn hist(&self) -> HistorySingleton<T> {
        self.prim().hist()
    }

    pub closed spec fn timestamp(&self) -> nat {
        self.prim().timestamp()
    }

    pub closed spec fn value(&self) -> T {
        self.prim().value()
    }

    pub closed spec fn has_view(&self) -> bool {
        self.seen().is_some()
    }

    pub closed spec fn view(&self) -> View
        recommends
            self.has_view(),
    {
        self.seen().unwrap().view()
    }

    // NA-AT-SW
    pub axiom fn as_atomic_points_to(tracked self) -> (tracked out: (AtomicPointsTo<T>, SingleWriter<T>, ViewSeen, nat))
        ensures
            out.0.loc() == self.loc(),
            out.0.mode() == AtomicMode::SingleWriter,
            out.1.loc() == self.loc(),
            out.1.hist() == out.0.hist(),
            out.0.hist().is_singleton(out.3, self.value(), Some(out.2.view()))
        ;

    // NA-AT-SW-VIEW
    pub axiom fn as_atomic_points_to_with_rsrc<P>(tracked self, tracked rsrc: P) -> (tracked out: (ViewAt<(P, AtomicPointsTo<T>, SingleWriter<T>)>, ViewSeen, nat))
        ensures
            out.0.view() == out.1.view(),
            out.0.value().0 == rsrc,
            out.0.value().1.loc() == self.loc(),
            out.0.value().1.mode() == AtomicMode::SingleWriter,
            out.0.value().2.loc() == self.loc(),
            out.0.value().1.hist() == out.0.value().2.hist(),
            out.0.value().1.hist().is_singleton(out.2, self.value(), Some(out.1.view()))
        ;
}

// Atomic Points-To

// AT-CAS-CAS-FRAC-AGREE -- skip for now, we aren't modeling the timestamp
// AT-CAS-SPLIT -- skip, taken care of by borrowing
// AT-SN-UNFOLD -- skip for now, only relates to race detector info

pub enum AtomicMode {
    Concurrent,
    SingleWriter,
    CompareAndSwap,
}

// note: skipped ghost name, single-writer timestamp
pub tracked struct AtomicPointsTo<T> {
    _phantom: PhantomData<T>
}

impl<T> AtomicPointsTo<T> {
    pub uninterp spec fn mode(&self) -> AtomicMode;

    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> History<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist().0.dom().len() > 0
    }

    // AT-EXCL
    pub axiom fn excl(tracked &mut self, tracked other: &Self)
        ensures
            self.loc() != other.loc()
        ;

    // AT-SW-AGREE
    pub axiom fn single_writer_agree(tracked &self, tracked sw: &SingleWriter<T>)
        requires
            self.loc() == sw.loc()
        ensures
            self.mode() == AtomicMode::SingleWriter,
            self.hist() == sw.hist()
        ;

    // AT-CAS-FRAC-AGREE
    pub axiom fn compare_and_swap_agree(tracked &self, tracked cas: &CompareAndSwap<T>)
        requires
            self.loc() == cas.loc()
        ensures
            self.mode() != AtomicMode::Concurrent,
            self.hist().contains(cas.hist())
        ;

    // AT-SN-VALID
    pub axiom fn history_seen_agree(tracked &self, tracked sn: &HistorySeen<T>)
        requires
            self.loc() == sn.loc()
        ensures
            self.hist().contains(sn.hist())
        ;

    pub proof fn history_sync_agree(tracked &self, tracked sy: &HistorySync<T>)
        requires
            self.loc() == sy.loc()
        ensures
            self.hist().contains(sy.hist())
    {
        let tracked sn = sy.get_history_seen();
        self.history_seen_agree(&sn);
    }

    // AT-SY
    pub axiom fn get_history_sync(tracked &self) -> (tracked out: HistorySync<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
        ;

    // AT-NA
    pub axiom fn as_nonatomic_points_to(tracked self) -> (tracked out: (NonAtomicPointsTo<T>, ViewSeen, nat))
        ensures
            self.hist().is_max_timestamp(out.2),
            out.0.loc() == self.loc(),
            out.0.timestamp() == out.2,
            out.0.value() == self.hist().value(out.2),
            out.0.has_view() && self.hist().has_view(out.2),
            out.0.view() == self.hist().view(out.2),
            out.1.view() == self.hist().view(out.2)
        ;

    // AT-CON-SW
    pub axiom fn concurrent_as_single_writer(tracked &mut self) -> (tracked out: SingleWriter<T>)
        requires
            old(self).mode() == AtomicMode::Concurrent,
        ensures
            self.mode() == AtomicMode::SingleWriter,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
            out.loc() == self.loc(),
            out.hist() == self.hist()
        ;

    // AT-SW-CON
    pub axiom fn single_writer_as_concurrent(tracked &mut self, tracked sw: SingleWriter<T>)
        requires
            old(self).mode() == AtomicMode::SingleWriter,
            old(self).loc() == sw.loc(),
        ensures
            self.mode() == AtomicMode::Concurrent,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist()
        ;

    // AT-CAS-SW
    pub axiom fn compare_and_swap_as_single_writer(tracked &mut self, tracked cas: CompareAndSwap<T>) -> (tracked out: SingleWriter<T>)
        requires
            old(self).mode() == AtomicMode::CompareAndSwap,
            old(self).loc() == cas.loc(),
        ensures
            self.mode() == AtomicMode::SingleWriter,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
            out.loc() == self.loc(),
            out.hist() == self.hist()
        ;

    // AT-SW-CAS
    pub axiom fn single_writer_as_compare_and_swap(tracked &mut self, tracked sw: SingleWriter<T>) -> (tracked out: CompareAndSwap<T>)
        requires
            old(self).mode() == AtomicMode::SingleWriter,
            old(self).loc() == sw.loc(),
        ensures
            self.mode() == AtomicMode::CompareAndSwap,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
            out.loc() == self.loc(),
            out.hist() == self.hist()
        ;
    
    // AT-CON-CAS |-
    pub axiom fn concurrent_as_compare_and_swap(tracked &mut self) -> (tracked out: CompareAndSwap<T>)
        requires
            old(self).mode() == AtomicMode::Concurrent,
        ensures
            self.mode() == AtomicMode::CompareAndSwap,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
            out.loc() == self.loc(),
            out.hist() == self.hist()
        ;

    // AT-CON-CAS -|
    pub axiom fn compare_and_swap_as_concurrent(tracked &mut self, tracked cas: CompareAndSwap<T>)
        requires
            old(self).mode() == AtomicMode::CompareAndSwap,
            old(self).loc() == cas.loc(),
        ensures
            self.mode() == AtomicMode::Concurrent,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist()
        ;
}

// note: #[derive(Clone)] doesn't seem to work due to PhantomData
#[derive(Copy)]
pub tracked struct HistorySeen<T> {
    _phantom: PhantomData<T>
}

impl<T> Clone for HistorySeen<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self { unimplemented!() }
}

impl<T> HistorySeen<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> History<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist().0.dom().len() > 0
    }

    // AT-SN-JOIN
    // note: there was a typo in Hai's thesis: https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/master/gpfsl/logic/atomic_preds.v#L624
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc()
        ensures
            out.loc() == self.loc(),
            out.hist() == self.hist().join(other.hist())
        ;

    // AT-SN-MONO
    pub axiom fn restrict(tracked &mut self, h: History<T>)
        requires
            h.0.dom().len() > 0,
            old(self).hist().contains(h)
        ensures
            self.loc() == old(self).loc(),
            self.hist() == h
        ;

    // AT-SN-UNFOLD
    pub axiom fn get_view_seen(tracked &self, timestamp: nat) -> (tracked out: ViewSeen)
        requires
            self.hist().contains_timestamp(timestamp) && self.hist().has_view(timestamp)
        ensures
            out.view() == View::singleton(self.loc(), timestamp)
        ;
}

#[derive(Copy)]
pub tracked struct HistorySync<T> {
    _phantom: PhantomData<T>
}

impl<T> Clone for HistorySync<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self { unimplemented!() }
}

impl<T> HistorySync<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> History<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist().0.dom().len() > 0
    }

    // AT-SY-SN
    pub axiom fn get_history_seen(tracked &self) -> (tracked out: HistorySeen<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
    ;

    // AT-SY-UNFOLD
    pub axiom fn get_view_seen(tracked &self, timestamp: nat) -> (tracked out: (ViewSeen, ViewSeen))
        requires
            self.hist().contains_timestamp(timestamp) && self.hist().has_view(timestamp)
        ensures
            out.0.view() == self.hist().view(timestamp),
            out.1.view() == View::singleton(self.loc(), timestamp)
        ;

    // AT-SY-JOIN
    // note: there was a typo in Hai's thesis: https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/master/gpfsl/logic/atomic_preds.v#L742
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc()
        ensures
            out.loc() == self.loc(),
            out.hist() == self.hist().join(other.hist())
        ;

    // AT-SY-MONO
    pub axiom fn restrict(tracked &mut self, h: History<T>)
        requires
            h.0.dom().len() > 0,
            old(self).hist().contains(h)
        ensures
            self.loc() == old(self).loc(),
            self.hist() == h
        ;
}

pub tracked struct SingleWriter<T> {
    _phantom: PhantomData<T>
}

impl<T> SingleWriter<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> History<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist().0.dom().len() > 0
    }

    // AT-SW-EXCL
    pub axiom fn excl(tracked &mut self, tracked other: &Self)
        ensures
            self.loc() != other.loc()
        ;

    // AT-SW-CAS-EXCL
    pub axiom fn compare_and_swap_excl(tracked &mut self, tracked other: &CompareAndSwap<T>)
        ensures
            self.loc() != other.loc()
        ;

    // AT-SW-SY
    pub axiom fn get_history_sync(tracked &self) -> (tracked out: HistorySync<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
    ;
}

// note: skipped timestamp
pub tracked struct CompareAndSwap<T> {
    _phantom: PhantomData<T>
}

impl<T> CompareAndSwap<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> History<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist().0.dom().len() > 0
    }

    // AT-CAS-JOIN
    pub axiom fn join(tracked &self, tracked other: &Self) -> (tracked out: &Self)
        requires
            self.loc() == other.loc()
        ensures
            out.loc() == self.loc(),
            out.hist() == self.hist().join(other.hist())
        ;
    
    // AT-CAS-SN
    pub axiom fn get_history_seen(tracked &self) -> (tracked out: HistorySeen<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
    ;
}

// this is just a placeholder type for now, we can refine what the internal representation should be later
// (Rust's atomic types use an UnsafeCell internally)
pub struct Ptr<T>(pub T);

impl<T> Ptr<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn value(&self) -> T;

    // I'm just encoding these functions as axioms right now so that we don't have to worry about implementing them.
    // That way, we can focus only on the signatures.

    // NA-ALLOC but simplified:
    // - only allocates a single location
    // - ensures that the location is initialized
    // should this also say something about the history in the NonAtomicPointsTo? I'm not sure if this info is ever used.
    pub axiom fn new_nonatomic(t: T) -> (tracked out: (Self, NonAtomicPointsTo<T>))
        ensures
            out.0.loc() == out.1.loc(),
            out.1.value() == t
        ;

    // NA-READ
    pub axiom fn read_nonatomic(&self, tracked pt: &NonAtomicPointsTo<T>) -> (out: T) where T: Copy
        requires
            self.loc() == pt.loc()
        ensures
            out == pt.value()
        ;

    // NA-WRITE
    pub axiom fn write_nonatomic(&self, tracked pt: &mut NonAtomicPointsTo<T>, t: T)
        requires
            self.loc() == old(pt).loc()
        ensures
            pt.loc() == old(pt).loc(),
            pt.value() == t
            // we could add more info here about the timestamp and view for the points to here?
            // there is nothing in the rule itself though, so maybe it is not needed?
            // more generally, will we ever need to reason about the PrimitiveNonAtomicPointsTo?
        ;

    pub proof fn new_atomic_single_writer(t: T) -> (tracked out: (Self, AtomicPointsTo<T>, SingleWriter<T>, ViewSeen, nat))
        ensures
            out.0.loc() == out.1.loc(),
            out.1.mode() == AtomicMode::SingleWriter,
            out.2.loc() == out.1.loc(),
            out.2.hist() == out.1.hist(),
            out.1.hist().is_singleton(out.4, t, Some(out.3.view()))
    {
        let tracked (p, na_pt) = Self::new_nonatomic(t);
        let tracked (a_pt, sw, sn, ts) = na_pt.as_atomic_points_to();
        (p, a_pt, sw, sn, ts)
    }

    pub proof fn new_atomic_compare_and_swap(t: T) -> (tracked out: (Self, AtomicPointsTo<T>, CompareAndSwap<T>, ViewSeen, nat))
        ensures
            out.0.loc() == out.1.loc(),
            out.1.mode() == AtomicMode::CompareAndSwap,
            out.2.loc() == out.1.loc(),
            out.2.hist() == out.1.hist(),
            out.1.hist().is_singleton(out.4, t, Some(out.3.view()))
    {
        let tracked (p, mut a_pt, sw, sn, ts) = Self::new_atomic_single_writer(t);
        let tracked cas = a_pt.single_writer_as_compare_and_swap(sw);
        (p, a_pt, cas, sn, ts)
    }

    pub proof fn new_atomic_concurrent(t: T) -> (tracked out: (Self, AtomicPointsTo<T>, ViewSeen, nat))
        ensures
            out.0.loc() == out.1.loc(),
            out.1.mode() == AtomicMode::Concurrent,
            out.1.hist().is_singleton(out.3, t, Some(out.2.view()))
    {
        let tracked (p, mut a_pt, sw, sn, ts) = Self::new_atomic_single_writer(t);
        let tracked _ = a_pt.single_writer_as_concurrent(sw);
        (p, a_pt, sn, ts)
    }

    // AT-READ-SN -- acquire
    // I skipped mutating the ViewAt<AtomicPointsTo> to join the new view. This is easily derivable from monotonicity.
    // However, we *do* need to mutate the HistorySeen to add the write we have now observed. 
    pub axiom fn read_acquire(&self, tracked v_sn: &ViewSeen, tracked h_sn: &mut HistorySeen<T>, tracked pt: ViewAt<AtomicPointsTo<T>>) -> (tracked out: (T, ViewSeen, History<T>, nat))
        requires
            self.loc() == pt.value().loc(),
            self.loc() == old(h_sn).loc(),
        ensures
            ({
                let v = out.0; // returned value
                let v_sn_new = out.1; // new ViewSeen
                let hist = out.2; // new history for HistorySeen 
                let timestamp = out.3; // timestamp of the write that was read
                let message_view = hist.view(timestamp); // message view for the write that was read
                &&& v_sn_new.view().contains(v_sn.view())
                &&& pt.value().hist().contains(hist) && hist.contains(old(h_sn).hist())
                &&& hist.value(timestamp) == v // the new HistorySeen will include the write we just read
                &&& old(h_sn).hist().max_timestamp() <= timestamp // the write is no earlier than the last write that was read at this loc
                &&& v_sn_new.view().contains(message_view) // because this is an acquire read, the latest ViewSeen will contain the message view
                &&& h_sn.loc() == old(h_sn).loc()
                &&& h_sn.hist() == hist
            })
        ;

    // AT-READ-SN -- relaxed
    pub axiom fn read_relaxed(&self, tracked v_sn: &ViewSeen, tracked h_sn: &mut HistorySeen<T>, tracked pt: ViewAt<AtomicPointsTo<T>>) -> (tracked out: (T, ViewSeen, Acquire<ViewSeen>, History<T>, nat))
        requires
            self.loc() == pt.value().loc(),
            self.loc() == old(h_sn).loc(),
        ensures
            ({
                let v = out.0; // returned value
                let v_sn_new = out.1; // new ViewSeen
                let acq_v_sn = out.2; // the view for the write that was read, under the acquire modality
                let hist = out.3; // new history for HistorySeen 
                let timestamp = out.4; // timestamp of the write that was read
                let message_view = hist.view(timestamp); // message view for the write that was read
                &&& v_sn_new.view().contains(v_sn.view())
                &&& pt.value().hist().contains(hist) && hist.contains(old(h_sn).hist())
                &&& hist.value(timestamp) == v // the new HistorySeen will include the write we just read
                &&& old(h_sn).hist().max_timestamp() <= timestamp // the write is no earlier than the last write that was read at this loc
                &&& acq_v_sn.value().view() == message_view // because this is a relaxed read, the Acquire<ViewSeen> will be the message view
                &&& h_sn.loc() == old(h_sn).loc()
                &&& h_sn.hist() == hist
            })
        ;

    // AT-WRITE-SN -- release
    // skipped mutating the history for h_sn + wrapping it with ViewAt:
    // - adding the write to the history could be derived as follows: 
    //    - apply view monotonicity to the returned HistorySeen to learn it at the latest view
    //    - apply VA-ELIM to unwrap the HistorySeen
    //    - join the two HistorySeens 
    // - note: I don't know whether knowing the full HistorySeen _under ViewAt_ is useful (maybe would be useful if you had to transfer this to a different thread?)
    // I also skipped mutating the ViewAt<AtomicPointsTo> to join the new view. This is easily derivable from monotonicity. We *do* need to add the new write to the history here, though.
    pub axiom fn write_release_concurrent(&self, t: T, tracked v_sn: &ViewSeen, tracked h_sn: HistorySeen<T>, tracked pt: &mut ViewAt<AtomicPointsTo<T>>) -> (tracked out: (ViewSeen, ViewAt<HistorySeen<T>>, nat))
        requires
            self.loc() == h_sn.loc(),
            self.loc() == old(pt).value().loc(),
            old(pt).value().mode() == AtomicMode::Concurrent
        ensures
            ({
                let v_sn_new = out.0; // new ViewSeen
                let h_sn_write = out.1; // HistorySeen containing singleton history for this write, known at the write view
                let timestamp = out.2; // timestamp of the new write
                let singleton_write_hist = History::singleton(timestamp, t, Some(v_sn_new.view()));
                &&& v_sn_new.view().contains(v_sn.view()) && v_sn.view() != v_sn_new.view() // latest thread view is strictly greater than the old one
                &&& h_sn.hist().max_timestamp() < timestamp && !old(pt).value().hist().0.dom().contains(timestamp) // timestamp is greater than all of the thread's observations and is unique for the history
                &&& h_sn_write.view() == v_sn_new.view() // because this is a release write, the write view is the latest thread view
                &&& h_sn_write.value().loc() == self.loc()
                &&& h_sn_write.value().hist() == singleton_write_hist
                &&& pt.view() == old(pt).view()
                &&& pt.value().loc() == old(pt).value().loc()
                &&& pt.value().hist() == old(pt).value().hist().join(singleton_write_hist) // the points-to's history has the new write
            })
        ;
}


} // verus!
