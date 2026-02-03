use super::prelude::*;
use crate::cell::CellId;
use crate::pcm::*;
use core::sync::atomic::Ordering;

verus! {

// Location = CellId
// Timestamp = nat
/// Represents "simple" view
pub struct View(pub Map<CellId, nat>);

impl View {
    /// True when `other` is contained in this View
    pub open spec fn contains(self, other: Self) -> bool {
        other.0.submap_of(self.0)
    }

    pub open spec fn empty() -> Self {
        Self ( Map::<CellId, nat>::empty() )
    }
}

pub struct History<T>(pub Map<nat, (T, Option<View>)>);

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

pub struct HistorySingleton<T> {
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
pub struct Release<T> {
    v: T,
}

impl<T> Release<T> {
    pub closed spec fn value(&self) -> T {
        self.v
    }
}

pub struct Acquire<T> {
    v: T,
}

impl<T> Acquire<T> {
    pub closed spec fn value(&self) -> T {
        self.v
    }
}

unsafe impl<T> Objective for Release<T> {}
unsafe impl<T> Objective for Acquire<T> {}

#[verifier::external_body]
// HOARE-REL-FENCE
pub fn rel_fence<T>(Tracked(rsrc): Tracked<T>) -> (out: Tracked<Release<T>>)
    ensures
        rsrc == out@.value(),
{
    core::sync::atomic::fence(Ordering::Release);
    Tracked(Release { v: rsrc })
}

#[verifier::external_body]
// HOARE-ACQ-FENCE
pub fn acq_fence<T>(Tracked(rsrc): Tracked<Acquire<T>>) -> (out: Tracked<T>)
    ensures
        out@ == rsrc.value(),
{
    core::sync::atomic::fence(Ordering::Acquire);
    Tracked(rsrc.v)
}

// This is only sound if the goal is a WP, where Release<T> is known to be interpreted under the release view, and T is known to be interpreted under the current view which includes the release view.
// HOARE-REL-FENCE-ELIM
pub axiom fn rel_fence_elim<T>(tracked rsrc: Release<T>) -> (tracked out: T)
    ensures
        out == rsrc.value(),
;

// See note on rel_fence_elim
// HOARE-ACQ-FENCE-INTRO
pub axiom fn acq_fence_intro<T>(tracked rsrc: T) -> (tracked out: Acquire<T>)
    ensures
        out.value() == rsrc,
;

// RELMOD-GHOST
pub proof fn relmod_ghost<P: PCM>(tracked rsrc: Release<Resource<P>>) -> (tracked out: Resource<P>)
    ensures
        out == rsrc.value(),
{
    rel_fence_elim(rsrc)
}

// ACQMOD-GHOST
pub axiom fn acqmod_ghost<P: PCM>(tracked rsrc: Acquire<Resource<P>>) -> (tracked out: Resource<P>)
    ensures
        out == rsrc.value(),
;

// GHOST-RELMOD
pub axiom fn ghost_relmod<P: PCM>(tracked rsrc: Resource<P>) -> (tracked out: Release<Resource<P>>)
    ensures
        out.value() == rsrc,
;

// implied by acq_fence_intro
// GHOST-ACQMOD
pub proof fn ghost_acqmod<P: PCM>(tracked rsrc: Resource<P>) -> (tracked out: Acquire<Resource<P>>)
    ensures
        out.value() == rsrc,
{
    acq_fence_intro(rsrc)
}

pub proof fn relmod_ghost2<P: PCM>(tracked r: Release<Resource<P>>) -> (tracked out: Resource<P>)
    ensures
        r.value() == out
{
    objective_from_release(r)
}

pub proof fn acqmod_ghost2<P: PCM>(tracked r: Acquire<Resource<P>>) -> (tracked out: Resource<P>)
    ensures
        r.value() == out
{
    objective_from_acquire(r)
}

pub proof fn ghost_relmod2<P: PCM>(tracked r: Resource<P>) -> (tracked out: Release<Resource<P>>)
    ensures
        r == out.value()
{
    objective_as_release(r)
}

pub proof fn ghost_acqmod2<P: PCM>(tracked r: Resource<P>) -> (tracked out: Acquire<Resource<P>>)
    ensures
        r == out.value()
{
    objective_as_acquire(r)
}

/// Release modality rules

// ATTEMPT 1: encode the fact that T1 |- T2 via a proof function that trnasform ownership of T1 into ownership of T2
// pub proof fn relmod_mono<T1, T2>(tracked rsrc : Release<T1>, to : T2, tracked f : proof_fn(tracked t1 : T1) -> tracked T2) -> (tracked out : Release<T2>)
//     requires
//         f.requires((rsrc.v,)),
//         forall|rsrc2: T2| f.ensures((rsrc.v,), rsrc2) ==>  rsrc2 == to,
//     ensures
//         out.v == to,
// {
//     let tracked v2 = f(rsrc.v);
//     Release { v: v2 }
// }
// ATTEMPT 2: encode the fact that T1 |- T2 via a trait. Is this the correct trait definition?
pub trait Entails<T1, T2> {
    proof fn entails(tracked t1: T1, t2: T2) -> (tracked out: T2)
        ensures
            out == t2,
    ;
}

// RELMOD-MONO
pub proof fn relmod_mono<T1, T2, E: Entails<T1, T2>>(
    tracked rsrc: Release<T1>,
    to: T2,
) -> (tracked out: Release<T2>)
    ensures
        out.value() == to,
{
    let tracked v = rel_fence_elim(rsrc);
    let tracked v2 = E::entails(v, to);
    Release { v: v2 }
}

// NOTE skipping RELMOD-PURE (what does owning a pure proposition mean in Verus?)
// pub proof fn relmod_pure<T>(tracked t : Release<T>) -> (out: T)
//     ensures out == rsrc.v,
// {
//     rel_fence_elim(rsrc)
// }
// NOTE I'm not sure if it's very important to have relmod_and, but in any case, below are two attempts at encoding it.
// ATTEMPT 1: Encoding P /\ Q with two separate shared references
// I tried here to return references to P and Q to indicate that there could be sharing, but I'm not sure how to relate rsrc (which need to be P /\ Q) to the result.
// pub axiom fn relmod_and<'a, T>(tracked rsrc: &'a Release<T>, P : T, Q : T) -> (tracked out: (&'a Release<P>, &'a Release<Q>))
//     requires
//         rsrc.v = ???
//     ensures
//         out.0.v == P,
//         out.1.v == Q,
//     ;
// ATTEMPT 2: Encoding the /\ operator explicitly as a struct, where basically owning And<T, T1, T2> means owning resource T and having proofs to get T1 from T and to get T2 from T.
// // For some reason the compiler rejects the below struct:
// // error[E0106]: missing lifetime specifier
// //    --> vstd/atomic_relaxed.rs:144:15
// //     |
// // 144 |     pub fst : proof_fn(tracked t : T) -> tracked T1,
// //     |               ^ expected named lifetime parameter
// //     |
// // help: consider introducing a named lifetime parameter
// //     |
// // 142 ~ pub struct And<'a, T1, T2, T> {
// // 143 |     pub v : Tracked<T>,
// // 144 ~     pub fst : p'a, roof_fn(tracked t : T) -> tracked T1,
// //     |
// pub struct and<T1, T2, T> {
//     pub v : tracked<T>,
//     pub fst : proof_fn(tracked t : T) -> tracked T1,
//     pub snd : proof_fn(tracked t : T) -> tracked T2,
// }
// pub axiom fn relmod_and<'a, T, P, Q>(tracked rsrc: Release<And<T,P,Q>>, p : P, q : Q) -> (tracked out: (Release<P>, &'a Release<Q>))
//     requires
//         rsrc.v.fst.requires((rsrc.v.v,)),
//         forall|p2: P| rsrc.v.fst.ensures((rsrc.v.v,), p2) ==> p2 == p,
//         rsrc.v.snd.requires((rsrc.v.v,)),
//         forall|q2: Q| rsrc.v.snd.ensures((rsrc.v.v,), q2) ==> q2 == q,
//     ensures
//         out.0.v == p,
//         out.1.v == q,
//     ;
// ATTEMPT 3: Encoding the /\ operator explicitly as a trait. Basically owning E where E implements And<T1, T2> means owning resource T and having proofs to get T1 from T and to get T2 from T.
// pub trait And<T1, T2> {
//     proof fn fst(tracked self, to: T1) -> (tracked out: T1)
//         ensures
//             out == to,
//         ;
//     proof fn snd(tracked self, to: T2) -> (tracked out: T2)
//         ensures
//             out == to,
//         ;
// }
// pub axiom fn relmod_and<'a, P, Q, E : And<P, Q>>(tracked rsrc: Release<E>, p : P, q : Q) -> (tracked out: (&'a Release<P>, &'a Release<Q>))
//     requires ???,
//     ensures
//         out.0.v == p,
//         out.1.v == q,
//     ;
pub enum Or<T1, T2> {
    Left(T1),
    Right(T2),
}

// RELMOD-OR
pub axiom fn relmod_or<P, Q>(tracked rsrc: Release<Or<P, Q>>) -> (tracked out: Or<
    Release<P>,
    Release<Q>,
>)
    ensures
        match (rsrc.value(), out) {
            (Or::Left(p), Or::Left(p2)) => p == p2.value(),
            (Or::Right(p), Or::Right(p2)) => p == p2.value(),
            _ => false,
        },
    ;

pub enum MyOr<T1: Objective, T2: Objective> {
    Left(T1),
    Right(T2)
}
unsafe impl<T1: Objective, T2: Objective> Objective for MyOr<T1, T2> {}

// weaker version (T1 and T2 must be objective)
pub proof fn relmod_or2<T1: Objective, T2: Objective>(tracked r: Release<MyOr<T1, T2>>) -> (tracked out: (Option<Release<T1>>, Option<Release<T2>>))
    ensures
        match r.value() {
            MyOr::Left(t1) => out.0.is_some() && out.0.unwrap().value() == t1 && out.1 == None::<Release<T2>>,
            MyOr::Right(t2) => out.1.is_some() && out.1.unwrap().value() == t2 && out.0 == None::<Release<T1>>
        }
{
    match objective_from_release(r) {
        MyOr::Left(t1) => (Some(objective_as_release(t1)), None),
        MyOr::Right(t2) => (None, Some(objective_as_release(t2)))
    }
}

// NOTE skipping RELMOD-FORALL and RELMOD-EXIST for now
// RELMOD-SEP |-
pub axiom fn relmod_sep<P, Q>(tracked rsrc: Release<(P, Q)>) -> (tracked out: (
    Release<P>,
    Release<Q>,
))
    ensures
        out.0.value() == rsrc.value().0,
        out.1.value() == rsrc.value().1,
    ;

// RELMOD-SEP -|
pub axiom fn relmod_join<P, Q>(tracked rsrc: (Release<P>, Release<Q>)) -> (tracked out: Release<
    (P, Q),
>)
    ensures
        out.value() == (rsrc.0.value(), rsrc.1.value()),
    ;

// NOTE The specs seem weak
// RELMOD-WAND
pub axiom fn relmod_wand<P, Q>(
    tracked rsrc: Release<proof_fn[Once](tracked p: P) -> tracked Q>,
) -> (tracked out: proof_fn[Once](tracked p: Release<P>) -> tracked Release<Q>)
        ensures
            forall|p: P| (#[trigger] rsrc.value().requires((p,))) ==>  exists |p2 : Release<P>| (#[trigger] out.requires((p2,))) && p == p2.value(),
            forall|p: Release<P>| (#[trigger] out.requires((p,))) ==>  (#[trigger] rsrc.value().requires((p.value(),))),
            forall|p : P, q : Q| (#[trigger] rsrc.value().ensures((p,), q)) ==>  exists |p2 : Release<P>, q2 : Release<Q>| (#[trigger] out.ensures((p2,), q2)) && p == p2.value() && q == q2.value(),
    				forall|p : Release<P>, q : Release<Q>| (#[trigger] out.ensures((p,), q)) ==>  (#[trigger] rsrc.value().ensures((p.value(),), q.value())),
        ;

// XXX how does verus accept this definition? Shouldn't the field v be private?
// pub axiom fn relmod_wand<P, Q>(
//     tracked rsrc: Release<proof_fn[Once](tracked p: P) -> tracked Q>,
// ) -> (tracked out: proof_fn[Once](tracked p: Release<P>) -> tracked Release<Q>)
// {
//     let tracked f = rsrc.v;
//     let tracked f2 = proof_fn[Once] |tracked p: Release<P>| -> (tracked q: Release<Q>)
//         requires
//             f.requires((p.v,)),
//         {
//             let tracked v2 = f(p.v);
//             Release { v: v2 }
//         };
//     f2
// }

// NOTE skipping RELMOD-LATER-INTRO and RELMOD-UNOPS

/// Acquire modality rules

// ACQMOD-MONO
pub axiom fn acqmod_mono<T1, T2, E: Entails<T1, T2>>(
    tracked rsrc: Acquire<T1>,
    to: T2,
) -> (tracked out: Acquire<T2>)
    ensures
        out.value() == to,
    ;

// ACQMOD-OR
pub axiom fn acqmod_or<P, Q>(tracked rsrc: Acquire<Or<P, Q>>) -> (tracked out: Or<
    Acquire<P>,
    Acquire<Q>,
>)
    ensures
        match (rsrc.value(), out) {
            (Or::Left(p), Or::Left(p2)) => p == p2.value(),
            (Or::Right(p), Or::Right(p2)) => p == p2.value(),
            _ => false,
        },
    ;

// ACQMOD-OR (weaker version)
pub proof fn acqmod_or2<T1: Objective, T2: Objective>(tracked r: Acquire<MyOr<T1, T2>>) -> (tracked out: (Option<Acquire<T1>>, Option<Acquire<T2>>))
    ensures
        match r.value() {
            MyOr::Left(t1) => out.0.is_some() && out.0.unwrap().value() == t1 && out.1 == None::<Acquire<T2>>,
            MyOr::Right(t2) => out.1.is_some() && out.1.unwrap().value() == t2 && out.0 == None::<Acquire<T1>>
        }
{
    match objective_from_acquire(r) {
        MyOr::Left(t1) => (Some(objective_as_acquire(t1)), None),
        MyOr::Right(t2) => (None, Some(objective_as_acquire(t2)))
    }
}

// ACQMOD-SEP |-
pub axiom fn acqmod_sep<P, Q>(tracked rsrc: Acquire<(P, Q)>) -> (tracked out: (
    Acquire<P>,
    Acquire<Q>,
))
    ensures
        out.0.value() == rsrc.value().0,
        out.1.value() == rsrc.value().1,
    ;

// ACQMOD-SEP -|
pub axiom fn acqmod_join<P, Q>(tracked rsrc: (Acquire<P>, Acquire<Q>)) -> (tracked out: Acquire<
    (P, Q),
>)
    ensures
        out.value() == (rsrc.0.value(), rsrc.1.value()),
    ;

// ACQMOD-WAND
pub axiom fn acqmod_wand<P, Q>(
    tracked rsrc: Acquire<proof_fn[Once](tracked p: P) -> tracked Q>,
) -> (tracked out: proof_fn[Once](tracked p: Acquire<P>) -> tracked Acquire<Q>)
        ensures
            forall|p: P| (#[trigger] rsrc.value().requires((p,))) ==>  exists |p2 : Acquire<P>| (#[trigger] out.requires((p2,))) && p == p2.value(),
            forall|p: Acquire<P>| (#[trigger] out.requires((p,))) ==>  (#[trigger] rsrc.value().requires((p.value(),))),
            forall|p : P, q : Q| (#[trigger] rsrc.value().ensures((p,), q)) ==>  exists |p2 : Acquire<P>, q2 : Acquire<Q>| (#[trigger] out.ensures((p2,), q2)) && p == p2.value() && q == q2.value(),
    				forall|p : Acquire<P>, q : Acquire<Q>| (#[trigger] out.ensures((p,), q)) ==>  (#[trigger] rsrc.value().ensures((p.value(),), q.value())),
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

// OBJ-BOPS with wand
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

/// This trait should be implemented on types P such that timeless(P) holds
pub unsafe trait IsTimeless {

}

// Do we have a trait for this or just use Copy?
/// This trait should be implemented on types P such that persistent(P) holds
pub unsafe trait IsPersistent {

}

// Explicit views
pub struct ViewSeen {
    view: View,
}

// How to implement a trait for a specific construction of a struct? 
// unsafe impl Objective for ViewSeen { View::empty() } {

// }

unsafe impl IsTimeless for ViewSeen {

}

unsafe impl IsPersistent for ViewSeen {

}

impl ViewSeen {
    pub closed spec fn view(&self) -> View {
        self.view
    }

    pub closed spec fn empty() -> ViewSeen {
        Self { view: View::empty() }
    }

    // VS_BOT
    pub axiom fn vs_bot() -> (tracked out: ViewSeen)
        ensures
            out.view() == View::empty(),
    ;
}

pub struct ViewAt<T> {
    view: View,
    v: T,
}

impl<T> ViewAt<T> {
    pub closed spec fn view(&self) -> View {
        self.view
    }

    pub closed spec fn value(&self) -> T {
        self.v
    }
}

pub struct ViewJoin<T> {
    view: View,
    v: T,
}

impl<T> ViewJoin<T> {
    pub closed spec fn view(&self) -> View {
        self.view
    }

    pub closed spec fn value(&self) -> T {
        self.v
    }
}

// Non-Atomic Points-To
pub struct PrimitiveNonAtomicPointsTo<T> {
    loc: CellId,
    hist: HistorySingleton<T>,
}

impl<T> PrimitiveNonAtomicPointsTo<T> {
    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> HistorySingleton<T> {
        self.hist
    }

    pub closed spec fn timestamp(&self) -> nat {
        self.hist.timestamp()
    }

    pub closed spec fn value(&self) -> T {
        self.hist.value()
    }

    pub closed spec fn has_view(&self) -> bool {
        self.hist.has_view()
    }

    pub closed spec fn view(&self) -> View
        recommends
            self.has_view(),
    {
        self.hist.view()
    }
}

pub struct NonAtomicPointsTo<T> {
    prim: PrimitiveNonAtomicPointsTo<T>,
    seen: Option<ViewSeen>,
}

impl<T> NonAtomicPointsTo<T> {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        (!self.prim.has_view() && self.seen.is_none()) || (self.prim.view()
            == self.seen.unwrap().view())
    }

    pub closed spec fn loc(&self) -> CellId {
        self.prim.loc()
    }

    pub closed spec fn hist(&self) -> HistorySingleton<T> {
        self.prim.hist()
    }

    pub closed spec fn timestamp(&self) -> nat {
        self.prim.timestamp()
    }

    pub closed spec fn value(&self) -> T {
        self.prim.value()
    }

    pub closed spec fn has_view(&self) -> bool {
        self.seen.is_some()
    }

    pub closed spec fn view(&self) -> View
        recommends
            self.has_view(),
    {
        self.seen.unwrap().view()
    }

    // NA-AT-SW
    // todo: why are the view and the timestamp arbitrary? would it not be derived from the history in this NA points to?
    // note: I put the timestamp in the output to avoid an existential quantifier
    pub axiom fn as_atomic_points_to(tracked self) -> (tracked out: (AtomicPointsTo<T>, SingleWriter<T>, ViewSeen, nat))
        ensures
            out.0.loc() == self.loc(),
            out.0.mode() == AtomicMode::SingleWriter,
            out.1.loc() == self.loc(),
            out.0.hist() == out.1.hist(),
            out.0.hist().0 == map![out.3 => (self.value(), Some(out.2.view()))]
        ;

    // NA-AT-SW-VIEW
    pub axiom fn as_atomic_points_to_with_rsrc<P>(tracked self, tracked rsrc: P) -> (tracked out: (ViewAt<(P, AtomicPointsTo<T>, SingleWriter<T>)>, ViewSeen, nat))
        ensures
            out.0.value().0 == rsrc,
            out.0.value().1.loc() == self.loc(),
            out.0.value().1.mode() == AtomicMode::SingleWriter,
            out.0.value().2.loc() == self.loc(),
            out.0.value().1.hist() == out.0.value().2.hist(),
            out.0.value().1.hist().0 == map![out.2 => (self.value(), Some(out.1.view()))]
        ;
}

// Atomic Points-To

// AT-EXCL, AT-SW-EXCL, AT-SW-CAS-EXCL -- skip, this is taken care of by the borrow checker
// AT-CAS-CAS-FRAC-AGREE -- skip for now, we aren't modeling the timestamp
// AT-CAS-SPLIT -- skip, taken care of by borrowing
// AT-SN-UNFOLD -- skip for now, only relates to race detector info
// todo: make HistorySeen and HistorySync persistent and timeless

pub enum AtomicMode {
    Concurrent,
    SingleWriter,
    CompareAndSwap,
}

// note: skipped ghost name, single-writer timestamp
pub struct AtomicPointsTo<T> {
    mode: AtomicMode,
    loc: CellId,
    hist: History<T>,
}

impl<T> AtomicPointsTo<T> {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist.0.dom().len() > 0
    }

    pub closed spec fn mode(&self) -> AtomicMode {
        self.mode
    }

    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }

    // AT-SW-AGREE
    pub axiom fn single_writer_agree(tracked &self, tracked sw: &SingleWriter<T>)
        requires
            self.loc() == sw.loc()
        ensures
            self.hist() == sw.hist()
        ;

    // AT-CAS-FRAC-AGREE
    pub axiom fn compare_and_swap_agree(tracked &self, tracked cas: &CompareAndSwap<T>)
        requires
            self.loc() == cas.loc()
        ensures
            self.hist().contains(cas.hist())
        ;

    // AT-SN-VALID
    // there is probably an analogous rule for history sync?
    pub axiom fn history_seen_agree(tracked &self, tracked sn: &HistorySeen<T>)
        requires
            self.loc() == sn.loc()
        ensures
            self.hist().contains(sn.hist())
        ;

    // AT-SY
    // todo: I interpreted this rule as not consuming the AtomicPointsTo resource. I think this is the only way that this rule makes sense
    pub axiom fn get_history_sync(tracked &self) -> (tracked out: HistorySync<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
        ;

    // AT-NA
    // todo: I assumed that the NA points-to's history is exactly the last item in the atomic points-to's history
    pub axiom fn as_nonatomic_points_to(tracked self) -> (tracked out: (NonAtomicPointsTo<T>, ViewSeen, nat))
        ensures
            self.hist().is_max_timestamp(out.2),
            out.0.loc() == self.loc(),
            out.0.timestamp() == out.2,
            out.0.value() == self.hist().value(out.2),
            out.0.has_view() && self.hist().has_view(out.2), // todo: is this always valid to assume?
            out.0.view() == self.hist().view(out.2),
            out.1.view() == self.hist().view(out.2)
        ;

    // AT-CON-SW
    pub axiom fn concurrent_as_single_writer(tracked self) -> (tracked out: (Self, SingleWriter<T>))
        requires
            self.mode() == AtomicMode::Concurrent,
        ensures
            out.0.mode() == AtomicMode::SingleWriter,
            out.0.loc() == self.loc(),
            out.0.hist() == self.hist(),
            out.1.loc() == self.loc(),
            out.1.hist() == self.hist()
        ;

    // AT-SW-CON
    pub axiom fn single_writer_as_concurrent(tracked self, tracked sw: SingleWriter<T>) -> (tracked out: Self)
        requires
            self.mode() == AtomicMode::SingleWriter,
            self.loc() == sw.loc(),
        ensures
            out.mode() == AtomicMode::Concurrent,
            out.loc() == self.loc(),
            out.hist() == self.hist()
        ;

    // AT-CAS-SW
    pub axiom fn compare_and_swap_as_single_writer(tracked self, tracked cas: CompareAndSwap<T>) -> (tracked out: (Self, SingleWriter<T>))
        requires
            self.mode() == AtomicMode::CompareAndSwap,
            self.loc() == cas.loc(),
        ensures
            out.0.mode() == AtomicMode::SingleWriter,
            out.0.loc() == self.loc(),
            out.0.hist() == self.hist(),
            out.1.loc() == self.loc(),
            out.1.hist() == self.hist()
        ;

    // AT-SW-CAS
    pub axiom fn single_writer_as_compare_and_swap(tracked self, tracked sw: SingleWriter<T>) -> (tracked out: (Self, CompareAndSwap<T>))
        requires
            self.mode() == AtomicMode::SingleWriter,
            self.loc() == sw.loc(),
        ensures
            out.0.mode() == AtomicMode::CompareAndSwap,
            out.0.loc() == self.loc(),
            out.0.hist() == self.hist(),
            out.1.loc() == self.loc(),
            out.1.hist() == self.hist()
        ;
    
    // AT-CON-CAS |-
    pub axiom fn concurrent_as_compare_and_swap(tracked self) -> (tracked out: (Self, CompareAndSwap<T>))
        requires
            self.mode() == AtomicMode::Concurrent,
        ensures
            out.0.mode() == AtomicMode::CompareAndSwap,
            out.0.loc() == self.loc(),
            out.0.hist() == self.hist(),
            out.1.loc() == self.loc(),
            out.1.hist() == self.hist()
        ;

    // AT-CON-CAS -|
    pub axiom fn compare_and_swap_as_concurrent(tracked self, tracked cas: CompareAndSwap<T>) -> (tracked out: Self)
        requires
            self.mode() == AtomicMode::CompareAndSwap,
            self.loc() == cas.loc(),
        ensures
            out.mode() == AtomicMode::Concurrent,
            out.loc() == self.loc(),
            out.hist() == self.hist()
        ;
}

pub struct HistorySeen<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> HistorySeen<T> {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist.0.dom().len() > 0
    }

    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }

    // AT-SN-JOIN
    // todo: was there a typo in this rule?
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc()
        ensures
            out.loc() == self.loc(),
            out.hist() == self.hist().join(other.hist())
        ;

    // AT-SN-MONO
    pub axiom fn restrict(tracked self, h: History<T>) -> (tracked out: Self)
        requires
            h.0.dom().len() > 0,
            self.hist().contains(h)
        ensures
            self.loc() == out.loc(),
            out.hist() == h
        ;
}

pub struct HistorySync<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> HistorySync<T> {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist.0.dom().len() > 0
    }

    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }

    // AT-SY-SN
    pub axiom fn get_history_seen(tracked &self) -> (out: HistorySeen<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
    ;

    // AT-SY-UNFOLD
    // note: skipped view-seen with the race detector info
    pub axiom fn get_view_seen(tracked &self, timestamp: nat) -> (out: ViewSeen)
        requires
            self.hist().contains_timestamp(timestamp) && self.hist().has_view(timestamp)
        ensures
            out.view() == self.hist().view(timestamp)
        ;

    // AT-SY-JOIN
    // todo: was there a typo in this rule?
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc()
        ensures
            out.loc() == self.loc(),
            out.hist() == self.hist().join(other.hist())
        ;

    // AT-SY-MONO
    pub axiom fn restrict(tracked self, h: History<T>) -> (tracked out: Self)
        requires
            h.0.dom().len() > 0,
            self.hist().contains(h)
        ensures
            self.loc() == out.loc(),
            out.hist() == h
        ;
}

pub struct SingleWriter<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> SingleWriter<T> {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist.0.dom().len() > 0
    }

    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }

    // AT-SW-SY
    // todo: I interpreted this rule as not consuming the SingleWriter resource.
    pub axiom fn get_history_sync(tracked &self) -> (out: HistorySync<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
    ;
}

// note: skipped timestamp
pub struct CompareAndSwap<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> CompareAndSwap<T> {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist.0.dom().len() > 0
    }

    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }

    // AT-CAS-JOIN
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc()
        ensures
            out.loc() == self.loc(),
            out.hist() == self.hist().join(other.hist())
        ;
    
    // AT-CAS-SN
    // todo: I interpreted this rule as not consuming the CompareAndSwap resource.
    pub axiom fn get_history_seen(tracked &self) -> (out: HistorySeen<T>)
        ensures
            self.loc() == out.loc(),
            self.hist() == out.hist()
    ;
}


} // verus!
