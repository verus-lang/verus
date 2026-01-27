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
    // todo: we could make this opaque if unfolding this definition is required very often
    pub open spec fn contains(&self, other: Self) -> bool {
        forall|l| #[trigger]
            self.0.dom().contains(l) ==> {
                &&& other.0.dom().contains(l)
                &&& self.0[l] <= other.0[l]
            }
    }
}

pub struct History<T>(pub Map<nat, (T, Option<View>)>);

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
    pub v: T,
}

impl<T> Release<T> {
    pub closed spec fn value(&self) -> T {
        self.v
    }
}

pub struct Acquire<T> {
    pub v: T,
}

impl<T> Acquire<T> {
    pub closed spec fn value(&self) -> T {
        self.v
    }
}

#[verifier::external_body]
pub fn rel_fence<T>(Tracked(rsrc): Tracked<T>) -> (out: Tracked<Release<T>>)
    ensures
        rsrc == out@.v,
{
    core::sync::atomic::fence(Ordering::Release);
    Tracked(Release { v: rsrc })
}

#[verifier::external_body]
pub fn acq_fence<T>(Tracked(rsrc): Tracked<Acquire<T>>) -> (out: Tracked<T>)
    ensures
        out@ == rsrc.v,
{
    core::sync::atomic::fence(Ordering::Acquire);
    Tracked(rsrc.v)
}

pub axiom fn rel_fence_elim<T>(tracked rsrc: Release<T>) -> (tracked out: T)
    ensures
        out == rsrc.v,
;

pub axiom fn acq_fence_intro<T>(tracked rsrc: T) -> (tracked out: Acquire<T>)
    ensures
        out.v == rsrc,
;

// implied by rel_fence_elim
pub proof fn relmod_ghost<P: PCM>(tracked rsrc: Release<Resource<P>>) -> (tracked out: Resource<P>)
    ensures
        out == rsrc.v,
{
    rel_fence_elim(rsrc)
}

pub axiom fn acqmod_ghost<P: PCM>(tracked rsrc: Acquire<Resource<P>>) -> (tracked out: Resource<P>)
    ensures
        out == rsrc.v,
;

pub axiom fn ghost_relmod<P: PCM>(tracked rsrc: Resource<P>) -> (tracked out: Release<Resource<P>>)
    ensures
        out.v == rsrc,
;

// implied by acq_fence_intro
pub proof fn ghost_acqmod<P: PCM>(tracked rsrc: Resource<P>) -> (tracked out: Acquire<Resource<P>>)
    ensures
        out.v == rsrc,
{
    acq_fence_intro(rsrc)
}

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

pub proof fn relmod_mono<T1, T2, E: Entails<T1, T2>>(
    tracked rsrc: Release<T1>,
    to: T2,
) -> (tracked out: Release<T2>)
    ensures
        out.v == to,
{
    let tracked v2 = E::entails(rsrc.v, to);
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

pub proof fn relmod_or<P, Q>(tracked rsrc: Release<Or<P, Q>>) -> (tracked out: Or<
    Release<P>,
    Release<Q>,
>)
    ensures
        out == match rsrc.v {
            Or::Left(p) => Or::Left(Release { v: p }),
            Or::Right(q) => Or::Right(Release { v: q }),
        },
{
    match rsrc.v {
        Or::Left(p) => Or::Left(Release { v: p }),
        Or::Right(q) => Or::Right(Release { v: q }),
    }
}

// NOTE skipping RELMOD-FORALL and RELMOD-EXIST for now
pub proof fn relmod_sep1<P, Q>(tracked rsrc: Release<(P, Q)>) -> (tracked out: (
    Release<P>,
    Release<Q>,
))
    ensures
        out == (Release { v: rsrc.v.0 }, Release { v: rsrc.v.1 }),
{
    (Release { v: rsrc.v.0 }, Release { v: rsrc.v.1 })
}

pub proof fn relmod_sep2<P, Q>(tracked rsrc: (Release<P>, Release<Q>)) -> (tracked out: Release<
    (P, Q),
>)
    ensures
        out == (Release { v: (rsrc.0.v, rsrc.1.v) }),
{
    Release { v: (rsrc.0.v, rsrc.1.v) }
}

// NOTE The specs seem weak
pub proof fn relmod_wand<P, Q>(
    tracked rsrc: Release<proof_fn[Once](tracked p: P) -> tracked Q>,
) -> (tracked out: proof_fn[Once](tracked p: Release<P>) -> tracked Release<Q>) {
    let tracked f = rsrc.v;
    let tracked f2 = proof_fn[Once] |tracked p: Release<P>| -> (tracked q: Release<Q>)
        requires
            f.requires((p.v,)),
        {
            let tracked v2 = f(p.v);
            Release { v: v2 }
        };
    f2
}

// NOTE skipping RELMOD-LATER-INTRO and RELMOD-UNOPS
// TODO acquire modality monotonicity, and, or, wand, sep1, sep2
// Objective modality
/// This trait should be implemented on types P such that objective(P) holds
pub unsafe trait IsObjective {

}

/// Represents objective modality: <obj>(P)
pub struct Objective<T> {
    v: T,
}

// GHOST-OBJ - todo: what ghost state can be marked IsObjective?
// todo: for the rules below, I am not sure what their Verus equivalent is
// i.e., how would you have a tracked "pure" thing? what about a tracked forall?
// PURE-OBJ
// TRUE-OBJ
// FALSE-OBJ
// OBJ-BOPS
// OBJ-UOPS
// OBJ-FORALL
// OBJ-EXISTS
// implement IsObjective on primitive types and their compositions (i.e. tuples)
// todo: could we support automatically implementing IsObjective on structs and enums whose fields all satisfy IsObjective?
macro_rules! declare_primitive_is_objective {
    ($($a:ty),*) => {
        verus! {
            $(unsafe impl IsObjective for $a {})*
        }
    }
}

declare_primitive_is_objective!(bool, char, (), u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, int, nat, str);

macro_rules! declare_generic_primitive_is_objective {
    ($($t: ident $a:ty),*) => {
        verus! {
            $(unsafe impl<$t: IsObjective> IsObjective for $a {})*
        }
    }
}

// todo: verifier currently does not support &mut T
declare_generic_primitive_is_objective!(T [T], T &T, T *mut T, T *const T);

unsafe impl<T: IsObjective, const N: usize> IsObjective for [T; N] {

}

macro_rules! declare_tuple_is_objective {
    ($($($a:ident)*),*) => {
        verus! {
            $(unsafe impl<$($a: IsObjective, )*> IsObjective for ($($a, )*) {})*
        }
    }
}

// could declare for longer tuples as well
declare_tuple_is_objective!(T0, T0 T1, T0 T1 T2, T0 T1 T2 T3);

// OBJ-OBJ
unsafe impl<T> IsObjective for Objective<T> {

}

impl<T: IsObjective> Objective<T> {
    // OBJMOD-INTRO
    pub axiom fn new(tracked v: T) -> (tracked obj: Objective<T>)
        ensures
            obj.value() == v,
    ;
}

impl<T> Objective<T> {
    pub closed spec fn value(&self) -> T {
        self.v
    }

    // OBJMOD-ELIM
    pub axiom fn to_inner(tracked self) -> (tracked v: T)
        ensures
            self.value() == v,
    ;

    // OBJMOD-MONO - how to represent P |- Q ?
    // OBJMOD-AND - how would you have something of type Objective <P /\ Q> ?
    // OBJMOD-OR -  how would you have something of type Objective<P \/ Q> ?
    // OBJMOD-FORALL - how would you have something of type Objective<forall x ...> ?
    // OBJMOD-EXIST - how would you have something of type Objective<exists x ...> ?
    // OBJMOD-SEP -|
    pub axiom fn join<U>(tracked self, tracked u: Objective<U>) -> (tracked out: Objective<(T, U)>)
        ensures
            self.value() == out.value().0,
            u.value() == out.value().1,
    ;

    // OBJMOD-RELMOD-INTRO
    pub axiom fn as_release(tracked self) -> (tracked out: Release<T>)
        ensures
            self.value() == out.value(),
    ;

    // RELMOD-OBJMOD-ELIM
    pub axiom fn from_release(tracked r: Release<Objective<T>>) -> (tracked out: Self)
        ensures
            r.value() == out,
    ;

    // OBJMOD-ACQMOD-INTRO
    pub axiom fn as_acquire(tracked self) -> (tracked out: Acquire<T>)
        ensures
            self.value() == out.value(),
    ;

    // ACQMOD-OBJMOD-ELIM
    pub axiom fn from_acquire(tracked a: Acquire<Objective<T>>) -> (tracked out: Self)
        ensures
            a.value() == out,
    ;
}

impl<T, U> Objective<(T, U)> {
    // OBJMOD-SEP |-
    pub axiom fn split(tracked self) -> (tracked out: (Objective<T>, Objective<U>))
        ensures
            self.value().0 == out.0.value(),
            self.value().1 == out.1.value(),
    ;
}

// Explicit views
pub struct ViewSeen {
    view: View,
}

impl ViewSeen {
    pub closed spec fn view(&self) -> View {
        self.view
    }
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

// invariant:
// views match
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
}

// Atomic Points-To
pub enum AtomicMode {
    Concurrent,
    SingleWriter,
    CompareAndSwap,
}

// note: skipped ghost name, single-writer timestamp
// todo: type invariant that history is non empty
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
}

pub struct HistorySeen<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> HistorySeen<T> {
    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }
}

pub struct HistorySync<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> HistorySync<T> {
    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }
}

pub struct SingleWriter<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> SingleWriter<T> {
    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }
}

// note: skipped timestamp
pub struct CompareAndSwap<T> {
    loc: CellId,
    hist: History<T>,
}

impl<T> CompareAndSwap<T> {
    pub closed spec fn loc(&self) -> CellId {
        self.loc
    }

    pub closed spec fn hist(&self) -> History<T> {
        self.hist
    }
}

} // verus!
