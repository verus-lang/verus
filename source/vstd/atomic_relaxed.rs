use super::prelude::*;
use crate::cell::CellId;

verus! {

// Location = CellId
// Timestamp = nat
/// Represents "simple" view
pub struct View(Map<CellId, nat>);

pub struct History<T>(Map<nat, (T, Option<View>)>);

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
