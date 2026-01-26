use super::prelude::*;
use crate::cell::CellId;

verus! {

// Location = CellId
// Timestamp = nat
// "Simple" view
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
pub struct Objective<T> {
    v: T,
}

impl<T> Objective<T> {
    pub closed spec fn value(&self) -> T {
        self.v
    }
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
