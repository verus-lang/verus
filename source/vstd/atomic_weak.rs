#[cfg(feature = "weak-memory")]
pub use weak_atomic_types::*;

#[cfg(feature = "weak-memory")]
mod weak_atomic_types {

    use core::sync::atomic::{
        AtomicBool, AtomicI8, AtomicI16, AtomicI32, AtomicIsize, AtomicPtr, AtomicU8, AtomicU16,
        AtomicU32, AtomicUsize, Ordering,
    };

    #[cfg(target_has_atomic = "64")]
    use core::sync::atomic::{AtomicI64, AtomicU64};

    use super::super::cell::CellId;
    use super::super::prelude::*;
    use super::super::thread_view::*;
    use super::super::wrapping::*;

    verus! {

broadcast use crate::group_vstd_default;

#[verifier::external_body]
pub fn fence_release(Tracked(vs): Tracked<ViewSeen>) -> (rel_vs: Tracked<ReleaseViewSeen>)
    ensures
        vs.view() == rel_vs@.view(),
    opens_invariants none
    no_unwind
{
    core::sync::atomic::fence(Ordering::Release);
    Tracked::assume_new()
}

#[verifier::external_body]
pub fn fence_acquire(Tracked(acq_vs): Tracked<AcquireViewSeen>) -> (vs: Tracked<ViewSeen>)
    ensures
        acq_vs.view() == vs@.view(),
    opens_invariants none
    no_unwind
{
    core::sync::atomic::fence(Ordering::Acquire);
    Tracked::assume_new()
}

#[verifier::ext_equal]
pub ghost struct AtomicHistory<T>(pub Map<nat, (T, ThreadView)>);

impl<T> AtomicHistory<T> {
    pub open spec fn dom(&self) -> Set<nat> {
        self.0.dom()
    }

    pub open spec fn contains_timestamp(&self, timestamp: nat) -> bool {
        self.0.dom().contains(timestamp)
    }

    pub open spec fn index(&self, timestamp: nat) -> (T, ThreadView)
        recommends
            self.contains_timestamp(timestamp),
    {
        self.0.index(timestamp)
    }

    pub open spec fn value(&self, timestamp: nat) -> T
        recommends
            self.contains_timestamp(timestamp),
    {
        self.index(timestamp).0
    }

    pub open spec fn thread_view(&self, timestamp: nat) -> ThreadView
        recommends
            self.contains_timestamp(timestamp),
    {
        self.index(timestamp).1
    }

    pub open spec fn get(&self, timestamp: nat) -> Option<(T, ThreadView)> {
        self.0.get(timestamp)
    }

    pub open spec fn get_value(&self, timestamp: nat) -> Option<T> {
        match self.get(timestamp) {
            Some((val, _)) => Some(val),
            None => None,
        }
    }

    pub open spec fn get_thread_view(&self, timestamp: nat) -> Option<ThreadView> {
        match self.get(timestamp) {
            Some((_, view)) => Some(view),
            None => None,
        }
    }

    pub open spec fn insert(&self, timestamp: nat, val: T, view: ThreadView) -> Self
        recommends
            !self.contains_timestamp(timestamp),
    {
        AtomicHistory(self.0.insert(timestamp, (val, view)))
    }

    pub broadcast proof fn insert_def(&self, timestamp: nat, val: T, view: ThreadView)
        ensures
            #[trigger] self.insert(timestamp, val, view).0 == self.0.insert(timestamp, (val, view)),
    {
    }

    pub open spec fn remove(&self, timestamp: nat) -> Self {
        AtomicHistory(self.0.remove(timestamp))
    }

    pub broadcast proof fn remove_def(&self, timestamp: nat)
        ensures
            #[trigger] self.remove(timestamp).0 == self.0.remove(timestamp),
    {
    }

    pub open spec fn is_singleton(&self, timestamp: nat, val: (T, ThreadView)) -> bool {
        &&& self.contains_timestamp(timestamp)
        &&& forall|ts| #[trigger]
            self.contains_timestamp(ts) ==> ts == timestamp && self.get(ts) == Some(val)
    }

    pub open spec fn is_max_timestamp(&self, timestamp: nat) -> bool {
        &&& self.contains_timestamp(timestamp)
        &&& forall|ts| #[trigger] self.contains_timestamp(ts) ==> ts <= timestamp
    }
}

pub broadcast proof fn history_insert_contains_timestamp_cases<T>(
    h: AtomicHistory<T>,
    t: nat,
    v: T,
    o: ThreadView,
    t2: nat,
)
    requires
        #[trigger] h.insert(t, v, o).contains_timestamp(t2),
    ensures
        t == t2 || h.contains_timestamp(t2),
{
}

pub broadcast proof fn history_insert_contains_inserted_timestamp<T>(
    h: AtomicHistory<T>,
    t: nat,
    v: T,
    o: ThreadView,
)
    ensures
        (#[trigger] h.insert(t, v, o)).contains_timestamp(t),
{
}

pub broadcast proof fn history_get_contains_timestamp<T>(h: AtomicHistory<T>, t: nat)
    requires
        (#[trigger] h.get(t)).is_some(),
    ensures
        h.contains_timestamp(t),
{
}

pub broadcast proof fn history_singleton_dom_singleton<T>(
    h: AtomicHistory<T>,
    ts: nat,
    val: (T, ThreadView),
)
    requires
        #[trigger] h.is_singleton(ts, val),
    ensures
        h.0.dom().is_singleton(),
{
    assert(forall|ts1| #[trigger] h.0.dom().contains(ts1) ==> h.contains_timestamp(ts1));
    assert(forall|ts1| #[trigger] h.0.dom().contains(ts1) ==> ts1 == ts);
}

pub broadcast group group_view_history {
    group_thread_view_axioms,
    history_insert_contains_inserted_timestamp,
    history_insert_contains_timestamp_cases,
    history_get_contains_timestamp,
    history_singleton_dom_singleton,
    AtomicHistory::insert_def,
    AtomicHistory::remove_def,
    AtomicPointsTo::get_timestamp_monotonic,
    AtomicPointsTo::get_timestamp_loc,
}

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub tracked struct AtomicPointsTo<T> {
    no_copy: NoCopy,
    unused: T,
}

unsafe impl<T> Objective for AtomicPointsTo<T> {

}

impl<T> AtomicPointsTo<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> AtomicHistory<T>;

    pub uninterp spec fn get_timestamp(&self, view: ThreadView) -> Option<nat>;

    pub broadcast axiom fn get_timestamp_monotonic(&self, v1: ThreadView, v2: ThreadView)
        requires
            v1.contains(v2),
        ensures
            #![trigger self.get_timestamp(v2), v1.contains(v2)]
            #![trigger self.get_timestamp(v1), v1.contains(v2)]
            self.get_timestamp(v2).is_some() ==> {
                &&& self.get_timestamp(v1).is_some()
                &&& self.get_timestamp(v2).unwrap() <= self.get_timestamp(v1).unwrap()
            },
    ;

    pub broadcast axiom fn get_timestamp_loc(&self, other: Self, v: ThreadView)
        requires
            self.loc() == other.loc(),
        ensures
            #[trigger] self.get_timestamp(v) == #[trigger] other.get_timestamp(v),
    ;

    pub axiom fn disjoint(tracked &mut self, tracked other: &Self)
        ensures
            final(self).loc() != other.loc(),
    ;
}

/// On a load, the thread must read a timestamp no smaller than that in its old view.
/// After a load, the thread's new view will contain the timestamp that was read.
pub open spec fn load_timestamp_in_view<T>(
    pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    timestamp: nat,
) -> bool {
    &&& pt.get_timestamp(old_view).is_none() || pt.get_timestamp(old_view).unwrap() <= timestamp
    &&& pt.get_timestamp(new_view) == Some(timestamp)
}

/// On a load, the location's AtomicHistory must have included [timestamp -> (val, message_view)].
pub open spec fn load_reads_from_history<T>(
    hist: AtomicHistory<T>,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    hist.get(timestamp) == Some((val, message_view))
}

/// After a load, the thread's new view will contain the old view.
pub open spec fn load_view_nondecreasing(old_view: ThreadView, new_view: ThreadView) -> bool {
    new_view.contains(old_view)
}

pub open spec fn load_acquire<T>(
    pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& load_timestamp_in_view(pt, old_view, new_view, timestamp)
    &&& load_reads_from_history(pt.hist(), val, timestamp, message_view)
    &&& load_view_nondecreasing(
        old_view,
        new_view,
    )
    // because this is an acquire load, the message view is joined to the thread's current view
    &&& new_view.contains(message_view)
}

pub open spec fn load_relaxed<T>(
    pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    acquire_view: ThreadView,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& load_timestamp_in_view(pt, old_view, new_view, timestamp)
    &&& load_reads_from_history(pt.hist(), val, timestamp, message_view)
    &&& load_view_nondecreasing(
        old_view,
        new_view,
    )
    // because this is a relaxed load, the message view is joined to the thread's acquire view
    &&& acquire_view.contains(message_view)
}

/// On a store, the store's timestamp must be greater than that in the thread's old view.
/// After a store, the thread's new view will contain the timestamp of the store.
/// The message view for the store will also contain the timestamp of the store.
pub open spec fn store_timestamp_in_view<T>(
    old_pt: AtomicPointsTo<T>,
    new_pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    message_view: ThreadView,
    timestamp: nat,
) -> bool {
    &&& old_pt.get_timestamp(old_view).is_none() || old_pt.get_timestamp(old_view).unwrap()
        < timestamp
    &&& new_pt.get_timestamp(new_view) == Some(timestamp)
    &&& new_pt.get_timestamp(message_view) == Some(timestamp)
}

/// After a store, the thread's new view will strictly contain its old view.
/// This is a strict containment because the new view will contain the timestamp of the store.
pub open spec fn store_view_increasing(old_view: ThreadView, new_view: ThreadView) -> bool {
    &&& new_view.contains_strict(old_view)
}

/// After a store, the locations's AtomicHistory is updated to contain the store.
/// The timestamp of the store must not have previously been an entry in the location's AtomicHistory.
pub open spec fn store_insert_history<T>(
    old_pt: AtomicPointsTo<T>,
    new_pt: AtomicPointsTo<T>,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& !old_pt.hist().contains_timestamp(timestamp)
    &&& new_pt.loc() == old_pt.loc()
    &&& new_pt.hist() == old_pt.hist().insert(timestamp, val, message_view)
}

pub open spec fn store_release<T>(
    old_pt: AtomicPointsTo<T>,
    new_pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& store_timestamp_in_view(old_pt, new_pt, old_view, new_view, message_view, timestamp)
    &&& store_view_increasing(old_view, new_view)
    &&& store_insert_history(
        old_pt,
        new_pt,
        val,
        timestamp,
        message_view,
    )
    // because this is a release store, the message view is the thread's current view
    &&& message_view == new_view
}

pub open spec fn store_relaxed<T>(
    old_pt: AtomicPointsTo<T>,
    new_pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    release_view: ThreadView,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& store_timestamp_in_view(old_pt, new_pt, old_view, new_view, message_view, timestamp)
    &&& store_view_increasing(old_view, new_view)
    &&& store_insert_history(
        old_pt,
        new_pt,
        val,
        timestamp,
        message_view,
    )
    // because this is a relaxed store, the message view contains the release view
    &&& message_view.contains(
        release_view,
    )
    // and the thread's current view will now contain the message view
    &&& new_view.contains(message_view)
}

/// After a store_mut, the locations's AtomicHistory is updated to be a singleton containing only the new store.
/// The timestamp of the store must not have previously been an entry in the location's AtomicHistory.
pub open spec fn store_mut_truncate_history<T>(
    old_pt: AtomicPointsTo<T>,
    new_pt: AtomicPointsTo<T>,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& !old_pt.hist().contains_timestamp(timestamp)
    &&& new_pt.loc() == old_pt.loc()
    &&& new_pt.hist().is_singleton(timestamp, (val, message_view))
}

pub open spec fn store_mut_release<T>(
    old_pt: AtomicPointsTo<T>,
    new_pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& store_timestamp_in_view(old_pt, new_pt, old_view, new_view, message_view, timestamp)
    &&& store_view_increasing(old_view, new_view)
    &&& store_mut_truncate_history(
        old_pt,
        new_pt,
        val,
        timestamp,
        message_view,
    )
    // because this is a release store, the message view is the thread's current view
    &&& message_view == new_view
}

pub open spec fn store_mut_relaxed<T>(
    old_pt: AtomicPointsTo<T>,
    new_pt: AtomicPointsTo<T>,
    old_view: ThreadView,
    new_view: ThreadView,
    release_view: ThreadView,
    val: T,
    timestamp: nat,
    message_view: ThreadView,
) -> bool {
    &&& store_timestamp_in_view(old_pt, new_pt, old_view, new_view, message_view, timestamp)
    &&& store_view_increasing(old_view, new_view)
    &&& store_mut_truncate_history(
        old_pt,
        new_pt,
        val,
        timestamp,
        message_view,
    )
    // because this is a relaxed store, the message view contains the release view
    &&& message_view.contains(
        release_view,
    )
    // and the thread's current view will now contain the message view
    &&& new_view.contains(message_view)
}

pub ghost struct LoadData {
    pub timestamp: nat,
    pub message_view: ThreadView,
}

pub ghost struct StoreData {
    pub timestamp: nat,
    pub message_view: ThreadView,
}

pub ghost struct UpdateData {
    pub load_timestamp: nat,
    pub load_message_view: ThreadView,
    pub store_message_view: ThreadView,
    pub intermediate_thread_view: ThreadView,
}

macro_rules! make_unsigned_integer_atomic {
    ($at_ident:ident, $rust_ty: ty, $value_ty: ty, $modname:ident) => {
        atomic_types!($at_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $rust_ty, $value_ty, []);
            atomic_integer_methods!($at_ident, $rust_ty, $value_ty, $modname);
        }
    };
}

macro_rules! make_signed_integer_atomic {
    ($at_ident:ident, $rust_ty: ty, $value_ty: ty, $modname:ident) => {
        atomic_types!($at_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $rust_ty, $value_ty, []);
            atomic_integer_methods!($at_ident, $rust_ty, $value_ty, $modname);
        }
    };
}

macro_rules! make_bool_atomic {
    ($at_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        atomic_types!($at_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $rust_ty, $value_ty, []);
            atomic_bool_methods!($at_ident, $rust_ty, $value_ty);
        }
    };
}

macro_rules! atomic_types {
    ($at_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        verus! {

        #[verifier::external_body]
        pub struct $at_ident {
            ato: $rust_ty,
        }

        }
    };
}

macro_rules! atomic_common_methods {
    ($at_ident: ty, $rust_ty: ty, $value_ty: ty, [ $($addr:tt)* ]) => {
        verus_impl!{

        pub uninterp spec fn loc(&self) -> CellId;

        #[inline(always)]
        #[verifier::external_body]
        pub const fn new(i: $value_ty) -> ((ato, pt, vs, ts): (
            Self,
            Tracked<AtomicPointsTo<$value_ty>>,
            Tracked<ViewSeen>,
            Ghost<nat>,
        ))
            ensures
                ato.loc() == pt@.loc(),
                pt@.hist().is_singleton(ts@, (i, vs@@)),
                pt@.get_timestamp(vs@@) == Some(ts@)
        {
            let p = $at_ident { ato: $rust_ty::new(i) };
            (p, Tracked::assume_new(), Tracked::assume_new(), Ghost::assume_new())
        }

        #[inline(always)]
        #[verifier::external_body]
        pub const fn new_incl(i: $value_ty, Tracked(vs0) : Tracked<ViewSeen>) -> ((ato, pt, vs, ts): (
            Self,
            Tracked<AtomicPointsTo<$value_ty>>,
            Tracked<ViewSeen>,
            Ghost<nat>,
        ))
            ensures
                ato.loc() == pt@.loc(),
                pt@.hist().is_singleton(ts@, (i, vs@@)),
                pt@.get_timestamp(vs@@) == Some(ts@),
                vs@@.contains(vs0@)
        {
            let p = $at_ident { ato: $rust_ty::new(i) };
            (p, Tracked::assume_new(), Tracked::assume_new(), Ghost::assume_new())
        }

        #[inline(always)]
        #[verifier::external_body]
        #[verifier::atomic]
        pub fn load(
            &self,
            order: Ordering,
            Tracked(vs): Tracked<&mut ViewSeen>,
            Tracked(pt): Tracked<&AtomicPointsTo<$value_ty>>,
        ) -> ((val, acq_vs, ld): ($value_ty, Tracked<AcquireViewSeen>, Ghost<LoadData>))
            requires
                self.loc() == pt.loc(),
                order matches Ordering::Acquire || order matches Ordering::Relaxed
            ensures
                match order {
                    Ordering::Acquire => load_acquire(*pt, old(vs)@, final(vs)@, val, ld@.timestamp, ld@.message_view),
                    Ordering::Relaxed => load_relaxed(*pt, old(vs)@, final(vs)@, acq_vs@@, val, ld@.timestamp, ld@.message_view)
                }
            opens_invariants none
            no_unwind
        {
            return (self.ato.load(order), Tracked::assume_new(), Ghost::assume_new());
        }

        #[inline(always)]
        #[verifier::external_body]
        #[verifier::atomic]
        pub fn store(
            &self,
            v: $value_ty,
            order: Ordering,
            Tracked(vs): Tracked<&mut ViewSeen>,
            Tracked(rel_vs): Tracked<ReleaseViewSeen>,
            Tracked(pt): Tracked<&mut AtomicPointsTo<$value_ty>>,
        ) -> (st: (Ghost<StoreData>))
            requires
                self.loc() == old(pt).loc(),
                order matches Ordering::Release || order matches Ordering::Relaxed
            ensures
                match order {
                    Ordering::Release => store_release(*old(pt), *final(pt), old(vs)@, final(vs)@, v, st@.timestamp, st@.message_view),
                    Ordering::Relaxed => store_relaxed(*old(pt), *final(pt), old(vs)@, final(vs)@, rel_vs@, v, st@.timestamp, st@.message_view)
                }
            opens_invariants none
            no_unwind
        {
            self.ato.store(v, order);
            (Ghost::assume_new())
        }


        #[inline(always)]
        #[verifier::external_body]
        #[verifier::atomic]
        pub fn store_mut(
            &mut self,
            v: $value_ty,
            order: Ordering,
            Tracked(v_sn): Tracked<&mut ViewSeen>,
            Tracked(rel_v_sn): Tracked<ReleaseViewSeen>,
            Tracked(pt): Tracked<&mut AtomicPointsTo<$value_ty>>,
        ) -> (st: (Ghost<StoreData>))
            requires
                old(self).loc() == old(pt).loc(),
                order matches Ordering::Release || order matches Ordering::Relaxed
            ensures
                match order {
                    Ordering::Release => store_mut_release(*old(pt), *final(pt), old(v_sn)@, final(v_sn)@, v, st@.timestamp, st@.message_view),
                    Ordering::Relaxed => store_mut_relaxed(*old(pt), *final(pt), old(v_sn)@, final(v_sn)@, rel_v_sn@, v, st@.timestamp, st@.message_view)
                },
                final(self).loc() == old(self).loc()
            opens_invariants none
            no_unwind
        {
            self.ato.store(v, order);
            (Ghost::assume_new())
        }

        #[inline(always)]
        #[verifier::external_body]
        #[verifier::atomic]
        pub fn compare_exchange(
            &self,
            current: $value_ty,
            new: $value_ty,
            success: Ordering,
            failure: Ordering,
            Tracked(vs): Tracked<&mut ViewSeen>,
            Tracked(rel_vs): Tracked<ReleaseViewSeen>,
            Tracked(pt): Tracked<&mut AtomicPointsTo<$value_ty>>,
        ) -> ((res, acq_vs, up): (Result<$value_ty, $value_ty>, Tracked<AcquireViewSeen>, Ghost<UpdateData>))
            requires
                self.loc() == old(pt).loc(),
                success matches Ordering::AcqRel || success matches Ordering::Acquire || success matches Ordering::Release || success matches Ordering::Relaxed,
                failure matches Ordering::Acquire || failure matches Ordering::Relaxed
            ensures
                match res {
                    Ok(v) => {
                        &&& current == v
                        &&& up@.store_message_view.contains_strict(up@.load_message_view)
                        &&& match success {
                            Ordering::AcqRel => {
                                &&& load_acquire(*old(pt), old(vs)@, up@.intermediate_thread_view, current, up@.load_timestamp, up@.load_message_view)
                                &&& store_release(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, new, up@.load_timestamp + 1, up@.store_message_view)
                            },
                            Ordering::Acquire => {
                                &&& load_acquire(*old(pt), old(vs)@, up@.intermediate_thread_view, current, up@.load_timestamp, up@.load_message_view)
                                &&& store_relaxed(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, rel_vs@, new, up@.load_timestamp + 1, up@.store_message_view)
                            },
                            Ordering::Release => {
                                &&& load_relaxed(*old(pt), old(vs)@, up@.intermediate_thread_view, acq_vs@@, v, up@.load_timestamp, up@.load_message_view)
                                &&& store_release(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, new, up@.load_timestamp + 1, up@.store_message_view)
                            },
                            Ordering::Relaxed => {
                                &&& load_relaxed(*old(pt), old(vs)@, up@.intermediate_thread_view, acq_vs@@, v, up@.load_timestamp, up@.load_message_view)
                                &&& store_relaxed(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, rel_vs@, new, up@.load_timestamp + 1, up@.store_message_view)
                            }
                        }
                    },
                    Err(v) => {
                        &&& current != v
                        &&& *final(pt) == *old(pt)
                        &&& match failure {
                            Ordering::Acquire => load_acquire(*old(pt), old(vs)@, final(vs)@, v, up@.load_timestamp, up@.load_message_view),
                            Ordering::Relaxed => load_relaxed(*old(pt), old(vs)@, final(vs)@, acq_vs@@, v, up@.load_timestamp, up@.load_message_view)
                        }
                    }
                }
            opens_invariants none
            no_unwind
        {
            return (self.ato.compare_exchange(current, new, success, failure), Tracked::assume_new(), Ghost::assume_new());
        }

        // TODO - compare_exchange_weak, swap

        #[inline(always)]
        pub axiom fn truncate_history(tracked &mut self, tracked pt: &mut AtomicPointsTo<$value_ty>, tracked vs: &mut ViewSeen) -> (ts: nat)
            requires
                old(self).loc() == old(pt).loc()
            ensures
                *final(self) == *old(self),
                final(pt).loc() == old(pt).loc(),
                old(pt).hist().is_max_timestamp(ts),
                final(pt).hist().is_singleton(ts, old(pt).hist().get(ts).unwrap()),
                final(vs)@.contains(old(vs)@),
                final(pt).get_timestamp(final(vs)@) == Some(ts),
                forall |t| #[trigger] old(pt).hist().contains_timestamp(t) ==> final(vs)@.contains(old(pt).hist().thread_view(t))

            opens_invariants none
        ;

        #[inline(always)]
        #[verifier::external_body]
        pub const fn into_inner(self, Tracked(pt): Tracked<AtomicPointsTo<$value_ty>>) -> ((val, vs, ts): ($value_ty, Tracked<ViewSeen>, Ghost<nat>))
            requires
                self.loc() == pt.loc(),
            ensures
                pt.hist().is_max_timestamp(ts@),
                val == pt.hist().value(ts@),
                pt.get_timestamp(vs@@) == Some(ts@),
                forall |t| #[trigger] pt.hist().contains_timestamp(t) ==> vs@@.contains(pt.hist().thread_view(t))
            opens_invariants none
            no_unwind
        {
            (self.ato.into_inner(), Tracked::assume_new(), Ghost::assume_new())
        }

        }
    };
}

macro_rules! atomic_integer_methods {
    ($at_ident:ident, $rust_ty: ty, $value_ty: ty, $modname:ident) => {
        verus_impl!{

        // this macro is currently a stub for the functions we plan to implement:
        // TODO - fetch_add_wrapping, fetch_sub_wrapping, fetch_add, fetch_sub, fetch_and, fetch_or, fetch_xor, fetch_nand, fetch_max, fetch_min

        #[inline(always)]
        #[verifier::external_body]
        #[verifier::atomic]
        pub fn fetch_add_wrapping(
            &self,
            val: $value_ty,
            order: Ordering,
            Tracked(vs): Tracked<&mut ViewSeen>,
            Tracked(rel_vs): Tracked<ReleaseViewSeen>,
            Tracked(pt): Tracked<&mut AtomicPointsTo<$value_ty>>,
        ) -> ((v, acq_vs, up): ($value_ty, Tracked<AcquireViewSeen>, Ghost<UpdateData>))
            requires
                self.loc() == old(pt).loc(),
                order matches Ordering::AcqRel || order matches Ordering::Acquire || order matches Ordering::Release || order matches Ordering::Relaxed,
            ensures
                up@.store_message_view.contains_strict(up@.load_message_view),
                match order {
                    Ordering::AcqRel => {
                        &&& load_acquire(*old(pt), old(vs)@, up@.intermediate_thread_view, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_release(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, $modname::wrapping_add(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    },
                    Ordering::Acquire => {
                        &&& load_acquire(*old(pt), old(vs)@, up@.intermediate_thread_view, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_relaxed(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, rel_vs@, $modname::wrapping_add(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    },
                    Ordering::Release => {
                        &&& load_relaxed(*old(pt), old(vs)@, up@.intermediate_thread_view, acq_vs@@, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_release(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, $modname::wrapping_add(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    },
                    Ordering::Relaxed => {
                        &&& load_relaxed(*old(pt), old(vs)@, up@.intermediate_thread_view, acq_vs@@, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_relaxed(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, rel_vs@, $modname::wrapping_add(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    }
                },
            opens_invariants none
            no_unwind
        {
            return (self.ato.fetch_add(val, order), Tracked::assume_new(), Ghost::assume_new());
        }

        // NOTE: specifying fetch_add in the weak setting is difficult since the precondition
        // must be stated in terms of the current value, and there are several possible current values.
        // Since there is no equivalent function in Rust and we think prohibiting wrapping can be done using an invariant,
        // we defer `fetch_add` and the other non-wrapping arithmetic specs.

        #[inline(always)]
        #[verifier::external_body]
        #[verifier::atomic]
        pub fn fetch_sub_wrapping(
            &self,
            val: $value_ty,
            order: Ordering,
            Tracked(vs): Tracked<&mut ViewSeen>,
            Tracked(rel_vs): Tracked<ReleaseViewSeen>,
            Tracked(pt): Tracked<&mut AtomicPointsTo<$value_ty>>,
        ) -> ((v, acq_vs, up): ($value_ty, Tracked<AcquireViewSeen>, Ghost<UpdateData>))
            requires
                self.loc() == old(pt).loc(),
                order matches Ordering::AcqRel || order matches Ordering::Acquire || order matches Ordering::Release || order matches Ordering::Relaxed,
            ensures
                up@.store_message_view.contains_strict(up@.load_message_view),
                match order {
                    Ordering::AcqRel => {
                        &&& load_acquire(*old(pt), old(vs)@, up@.intermediate_thread_view, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_release(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, $modname::wrapping_sub(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    },
                    Ordering::Acquire => {
                        &&& load_acquire(*old(pt), old(vs)@, up@.intermediate_thread_view, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_relaxed(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, rel_vs@, $modname::wrapping_sub(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    },
                    Ordering::Release => {
                        &&& load_relaxed(*old(pt), old(vs)@, up@.intermediate_thread_view, acq_vs@@, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_release(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, $modname::wrapping_sub(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    },
                    Ordering::Relaxed => {
                        &&& load_relaxed(*old(pt), old(vs)@, up@.intermediate_thread_view, acq_vs@@, v, up@.load_timestamp, up@.load_message_view)
                        &&& store_relaxed(*old(pt), *final(pt), up@.intermediate_thread_view, final(vs)@, rel_vs@, $modname::wrapping_sub(v, val), up@.load_timestamp + 1, up@.store_message_view)
                    }
                },
            opens_invariants none
            no_unwind
        {
            return (self.ato.fetch_sub(val, order), Tracked::assume_new(), Ghost::assume_new());
        }

        }
    };
}

macro_rules! atomic_bool_methods {
    ($at_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        verus!{

        // this macro is currently a stub for the functions we plan to implement:
        // TODO - fetch_and, fetch_or, fetch_xor, fetch_nand

        }
    };
}

make_bool_atomic!(PAtomicWeakBool, AtomicBool, bool);

make_unsigned_integer_atomic!(PAtomicWeakU8, AtomicU8, u8, u8_specs);

make_unsigned_integer_atomic!(PAtomicWeakU16, AtomicU16, u16, u16_specs);

make_unsigned_integer_atomic!(PAtomicWeakU32, AtomicU32, u32, u32_specs);

#[cfg(target_has_atomic = "64")]
make_unsigned_integer_atomic!(PAtomicWeakU64, AtomicU64, u64, u64_specs);

make_unsigned_integer_atomic!(PAtomicWeakUsize, AtomicUsize, usize, usize_specs);

make_signed_integer_atomic!(PAtomicWeakI8, AtomicI8, i8, i8_specs);

make_signed_integer_atomic!(PAtomicWeakI16, AtomicI16, i16, i16_specs);

make_signed_integer_atomic!(PAtomicWeakI32, AtomicI32, i32, i32_specs);

#[cfg(target_has_atomic = "64")]
make_signed_integer_atomic!(PAtomicWeakI64, AtomicI64, i64,i64_specs);

make_signed_integer_atomic!(PAtomicWeakIsize, AtomicIsize, isize, isize_specs);

// TODO - AtomicPtr
} // verus!
}
