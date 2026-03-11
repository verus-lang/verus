use crate::prelude::*;
use crate::cell::CellId;
use crate::pcm::*;
use core::sync::atomic::Ordering;
use std::marker::PhantomData;
use std::sync::atomic::*;

verus! {

broadcast use crate::group_vstd_default;

// Location = CellId
// Timestamp = nat
/// Represents "simple" view
#[verifier::ext_equal]
pub ghost struct View(pub Map<CellId, nat>);

impl View {
    /// True when `other` is contained in this View
    #[verifier::opaque]
    pub open spec fn contains(self, other: Self) -> bool {
        &&& other.0.dom().subset_of(self.0.dom())
        &&& forall |k| 
            #![trigger self.0.dom().contains(k)]
            #![trigger other.0.dom().contains(k)]
            self.0.dom().contains(k) ==> !other.0.dom().contains(k) || (other.0.dom().contains(k) && other.0[k] <= self.0[k])
    }

    pub open spec fn contains_loc(self, loc: CellId) -> bool {
        self.0.dom().contains(loc)
    }

    pub open spec fn get_timestamp(self, loc: CellId) -> nat
        recommends self.contains_loc(loc),
    {
        self.0.index(loc)
    }

    pub open spec fn contains_strict(self, other: Self) -> bool {
        &&& self.contains(other)
        &&& self != other
    }

    pub broadcast proof fn contains_and_contains_strict(v1: View, v2: View, v3: View)
        ensures
            #[trigger] v1.contains_strict(v2) && #[trigger] v2.contains(v3) ==> v1.contains_strict(v3)
    {
        admit(); // todo
    }

    #[verifier::opaque]
    pub open spec fn join(self, other: Self) -> Self {
        View(
            Map::new(
                |k: CellId| self.0.dom().contains(k) || other.0.dom().contains(k),
                |k: CellId|
                    if self.0.dom().contains(k) {
                        if other.0.dom().contains(k) {
                            if self.0[k] >= other.0[k] {
                                self.0[k]
                            } else {
                                other.0[k]
                            }
                        } else {
                            self.0[k]
                        }
                    } else {
                        other.0[k]
                    },
            ),
        )
    }

    pub open spec fn empty() -> Self {
        Self(Map::<CellId, nat>::empty())
    }

    pub open spec fn singleton(loc: CellId, timestamp: nat) -> Self {
        Self(map![loc => timestamp])
    }
}

pub ghost struct History<T>(pub Map<nat, (T, Option<View>)>);

impl<T> History<T> {
    /// True when `other` is contained in this History
    #[verifier::opaque]
    pub open spec fn contains(self, other: Self) -> bool {
        other.0.submap_of(self.0)
    }

    #[verifier::opaque]
    pub open spec fn agrees(self, other: Self) -> bool {
        self.0.agrees(other.0)
    }

    // history join assumes that all histories agree
    // this should be true for any assertions that we have about the history of a given location
    #[verifier::opaque]
    pub open spec fn join(self, other: Self) -> History<T>
        recommends
            self.agrees(other) || other.agrees(self),
    {
        History(self.0.union_prefer_right(other.0))
    }

    pub open spec fn contains_timestamp(&self, timestamp: nat) -> bool {
        self.0.dom().contains(timestamp)
    }

    pub open spec fn is_max_timestamp(&self, timestamp: nat) -> bool {
        &&& self.contains_timestamp(timestamp)
        &&& forall|t| #[trigger] self.contains_timestamp(t) ==> t <= timestamp
    }

    pub open spec fn max_timestamp(&self) -> nat
        recommends
            self.0.len() > 0,
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
            self.contains_timestamp(timestamp),
    {
        self.0[timestamp].1.is_some()
    }

    pub open spec fn view(&self, timestamp: nat) -> View
        recommends
            self.has_view(timestamp),
    {
        self.0[timestamp].1.unwrap()
    }

    pub open spec fn value(&self, timestamp: nat) -> T
        recommends
            self.contains_timestamp(timestamp),
    {
        self.0[timestamp].0
    }
}

pub broadcast proof fn view_contains_refl(v: View)
    ensures
        #[trigger] v.contains(v)
{
    reveal(View::contains);
}

pub broadcast proof fn view_contains_anti_sym(v1: View, v2: View)
    requires
        #[trigger] v1.contains(v2),
        v1 != v2
    ensures
        !(#[trigger] v2.contains(v1))
{
    reveal(View::contains);
    if (v1.contains(v2) && v1 != v2) {
        if (!(v1.0.dom() =~= v2.0.dom())) {
            assert forall|k| #[trigger] v2.0.dom().contains(k) implies v1.0.dom().contains(k) by {}
            assert(!v2.contains(v1));
        } else {
            assert(v1.0.dom() =~= v2.0.dom());
            assert(!(v1 =~= v2));
        }
    }
}

pub broadcast proof fn view_contains_trans(v1: View, v2: View, v3: View)
    requires
        #[trigger] v1.contains(v2),
        #[trigger] v2.contains(v3)
    ensures
        #[trigger] v1.contains(v3)
{
    reveal(View::contains);
}

pub broadcast proof fn view_join_assoc(v1: View, v2: View, v3: View)
    ensures
        #[trigger] v1.join(v2.join(v3)) =~= #[trigger] v1.join(v2).join(v3)
{
    reveal(View::contains);
    reveal(View::join);
    assert(v1.join(v2.join(v3)).0 =~= v1.join(v2).join(v3).0);
}

pub broadcast proof fn view_join_comm(v1: View, v2: View)
    ensures
        #[trigger] v1.join(v2) =~= v2.join(v1)
{
    reveal(View::contains);
    reveal(View::join);
    assert(v1.join(v2).0 =~= v2.join(v1).0);
}

pub broadcast proof fn view_join_idemp(v: View)
    ensures
        #[trigger] v.join(v) =~= v
{
    reveal(View::join);
    assert(v.join(v).0 =~= v.0);
}

pub broadcast proof fn view_join_contains(v1: View, v2: View)
    ensures
        #[trigger] v1.join(v2).contains(v1)
{
    reveal(View::contains);
    reveal(View::join);
}

pub broadcast proof fn history_contains_refl<T>(h: History<T>)
    ensures
        #[trigger] h.contains(h)
{
    reveal(History::contains);
}

pub broadcast proof fn history_contains_anti_sym<T>(h1: History<T>, h2: History<T>)
    requires
        #[trigger] h1.contains(h2),
        h1 != h2
    ensures
        !(#[trigger] h2.contains(h1))
{
    reveal(History::contains);
    if (!(h1.0.dom() =~= h2.0.dom())) {
        assert forall|k| #[trigger] h2.0.dom().contains(k) implies h1.0.dom().contains(k) by {}
        assert(!h2.contains(h1));
    } else {
        assert(h1.0.dom() =~= h2.0.dom());
        assert(!(h1.0 =~= h2.0));
    }
}

pub broadcast proof fn history_contains_trans<T>(h1: History<T>, h2: History<T>, h3: History<T>)
    requires
        #[trigger] h1.contains(h2),
        #[trigger] h2.contains(h3),
    ensures
        #[trigger] h1.contains(h3)
{
    reveal(History::contains);
    assert forall |k: nat| #[trigger] h3.0.dom().contains(k) implies #[trigger] h1.0.dom().contains(k) && h3.0[k] == h1.0[k] by {
        assert(h2.0.dom().contains(k));
        assert(h1.0.dom().contains(k));
    }
}

pub broadcast proof fn history_join_assoc<T>(h1: History<T>, h2: History<T>, h3: History<T>)
    requires
        h1.agrees(h2),
        h2.agrees(h3),
        h1.agrees(h3)
    ensures
        #[trigger] h1.join(h2.join(h3)) =~= #[trigger] h1.join(h2).join(h3)
{
    reveal(History::agrees);
    reveal(History::join);
    assert(h1.join(h2.join(h3)).0 =~= h1.join(h2).join(h3).0);
}

pub broadcast proof fn history_join_comm<T>(h1: History<T>, h2: History<T>)
    requires
        h1.agrees(h2)
    ensures
        #[trigger] h1.join(h2) =~= h2.join(h1)
{
    reveal(History::agrees);
    reveal(History::join);
    assert(h1.join(h2).0 =~= h2.join(h1).0);
}

pub broadcast proof fn history_join_idemp<T>(h: History<T>)
    ensures
        #[trigger] h.join(h) =~= h
{
    reveal(History::join);
    assert(h.join(h).0 =~= h.0);
}

pub broadcast proof fn history_join_contains<T>(h1: History<T>, h2: History<T>)
    requires
        h1.agrees(h2)
    ensures
        #![trigger h1.join(h2).contains(h1)]
        #![trigger h1.join(h2).contains(h2)] 
        h1.join(h2).contains(h1),
        h1.join(h2).contains(h2)
{
    reveal(History::agrees);
    reveal(History::contains);
    reveal(History::join);
}

pub broadcast proof fn history_agrees_refl<T>(h: History<T>)
    ensures
        #[trigger] h.agrees(h)
{
    reveal(History::agrees);
}

pub broadcast proof fn history_agrees_sym<T>(h1: History<T>, h2: History<T>)
    requires
        #[trigger] h1.agrees(h2)
    ensures
        #[trigger] h2.agrees(h1)
{
    reveal(History::agrees);
}

pub broadcast proof fn history_agrees_singleton_distinct<T>(t1: nat, v1: T, o1: Option<View>, t2: nat, v2: T, o2: Option<View>)
    requires
        t1 != t2
    ensures
        #[trigger] History::singleton(t1, v1, o1).agrees(History::singleton(t2, v2, o2))
{
    reveal(History::agrees);
}

pub broadcast proof fn history_contains_singleton_distinct<T>(h: History<T>, t1: nat, v1: T, o1: Option<View>, t2: nat, v2: T, o2: Option<View>)
    requires
        #[trigger] h.contains(History::singleton(t1, v1, o1)),
        #[trigger] h.contains(History::singleton(t2, v2, o2)),
        v1 != v2
    ensures
        t1 != t2
{
    reveal(History::contains);
    assert(History::singleton(t1, v1, o1).0.dom().contains(t1));
    assert(History::singleton(t2, v2, o2).0.dom().contains(t2));
    assert(h.0.dom().contains(t1) && h.0.dom().contains(t2));
    assert(h.0[t1] == (v1, o1));
    assert(h.0[t2] == (v2, o2));
}

pub broadcast proof fn history_singleton_eq<T>(t1: nat, v1: T, o1: Option<View>, t2: nat, v2: T, o2: Option<View>)
    requires
        #[trigger] History::singleton(t1, v1, o1).contains(History::singleton(t2, v2, o2))
    ensures
        t1 == t2, 
        v1 == v2,
        o1 == o2
{
    admit();
}

pub broadcast proof fn history_contains_join_singleton_eq<T>(h: History<T>, t1: nat, v1: T, o1: Option<View>, t2: nat, v2: T, o2: Option<View>, t3: nat, v3: T, o3: Option<View>)
    requires
        #[trigger] h.contains(History::singleton(t1, v1, o1)),
        #[trigger] h.contains(History::singleton(t2, v2, o2)),
        h == #[trigger] History::singleton(t1, v1, o1).join(History::singleton(t3, v3, o3)),
        History::singleton(t1, v1, o1) != History::singleton(t2, v2, o2)
    ensures
        t2 == t3,
        v2 == v3,
        o2 == o3
{
    reveal(History::contains);
    reveal(History::join);
    admit(); // todo
}

pub broadcast proof fn history_contains_distinct<T>(h1: History<T>, h2: History<T>, h3: History<T>)
    requires
        #[trigger] h1.contains(h2),
        #[trigger] h1.contains(h3),
        h2 != h3
    ensures
        h1 != h2
{
    reveal(History::contains);
    admit(); // todo
}

pub broadcast proof fn history_not_contains_max_timestamp<T>(h: History<T>, t: nat)
    requires
        h.max_timestamp() < t
    ensures
        !(#[trigger] h.contains_timestamp(t))
{
    admit();
}

pub broadcast proof fn history_agrees_singleton_new_timestamp<T>(h: History<T>, t: nat, v: T, o: Option<View>)
    requires
        !h.contains_timestamp(t)
    ensures
        #[trigger] h.agrees(History::singleton(t, v, o))
{
    admit();
}

pub broadcast group group_view_history {
    view_contains_refl,
    view_contains_anti_sym,
    view_contains_trans,
    view_join_assoc,
    view_join_comm,
    view_join_idemp,
    view_join_contains,
    history_contains_refl,
    history_contains_anti_sym,
    history_contains_trans,
    history_join_assoc,
    history_join_comm,
    history_join_idemp,
    history_join_contains,
    history_agrees_refl,
    history_agrees_sym,
    history_singleton_eq,
    history_agrees_singleton_distinct,
    history_contains_singleton_distinct,
    history_contains_join_singleton_eq,
    history_contains_distinct,
    history_not_contains_max_timestamp,
    history_agrees_singleton_new_timestamp,
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
    v: T
}

impl<T> Release<T> {
    pub uninterp spec fn value(&self) -> T;
}

pub tracked struct Acquire<T> {
    v: T
}

impl<T> Acquire<T> {
    pub uninterp spec fn value(&self) -> T;
}

// Note 8.11
unsafe impl<T> Objective for Release<T> {

}

unsafe impl<T> Objective for Acquire<T> {

}

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
        f.value().requires((rsrc.value(),)),
    ensures
        f.value().ensures((rsrc.value(),), out.value()),
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
        f.value().requires((rsrc.value(),)),
    ensures
        f.value().ensures((rsrc.value(),), out.value()),
;

// Objective
/// This trait should be implemented on types P such that objective(P) holds
pub unsafe trait Objective {

}

// GHOST-OBJ
// todo: what other ghost state can be marked Objective?
unsafe impl<P: PCM> Objective for Resource<P> {

}

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
unsafe impl<'a, P: Objective, Q: Objective, F: ProofFnOnce> Objective for proof_fn<'a, F>(
    tracked p: P,
) -> tracked Q {

}

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
#[verifier::external_body]
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
            self.view() == v1.join(v2),
        ensures
            out.0.view() == v1,
            out.1.view() == v2,
    ;

    // VS-JOIN -|
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        ensures
            out.view() == self.view().join(other.view()),
    ;

    // VS-MONO
    pub axiom fn restrict(tracked self, v: View) -> (tracked out: Self)
        requires
            self.view().contains(v),
        ensures
            out.view() == v,
    ;
}

#[derive(Clone, Copy)]
pub tracked struct EmptyViewSeen;

unsafe impl Objective for EmptyViewSeen {

}

impl EmptyViewSeen {
    pub axiom fn from_view_seen(tracked v: ViewSeen) -> (tracked out: Self)
        requires
            v.view() == View::empty(),
    ;

    pub axiom fn as_view_seen(tracked self) -> (tracked out: ViewSeen)
        ensures
            out.view() == View::empty(),
    ;
}

// ViewAt<T> is persistent when T is persistent
// the #[derive] attribute will ensure that ViewAt<T>: Copy only when T: Copy
#[derive(Copy)]
pub tracked struct ViewAt<T> {
    v: T
}

impl<T: Clone> Clone for ViewAt<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

unsafe impl<T> Objective for ViewAt<T> {

}

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
    pub axiom fn new_incl(tracked t: T, tracked sn: ViewSeen) -> (tracked out: (Self, ViewSeen))
        ensures
            out.0.value() == t,
            out.0.view() == out.1.view(),
            out.1.view().contains(sn.view()),
    ;

    // VA-ELIM
    pub axiom fn into_inner(tracked self, tracked sn: ViewSeen) -> (tracked out: T)
        requires
            self.view() == sn.view(),  // could be sn.view().contains(self.view())

        ensures
            out == self.value(),
    ;

    // this is encoding view monotonicity
    pub axiom fn weaken(tracked self, v: View) -> (tracked out: Self)
        requires
            v.contains(self.view()),
        ensures
            out.view() == v,
            out.value() == self.value(),
    ;

    // VA-MONO, VA-WAND, VA-UNOPS with update -- we are encoding all of these as the below rule.
    // strictly speaking, this rule models a wand update.
    pub axiom fn apply_fn<U>(
        tracked self,
        tracked f: ViewAt<proof_fn[Once](tracked v1: T) -> tracked U>,
    ) -> (tracked out: ViewAt<U>)
        requires
            f.value().requires((self.value(),)),
            f.view() == self.view(),
        ensures
            f.value().ensures((self.value(),), out.value()),
            out.view() == self.view(),
    ;
}

impl<T: Objective> ViewAt<T> {
    // VA-OBJ |-
    pub axiom fn new_objective(tracked t: T) -> (tracked out: Self)
        ensures
            out.value() == t,
    ;

    // VA-OBJ -|
    pub axiom fn into_inner_objective(tracked self) -> (tracked out: T)
        ensures
            out == self.value(),
    ;
}

#[derive(Copy)]
pub tracked struct ViewJoin<T> {
    v: T
}

impl<T: Clone> Clone for ViewJoin<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

unsafe impl<T> Objective for ViewJoin<T> {

}

// I am skipping a lot of rules for now. If we don't use raw invariants, I am not sure how much we will use view joins
// skip - VJ-JOIN, VA-VJ, VJ-VA, VJ-VA-ACC, VJ-BOPS (including wand), VJ-UNOPS
impl<T> ViewJoin<T> {
    pub uninterp spec fn view(&self) -> View;

    pub uninterp spec fn value(&self) -> T;

    // this is encoding view monotonicity
    pub axiom fn weaken(tracked self, v: View) -> (tracked out: Self)
        requires
            v.contains(self.view()),
        ensures
            out.view() == v,
            out.value() == self.value(),
    ;

    // VJ-INTRO-NOW
    pub axiom fn new(tracked t: T) -> (tracked out: Self)
        ensures
            out.value() == t,
    ;

    // this is kind of like VJ-UNFOLD |-
    // this isn't an exact encoding, but perhaps this would work fine in practice
    pub proof fn new_incl(tracked t: T, tracked sn: ViewSeen) -> (tracked out: Self)
        ensures
            out.value() == t,
            out.view().contains(sn.view()),
    {
        let tracked (at, _) = ViewAt::new_incl(t, sn);
        Self::from_view_at(at)
    }

    // VJ-ELIM
    // this is kind of also encoding VJ-UNFOLD -|, but not exactly
    pub axiom fn into_inner(tracked self, tracked sn: ViewSeen) -> (tracked out: T)
        requires
            self.view() == sn.view(),
        ensures
            out == self.value(),
    ;

    // VA-TO-VJ
    pub axiom fn from_view_at(tracked at: ViewAt<T>) -> (tracked out: Self)
        ensures
            out.view() == at.view(),
            out.value() == at.value(),
    ;

    // VJ-ELIM-VA
    pub axiom fn as_view_at(tracked self, tracked sn: ViewSeen) -> (tracked out: (
        ViewSeen,
        ViewAt<T>,
    ))
        ensures
            out.0.view().contains(sn.view()),
            out.1.view() == out.0.view().join(self.view()),
            out.1.value() == self.value(),
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
    v: T
}

unsafe impl<T> Objective for AtomicPointsTo<T> {}

impl<T> AtomicPointsTo<T> {
    pub uninterp spec fn mode(&self) -> AtomicMode;

    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> History<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist().0.len() > 0
    }

    // AT-EXCL
    pub axiom fn excl(tracked &mut self, tracked other: &Self)
        ensures
            self.loc() != other.loc(),
    ;

    // AT-SW-AGREE
    pub axiom fn single_writer_agree(tracked &self, tracked sw: &SingleWriter<T>)
        requires
            self.loc() == sw.loc(),
        ensures
            self.mode() == AtomicMode::SingleWriter,
            self.hist() == sw.hist(),
    ;

    // AT-CAS-FRAC-AGREE
    pub axiom fn compare_and_swap_agree(tracked &self, tracked cas: &CompareAndSwap<T>)
        requires
            self.loc() == cas.loc(),
        ensures
            self.mode() != AtomicMode::Concurrent,
            self.hist().contains(cas.hist()),
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
            out.hist() == self.hist(),
    ;

    // AT-SW-CON
    pub axiom fn single_writer_as_concurrent(tracked &mut self, tracked sw: SingleWriter<T>)
        requires
            old(self).mode() == AtomicMode::SingleWriter,
            old(self).loc() == sw.loc(),
        ensures
            self.mode() == AtomicMode::Concurrent,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
    ;

    // AT-CAS-SW
    pub axiom fn compare_and_swap_as_single_writer(
        tracked &mut self,
        tracked cas: CompareAndSwap<T>,
    ) -> (tracked out: SingleWriter<T>)
        requires
            old(self).mode() == AtomicMode::CompareAndSwap,
            old(self).loc() == cas.loc(),
        ensures
            self.mode() == AtomicMode::SingleWriter,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
            out.loc() == self.loc(),
            out.hist() == self.hist(),
    ;

    // AT-SW-CAS
    pub axiom fn single_writer_as_compare_and_swap(
        tracked &mut self,
        tracked sw: SingleWriter<T>,
    ) -> (tracked out: CompareAndSwap<T>)
        requires
            old(self).mode() == AtomicMode::SingleWriter,
            old(self).loc() == sw.loc(),
        ensures
            self.mode() == AtomicMode::CompareAndSwap,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
            out.loc() == self.loc(),
            out.hist() == self.hist(),
    ;

    // AT-CON-CAS |-
    pub axiom fn concurrent_as_compare_and_swap(tracked &mut self) -> (tracked out: CompareAndSwap<
        T,
    >)
        requires
            old(self).mode() == AtomicMode::Concurrent,
        ensures
            self.mode() == AtomicMode::CompareAndSwap,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
            out.loc() == self.loc(),
            out.hist() == self.hist(),
    ;

    // AT-CON-CAS -|
    pub axiom fn compare_and_swap_as_concurrent(tracked &mut self, tracked cas: CompareAndSwap<T>)
        requires
            old(self).mode() == AtomicMode::CompareAndSwap,
            old(self).loc() == cas.loc(),
        ensures
            self.mode() == AtomicMode::Concurrent,
            self.loc() == old(self).loc(),
            self.hist() == old(self).hist(),
    ;
}

pub tracked struct SingleWriter<T> {
    v: T
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
            self.loc() != other.loc(),
    ;

    // AT-SW-CAS-EXCL
    pub axiom fn compare_and_swap_excl(tracked &mut self, tracked other: &CompareAndSwap<T>)
        ensures
            self.loc() != other.loc(),
    ;
}

// note: skipped timestamp
pub tracked struct CompareAndSwap<T> {
    v: T
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
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.hist() == self.hist().join(other.hist()),
    ;

}

/// This trait is implemented on types which support atomic operations.
pub unsafe trait AtomicType {}

macro_rules! declare_type_is_atomic {
    ($($a:ty),*) => {
        verus! {
            $(unsafe impl AtomicType for $a {})*
        }
    }
}

declare_type_is_atomic!(bool, u8, u16, u32, u64, usize, i8, i16, i32, i64);

unsafe impl<T> AtomicType for *mut T {}

// todo - macro to declare all of the atomic types
#[verifier::external_body]
pub struct PWeakAtomicU8 {
    ato: AtomicU8,
}

/*impl<T: AtomicType + Clone> Clone for Ptr<T> {
    #[verifier::external_body]
    fn clone(&self) -> (res: Self)
        ensures
            res.value() == self.value(),
            res.loc() == self.loc()
    {
        Ptr(self.0.clone())
    }
}

impl<T: AtomicType + Copy> Copy for Ptr<T> {

}*/

impl PWeakAtomicU8 {
    pub uninterp spec fn loc(&self) -> CellId;

    // todo - make const
    #[inline(always)]
    #[verifier::external_body]
    pub /*const*/ fn new_single_writer(i: u8) -> (res: (Self, Tracked<AtomicPointsTo<u8>>, Tracked<SingleWriter<u8>>, Tracked<ViewSeen>, Ghost<nat>))
        ensures
            res.0.loc() == res.1@.loc(),
            res.1@.mode() == AtomicMode::SingleWriter,
            res.2@.loc() == res.1@.loc(),
            res.2@.hist() == res.1@.hist(),
            res.1@.hist().is_singleton(res.4@, i, Some(res.3@.view())),
    {
        let p = PWeakAtomicU8 { ato: AtomicU8::new(i) };
        (p, Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Ghost::new(unreached()))
    }

    pub fn new_compare_and_swap(t: u8) -> (res: (Self, Tracked<AtomicPointsTo<u8>>, Tracked<CompareAndSwap<u8>>, Tracked<ViewSeen>, Ghost<nat>))
        ensures
            res.0.loc() == res.1@.loc(),
            res.1@.mode() == AtomicMode::CompareAndSwap,
            res.2@.loc() == res.1@.loc(),
            res.2@.hist() == res.1@.hist(),
            res.1@.hist().is_singleton(res.4@, t, Some(res.3@.view())),
    {
        let (at, Tracked(pt), Tracked(sw), vs, ts) = Self::new_single_writer(t);
        let tracked cas = pt.single_writer_as_compare_and_swap(sw);
        (at, Tracked(pt), Tracked(cas), vs, ts)
    }

    pub fn new_atomic_concurrent(t: u8) -> (res: (
        Self,
        Tracked<AtomicPointsTo<u8>>,
        Tracked<ViewSeen>,
        Ghost<nat>,
    ))
        ensures
            res.0.loc() == res.1@.loc(),
            res.1@.mode() == AtomicMode::Concurrent,
            res.1@.hist().is_singleton(res.3@, t, Some(res.2@.view())),
    {
        let (at, Tracked(pt), Tracked(sw), vs, ts) = Self::new_single_writer(t);
        proof {
            pt.single_writer_as_concurrent(sw);
        }
        (at, Tracked(pt), vs, ts)
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn into_inner(self, Tracked(pt): Tracked<AtomicPointsTo<u8>>) -> (ret: u8)
        requires
            self.loc() == pt.loc(),
        ensures
            ret == pt.hist().value(pt.hist().max_timestamp())
        opens_invariants none
        no_unwind
    {
        return self.ato.into_inner();
    }

    // AT-READ-SN -- acquire, and also AT-READ-SN-ACQ
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_acquire(
        &self,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(pt): Tracked<&AtomicPointsTo<u8>>,
    ) -> (out: (u8, Ghost<nat>, Ghost<View>))
        requires
            self.loc() == pt.loc(),
            // the thread must've observed at least the allocation?
            // ^ I think this should be true by the fact that the thread has &self
            //old(v_sn).view().contains_loc(self.loc()),
        ensures
            ({
                let v = out.0;  // read value
                let timestamp = out.1@;  // timestamp of the write that was read
                let write_view = out.2@;  // message view for the write that was read
                let singleton_write_hist = History::singleton(timestamp, v, Some(write_view));
                // the write is no earlier than the last write that this thread has seen
                &&& old(v_sn).view().get_timestamp(self.loc()) <= timestamp
                &&& v_sn.view().contains(old(v_sn).view())
                &&& timestamp <= v_sn.view().get_timestamp(self.loc())
                // because this is an acquire read, the message view is joined to the thread's current view
                &&& v_sn.view().contains(write_view)
                // the location's history must've included [timestamp -> (v, write_view)]
                &&& pt.hist().contains(singleton_write_hist)
            }),
        opens_invariants none
        no_unwind
    {
        return (self.ato.load(Ordering::Acquire), Ghost::new(unreached()), Ghost::new(unreached()));
    }

    // AT-READ-SN -- relaxed
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_relaxed(
        &self,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(pt): Tracked<&AtomicPointsTo<u8>>,
    ) -> (out: (u8, Ghost<nat>, Ghost<View>, Tracked<Acquire<ViewSeen>>))
        requires
            self.loc() == pt.loc(),
            //old(v_sn).view().contains_loc(self.loc()), // todo - do we need this? see load_acquire
        ensures
            ({
                let v = out.0;  // read value
                let timestamp = out.1@;  // timestamp of the write that was read
                let write_view = out.2@;  // message view for the write that was read
                let acq_v_sn = out.3@;  // new ViewSeen, under the acquire modality
                let singleton_write_hist = History::singleton(timestamp, v, Some(write_view));
                &&& old(v_sn).view().get_timestamp(self.loc()) <= timestamp
                &&& v_sn.view().contains(old(v_sn).view())
                &&& timestamp <= v_sn.view().get_timestamp(self.loc())
                // because this is a relaxed read, the message view is joined to the thread's acquire view
                &&& acq_v_sn.value().view().contains(write_view)
                // the location's history must've included [timestamp -> (v, write_view)]
                &&& pt.hist().contains(singleton_write_hist)
            }),
        opens_invariants none
        no_unwind
    {
        return (self.ato.load(Ordering::Relaxed), Ghost::new(unreached()), Ghost::new(unreached()), Tracked::assume_new());
    }

    // AT-WRITE-SN -- release
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_release_concurrent(
        &self,
        v: u8,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
    ) -> (out: (Ghost<View>, Ghost<nat>))
        requires
            self.loc() == old(pt).loc(),
            // the thread must've observed at least the allocation?
            //old(v_sn).view().contains_loc(self.loc()), // todo
            old(pt).mode() == AtomicMode::Concurrent,
        ensures
            ({
                let write_view = out.0@;  // view for the write message
                let timestamp = out.1@;  // timestamp of the new write
                let singleton_write_hist = History::singleton(timestamp, v, Some(write_view));
                // the thread's current view is strictly greater than the old one
                &&& v_sn.view().contains_strict(old(v_sn).view())
                // timestamp is greater than all of the thread's observations and is unique for this location's history
                &&& old(v_sn).view().get_timestamp(self.loc()) < timestamp
                &&& !old(pt).hist().contains_timestamp(timestamp)
                // the thread's current view has seen the write timestamps
                &&& timestamp <= v_sn.view().get_timestamp(self.loc())
                // because this is a release write, the write view is the thread's current view
                &&& write_view == v_sn.view()
                // the points-to's history is updated to contain the new write
                &&& pt.loc() == old(pt).loc()
                &&& pt.mode() == old(pt).mode()
                &&& pt.hist() == old(pt).hist().join(singleton_write_hist)
            }),
        opens_invariants none
        no_unwind
    {
        self.ato.store(v, Ordering::Release);
        (Ghost(unreached()), Ghost(unreached()))
    }

    // AT-WRITE-SN -- relaxed
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_relaxed_concurrent(
        &self,
        v: u8,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(rel_v_sn): Tracked<Release<ViewSeen>>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
    ) -> (out: (Ghost<View>, Ghost<nat>))
        requires
            self.loc() == old(pt).loc(),
            // the thread must've observed at least the allocation?
            //old(v_sn).view().contains_loc(self.loc()), // todo
            old(pt).mode() == AtomicMode::Concurrent,
        ensures
            ({
                let write_view = out.0@; // view for the write message
                let timestamp = out.1@;  // timestamp of the new write
                let singleton_write_hist = History::singleton(timestamp, v, Some(write_view));
                // latest thread view is strictly greater than the old one,
                // and the write view is not contained in the old thread view
                &&& v_sn.view().contains_strict(old(v_sn).view())
                &&& !old(v_sn).view().contains(write_view)
                // timestamp is greater than all of the thread's observations and is unique for the history
                &&& old(v_sn).view().get_timestamp(self.loc()) < timestamp
                &&& !old(pt).hist().contains_timestamp(timestamp)
                // the thread's current view has seen the write timestamps
                &&& timestamp <= v_sn.view().get_timestamp(self.loc())
                // because this is a relaxed write, the write view contains the release view
                // and the new thread view contains the write view
                &&& write_view.contains(rel_v_sn.value().view())
                &&& v_sn.view().contains(write_view)
                // the points-to's history is updated to contain the new write, 
                &&& pt.loc() == old(pt).loc()
                &&& pt.mode() == old(pt).mode()
                &&& pt.hist() == old(pt).hist().join(singleton_write_hist)
            }),
        opens_invariants none
        no_unwind
    {
        self.ato.store(v, Ordering::Relaxed);
        (Ghost(unreached()), Ghost(unreached()))
    }

    // AT-WRITE-SW
    #[verifier::atomic]
    pub fn store_release_single_writer(
        &self,
        v: u8,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(sw): Tracked<&mut SingleWriter<u8>>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
    ) -> (out: Ghost<nat>)
        requires
            self.loc() == old(sw).loc(),
            self.loc() == old(pt).loc(),
            // the thread must've observed at least the allocation?
            //old(v_sn).view().contains_loc(self.loc()), // todo
            old(pt).mode() == AtomicMode::SingleWriter,
        ensures
            ({
                let timestamp = out@;  // timestamp of the new write
                let write_view = v_sn.view();
                let singleton_write_hist = History::singleton(timestamp, v, Some(write_view));
                // latest thread view is strictly greater than the old one
                &&& v_sn.view().contains_strict(old(v_sn).view())
                // timestamp is greater than all of the previous history
                // LAILA: do we also need the following two assertions (or do we need lemma that imply them?):
                // NATALIE: I think these could be useful
                // old(v_sn).view().get_timestamp(self.loc()) < timestamp
                // timestamp <= v_sn.view().get_timestamp(self.loc())
                &&& old(pt).hist().max_timestamp() < timestamp
                // SingleWriter's history has the new write
                &&& sw.loc() == old(sw).loc()
                &&& old(sw).hist() == old(pt).hist()  // sw and pt are in sync at the start of the write. LAILA: should this be a precondition? NATALIE: I think this would be implied by the agreement axiom for SingleWriter and AtomicPointsTo
                &&& sw.hist() == pt.hist()
                // the points-to's history is updated to contain the new write
                &&& pt.loc() == old(pt).loc()
                &&& pt.mode() == old(pt).mode()
                &&& pt.hist() == old(pt).hist().join(singleton_write_hist)

            }),
        opens_invariants none
        no_unwind
    {
        // problem: here sw is &mut, but single_writer_as_concurrent expects full ownership of the SingleWriter<u8>
        // would we want to "borrow" a &mut Concurrent AtomicPointsTo<u8> from a &mut SingleWriter AtomicPointsTo<u8> and a &mut SingleWriter<u8>?
        //
        // Verus gives an error for the following signature: 
        // pub axiom fn borrow_single_writer_as_concurrent(tracked &mut self, tracked sw: &mut SingleWriter<T>) -> (tracked out: &mut Self);
        // 
        // error: The verifier does not yet support the following Rust feature: &mut types, except in special cases
        assume(false);
        let (_, ts) = self.store_release_concurrent(
            v,
            Tracked(v_sn),
            Tracked(pt),
        );
        ts
    }

    // AT-WRITE-SW-REL
    #[verifier::atomic]
    pub fn store_release_single_writer_with_rsrc<P>(
        &self,
        v: u8,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(sw): Tracked<&mut SingleWriter<u8>>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
        Tracked(rsrc): Tracked<P>,
    ) -> (out: (Tracked<ViewAt<P>>, Ghost<nat>))
        requires
            self.loc() == old(sw).loc(),
            self.loc() == old(pt).loc(),
            // the thread must've observed at least the allocation?
            //old(v_sn).view().contains_loc(self.loc()), // todo
            old(pt).mode() == AtomicMode::SingleWriter,
        ensures
            ({
                let va_rsrc = out.0@;  // rsrc, under ViewAt
                let timestamp = out.1@;  // timestamp of the new write
                let write_view = v_sn.view();
                let singleton_write_hist = History::singleton(timestamp, v, Some(write_view));
                // latest thread view is strictly greater than the old one
                &&& v_sn.view().contains_strict(old(v_sn).view())
                // timestamp is greater than all of the previous history
                &&& old(pt).hist().max_timestamp() < timestamp
                &&& va_rsrc.view() == v_sn.view() && va_rsrc.value() == rsrc
                // SingleWriter's history has the new write
                &&& sw.loc() == old(sw).loc()
                &&& sw.hist() == old(sw).hist().join(singleton_write_hist)
                // the points-to's history is updated to contains the new write, 
                &&& pt.loc() == old(pt).loc()
                &&& pt.mode() == old(pt).mode()
                &&& pt.hist() == old(pt).hist().join(singleton_write_hist,)
            }),
        opens_invariants none
        no_unwind
    {
        broadcast use View::contains_and_contains_strict;
        //assert(pt.hist().0.len() > 0);

        let tracked (va_rsrc, mut v_sn0) = ViewAt::new_incl(rsrc, *v_sn);
        let ghost v_sn0_old = v_sn0;
        let timestamp = self.store_release_single_writer(v, Tracked(&mut v_sn0), Tracked(sw), Tracked(pt));
        let tracked va_rsrc = va_rsrc.weaken(v_sn0.view());
        proof {
            *v_sn = v_sn0;
        }
        //reveal(History::agrees);
        (Tracked(va_rsrc), timestamp)
    }
}

} // verus!
