use crate::prelude::*;
use crate::cell::CellId;
use crate::pcm::*;
use crate::invariant::*;
use crate::atomic_ghost::AtomicInvariantPredicate;
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
}

pub ghost struct History<T>(pub Map<nat, (T, Option<View>)>);

impl<T> History<T> {
    // #[verifier::type_invariant]
    // pub closed spec fn inv(&self) -> bool {
    //     self.0.dom().finite()
    // }

    pub open spec fn contains_timestamp(&self, timestamp: nat) -> bool {
        self.0.dom().contains(timestamp)
    }

    pub open spec fn index(&self, timestamp: nat) -> (T, Option<View>) 
        recommends self.contains_timestamp(timestamp)
    {
        self.0.index(timestamp)
    }

    pub open spec fn remove(&self, timestamp: nat) -> Self {
        History(self.0.remove(timestamp))
    }

    pub open spec fn dom(&self) -> Set<nat> {
        self.0.dom()
    }

    pub open spec fn get(&self, timestamp: nat) -> Option<(T, Option<View>)> {
        self.0.get(timestamp)
    }

    pub open spec fn insert(&self, timestamp: nat, val: T, view: Option<View>) -> Self 
        recommends
            !self.contains_timestamp(timestamp)
    {
        History(self.0.insert(timestamp, (val, view)))
    }

    pub open spec fn is_singleton(&self, timestamp: nat, val: (T, Option<View>)) -> bool {
        &&& self.contains_timestamp(timestamp)
        &&& forall|ts| #[trigger] self.contains_timestamp(ts) ==> ts == timestamp && self.get(ts) == Some(val)
    }

    pub open spec fn is_max_timestamp(&self, timestamp: nat) -> bool {
        &&& self.contains_timestamp(timestamp)
        &&& forall|ts| #[trigger] self.contains_timestamp(ts) ==> ts <= timestamp
    }

    // pub uninterp spec fn last(&self) -> (nat, (T, Option<View>))
    //     recommends self.0.len() > 0;

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

pub broadcast proof fn history_insert_contains_timestamp_cases<T>(h: History<T>, t: nat, v: T, o: Option<View>, t2: nat)
    requires
        #[trigger] h.insert(t, v, o).contains_timestamp(t2)
    ensures
        t == t2 || h.contains_timestamp(t2)
{}

pub broadcast proof fn history_insert_contains_inserted_timestamp<T>(h: History<T>, t: nat, v: T, o: Option<View>)
    ensures
        (#[trigger] h.insert(t, v, o)).contains_timestamp(t)
{}

pub broadcast proof fn history_get_contains_timestamp<T>(h: History<T>, t: nat)
    requires
        (#[trigger] h.get(t)).is_some()
    ensures
        h.contains_timestamp(t)
{}

pub broadcast proof fn history_singleton_dom_singleton<T>(h: History<T>, ts : nat, val : (T, Option<View>))
    requires
        h.0.dom().finite(),
        #[trigger] h.is_singleton(ts, val)
    ensures
        h.0.dom().is_singleton(),
{
    assert (forall |ts1| #[trigger] h.0.dom().contains(ts1) ==>  h.contains_timestamp(ts1));
    assert (forall |ts1| #[trigger] h.0.dom().contains(ts1) ==>  ts1 == ts);
}



pub broadcast group group_view_history {
    view_contains_refl,
    view_contains_anti_sym,
    view_contains_trans,
    view_join_assoc,
    view_join_comm,
    view_join_idemp,
    view_join_contains,
    history_insert_contains_inserted_timestamp,
    history_insert_contains_timestamp_cases,
    history_get_contains_timestamp,
    view_join_comm,
    view_join_contains,
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
// HOARE-ACQ-FENCE
pub fn fence_acquire(Tracked(acq_vs): Tracked<AcquireViewSeen>) -> (vs: Tracked<ViewSeen>)
    ensures
        acq_vs.view() == vs@.view(),
    opens_invariants none
    no_unwind
{
    core::sync::atomic::fence(Ordering::Acquire);
    Tracked::assume_new()
}

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
    pub axiom fn new() -> (tracked out: ViewSeen)
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

#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct ReleaseViewSeen;

impl ReleaseViewSeen {
    pub uninterp spec fn view(&self) -> View;

    pub axiom fn new() -> (tracked out: Self)
        ensures
            out.view() == View::empty();
}

#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct AcquireViewSeen;

impl AcquireViewSeen {
    pub uninterp spec fn view(&self) -> View;

    pub axiom fn new() -> (tracked out: Self)
        ensures
            out.view() == View::empty();
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

    // VA-BOPS for the separating conjunction case
    pub axiom fn va_join<U>(tracked v0 : ViewAt<T>, tracked v1: ViewAt<U>) -> (tracked out: ViewAt<(T, U)>)
        requires
            v0.view() == v1.view(),
        ensures
            out.view() == v0.view(),
            out.value().0 == v0.value(),
            out.value().1 == v1.value(),
    ;

    // We can strengthen the above rule by not requiring that the views match (we can just take the join of the views).
    // This is useful because it means we don't have to do as much view manipulation in proofs to apply this rule.
    pub proof fn va_join_strong<U>(tracked v0 : ViewAt<T>, tracked v1: ViewAt<U>) -> (tracked out: ViewAt<(T, U)>)
        ensures
            out.view() == v0.view().join(v1.view()),
            out.value().0 == v0.value(),
            out.value().1 == v1.value(),
    {
        let view0 = v0.view();
        let view1 = v1.view();
        let view_join = view0.join(view1);
        assert(view_join.contains(view0)) by {
            view_join_contains(view0, view1);
        }
        assert(view_join.contains(view1)) by {
            view_join_comm(view0, view1);
            view_join_contains(view1, view0);
        }
        let tracked v0 = v0.weaken(view_join);
        let tracked v1 = v1.weaken(view_join);
        ViewAt::va_join(v0, v1)
    }


    // VA-ELIM
    pub axiom fn into_inner(tracked self, tracked sn: ViewSeen) -> (tracked out: T)
        requires
            sn.view().contains(self.view())
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

    // I needed this function when verifying `spinlock::unlock`
    /* Basically, I had two resourse a, b : ViewAt<PointsTo<T>>, with
       a.value().id() == b.value().id() and I wanted to derive a contradiction.
       I generalized this to a generic (contradictory) T:
       The way this works is, given a function f that derives a contradiction from T,
       `va_disjoint` will use f to create a function f' that creates an invalid resource from T,
    		then it uses ViewAt::apply_fn to go from a ViewAt<T> to a ViewAt<Resource<ExclCarrier>>, with an invalid token,
        then because Resource<P> is objective, it uses into_inner_objective() to go from ViewAt<T> to T, then uses validate() to derive a contradiction. */
    pub proof fn va_disjoint(
        tracked self,
        tracked f : proof_fn(tracked v : T))
        requires
            f.requires((self.value(),)),
            f.ensures((self.value(), ), ()) ==>  false,
         ensures
            false,
    {
        let tracked f = proof_fn[Once]|tracked v : T| -> (tracked out : Resource<ExclCarrier>)
        requires v == self.value(),
        ensures !out.value().valid(),
        {
            f(v);
            Resource::alloc(ExclCarrier::Excl)
        };

        let tracked mut va_f = ViewAt::new(f).0;
        let view1 = va_f.view();
        let view2 = self.view();
        let view_join = view1.join(view2);
        assert(view_join.contains(view1)) by {
            view_join_contains(view1, view2);
        }
        assert(view_join.contains(view2)) by {
            view_join_comm(view1, view2);
            view_join_contains(view2, view1);
        }
        let tracked va_f = va_f.weaken(view_join);
        let tracked va_t = self.weaken(view_join);
        let tracked va_tok = va_t.apply_fn(va_f);

        va_tok.into_inner_objective().validate();
    }

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
// note: skipped ghost name, single-writer timestamp
pub tracked struct AtomicPointsTo<T> {
    v: T
}

unsafe impl<T> Objective for AtomicPointsTo<T> {}

impl<T> AtomicPointsTo<T> {
    pub uninterp spec fn loc(&self) -> CellId;

    pub uninterp spec fn hist(&self) -> History<T>;

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.hist().0.len() > 0 && self.hist().0.dom().finite()
    }

    // AT-EXCL
    pub axiom fn excl(tracked &mut self, tracked other: &Self)
        ensures
            self.loc() != other.loc(),
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

impl PWeakAtomicU8 {
    pub uninterp spec fn loc(&self) -> CellId;

    // todo - make const
    #[inline(always)]
    #[verifier::external_body]
    pub /*const*/ fn new(i: u8) -> (res: (
        Self,
        Tracked<AtomicPointsTo<u8>>,
        Tracked<ViewSeen>,
        Ghost<nat>,
    ))
        ensures
            res.0.loc() == res.1@.loc(),
            res.1@.hist().is_singleton(res.3@, (i, Some(res.2@.view()))),
            res.2@.view().contains_loc(res.1@.loc()),
            res.2@.view().get_timestamp(res.1@.loc()) == res.3@
    {
        let p = PWeakAtomicU8 { ato: AtomicU8::new(i) };
        (p, Tracked::assume_new(), Tracked::assume_new(), Ghost::new(unreached()))
    }

    // todo - make const
    #[inline(always)]
    #[verifier::external_body]
    pub /*const*/ fn new_incl(i: u8, Tracked(vs) : Tracked<ViewSeen>) -> (res: (
        Self,
        Tracked<AtomicPointsTo<u8>>,
        Tracked<ViewSeen>,
        Ghost<nat>,
    ))
        ensures
            res.0.loc() == res.1@.loc(),
            res.1@.hist().is_singleton(res.3@, (i, Some(res.2@.view()))),
            res.2@.view().contains_loc(res.1@.loc()),
            res.2@.view().get_timestamp(res.1@.loc()) == res.3@,
     				res.2@.view().contains(vs.view())
    {
        let p = PWeakAtomicU8 { ato: AtomicU8::new(i) };
        (p, Tracked::assume_new(), Tracked::assume_new(), Ghost::new(unreached()))
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn into_inner(self, Tracked(pt): Tracked<AtomicPointsTo<u8>>) -> (ret: (u8, Ghost<nat>))
        requires
            self.loc() == pt.loc(),
        ensures
            pt.hist().is_max_timestamp(ret.1@),
            ret.0 == pt.hist().get(ret.1@).unwrap().0
        opens_invariants none
        no_unwind
    {
        (self.ato.into_inner(), Ghost::new(unreached()))
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
        ensures
            ({
                let v = out.0;  // read value
                let timestamp = out.1@;  // timestamp of the write that was read
                let write_view = out.2@;  // message view for the write that was read
                // the write is no earlier than the last write that this thread has seen
                &&& old(v_sn).view().get_timestamp(self.loc()) <= timestamp
                &&& v_sn.view().contains(old(v_sn).view())
                &&& timestamp <= v_sn.view().get_timestamp(self.loc())
                // because this is an acquire read, the message view is joined to the thread's current view
                &&& v_sn.view().contains(write_view)
                // the location's history must've included [timestamp -> (v, write_view)]
                &&& pt.hist().get(timestamp) == Some((v, Some(write_view)))
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
    ) -> (out: (u8, Tracked<AcquireViewSeen>, Ghost<nat>, Ghost<View>))
        requires
            self.loc() == pt.loc(),
        ensures
            ({
                let v = out.0;  // read value
                let acq_v_sn = out.1@;  // new ViewSeen, under the acquire modality
                let timestamp = out.2@;  // timestamp of the write that was read
                let write_view = out.3@;  // message view for the write that was read
                &&& old(v_sn).view().get_timestamp(self.loc()) <= timestamp
                &&& v_sn.view().contains(old(v_sn).view())
                &&& timestamp <= v_sn.view().get_timestamp(self.loc())
                // because this is a relaxed read, the message view is joined to the thread's acquire view
                &&& acq_v_sn.view().contains(write_view)
                // the location's history must've included [timestamp -> (v, write_view)]
                &&& pt.hist().get(timestamp) == Some((v, Some(write_view)))
            }),
        opens_invariants none
        no_unwind
    {
        return (self.ato.load(Ordering::Relaxed), Tracked::assume_new(), Ghost::new(unreached()), Ghost::new(unreached()));
    }

    // AT-WRITE-SN -- release
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_release(
        &self,
        v: u8,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
    ) -> (out: (Ghost<View>, Ghost<nat>))
        requires
            self.loc() == old(pt).loc(),
        ensures
            ({
                let write_view = out.0@;  // view for the write message
                let timestamp = out.1@;  // timestamp of the new write
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
                &&& pt.hist() == old(pt).hist().insert(timestamp, v, Some(write_view))
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
    pub fn store_relaxed(
        &self,
        v: u8,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(rel_v_sn): Tracked<ReleaseViewSeen>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
    ) -> (out: (Ghost<View>, Ghost<nat>))
        requires
            self.loc() == old(pt).loc(),
        ensures
            ({
                let write_view = out.0@; // view for the write message
                let timestamp = out.1@;  // timestamp of the new write
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
                &&& write_view.contains(rel_v_sn.view())
                &&& v_sn.view().contains(write_view)
                // the points-to's history is updated to contain the new write, 
                &&& pt.loc() == old(pt).loc()
                &&& pt.hist() == old(pt).hist().insert(timestamp, v, Some(write_view))
            }),
        opens_invariants none
        no_unwind
    {
        self.ato.store(v, Ordering::Relaxed);
        (Ghost(unreached()), Ghost(unreached()))
    }

    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_relaxed_mut(
        &mut self,
        v: u8,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(rel_v_sn): Tracked<ReleaseViewSeen>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
    ) -> (out: (Ghost<View>, Ghost<nat>))
        requires
            old(self).loc() == old(pt).loc(),
        ensures
            ({
                let write_view = out.0@; // view for the write message
                let timestamp = out.1@;  // timestamp of the new write
                // latest thread view is strictly greater than the old one,
                // and the write view is not contained in the old thread view
                &&& v_sn.view().contains_strict(old(v_sn).view())
                &&& !old(v_sn).view().contains(write_view)
                // timestamp is greater than all of the thread's observations and is unique for the history
                &&& old(v_sn).view().get_timestamp(self.loc()) < timestamp
                &&& !old(pt).hist().contains_timestamp(timestamp)
                // the thread's current view has seen the write timestamps
                &&& timestamp == v_sn.view().get_timestamp(self.loc())
                // because this is a relaxed write, the write view contains the release view
                // and the new thread view contains the write view
                &&& write_view.contains(rel_v_sn.view())
                &&& v_sn.view().contains(write_view)
                // the points-to's history is updated to contain the new write, and is also truncated to remove all other entries
                &&& pt.loc() == old(pt).loc()
                &&& pt.hist().is_singleton(timestamp, (v, Some(write_view)))
                &&& self.loc() == old(self).loc()
            }),
        opens_invariants none
        no_unwind
    {
        self.ato.store(v, Ordering::Relaxed);
        (Ghost(unreached()), Ghost(unreached()))
    }

    #[inline(always)]
    #[verifier::external_body]
    // TODO make this proof so that it can be used inside an atomic invariant body
    pub fn truncate_history(&mut self, Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>) -> (ts: Ghost<nat>)
        requires
            old(self).loc() == old(pt).loc()
        ensures
            *self == *old(self),
            pt.loc() == old(pt).loc(),
            old(pt).hist().is_max_timestamp(ts@),
            pt.hist().is_singleton(ts@, old(pt).hist().get(ts@).unwrap())
        opens_invariants none
        no_unwind
    {
        Ghost(unreached())
    }

    // AT-CAS-SN-GEN -- of = relaxed, or = acquire, ow = relaxed
    // NN: too verbose, can we factor out this such that we can reuse loading and storing specs across different operations
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn cas_rlx_acq_rlx(
        &self,
        Tracked(v_sn): Tracked<&mut ViewSeen>,
        Tracked(rel_v_sn): Tracked<ReleaseViewSeen>,
        Tracked(pt): Tracked<&mut AtomicPointsTo<u8>>,
        vr : u8,
        vw : u8,
    ) -> (out: (Result<u8, u8>, Ghost<View>, Ghost<View>, Ghost<nat>, Tracked<Option<AcquireViewSeen>>))
        requires
            self.loc() == old(pt).loc(),
        ensures
            ({
                let res = out.0; // whether the CAS succeeded
                let read_view = out.1@; // view for the read message
                let write_view = out.2@; // view for the write message (if the CAS succeeded)
                let timestamp = out.3@;  // timestamp of the write that was read
                let vs_vr_opt = out.4@; // new ViewSeen under the acquire modality, if the CAS failed because of = rlx
                let v = match res { Ok(v) => v, Err(v) => v, };
                // the write that was read is no earlier than the last write that this thread has seen
                &&& old(v_sn).view().get_timestamp(self.loc()) <= timestamp
                // latest thread view is greater than (or potentially equal to if CAS fails) the old one,
                &&& v_sn.view().contains(old(v_sn).view())
                // the latest thread view has seen the timestamp of the write that was read
                &&& timestamp <= v_sn.view().get_timestamp(self.loc())
                &&& #[trigger] pt.hist().get(timestamp) == Some((v, Some(read_view)))
                &&& pt.loc() == old(pt).loc()
                &&& ({
                    &&& res matches Ok(_)
                    &&& vr == v
                    &&& v_sn.view().contains_strict(old(v_sn).view())
                    &&& write_view.contains_strict(read_view)
                    &&& !read_view.contains(v_sn.view())
                    // the new write will be placed in the history next to the write that was read, the history should have this timestamp available
                    &&& !old(pt).hist().contains_timestamp(timestamp+1)
                    // because this is a relaxed write (ow = rlx), the write view contains the release view
                    &&& write_view.contains(rel_v_sn.view())
                    // because the successful read is an acquire read (or = acq), the read and write views are both joined to the thread's current view
                    &&& v_sn.view().contains(write_view)
                    // the points-to's history is updated to contain the new write,
                    &&& pt.hist() == old(pt).hist().insert(timestamp+1, vw, Some(write_view)) }) ||
                ({
                    &&& res matches Err(_)
                    &&& vr != v
                    &&& pt.hist() == old(pt).hist()
                    &&& vs_vr_opt.is_some()
                    &&& vs_vr_opt.unwrap().view() == read_view
                })
            }),
        opens_invariants none
        no_unwind
    {
        return (self.ato.compare_exchange(vr, vw, Ordering::Acquire, Ordering::Relaxed), Ghost::new(unreached()), Ghost::new(unreached()), Ghost::new(unreached()), Tracked::assume_new());
    }
}

// version of atomic_ghost types for weak memory
// todo - macro to declare all atomic types

pub struct WeakAtomicPredU8<Pred> { p: Pred }

/*
// changed from SC atomic_ghost:
// - Pred is over a History<u8> instead of a u8
// - AtomicPointsTo is SingleWriter mode
//
// It seems like we might need different APIs for each of the AtomicPointsTo modes. 
// Some atomic ops have preconditions on AtomicPointsTo::mode()
impl<K, G, Pred> InvariantPredicate<(K, CellId), (AtomicPointsTo<u8>, G)> for WeakAtomicPredU8<Pred>
    where Pred: AtomicInvariantPredicate<K, History<u8>, G>
{
    open spec fn inv(k_loc: (K, CellId), perm_g: (AtomicPointsTo<u8>, G)) -> bool {
        let (k, loc) = k_loc;
        let (perm, g) = perm_g;

        &&& perm.loc() == loc
        &&& Pred::atomic_inv(k, perm.hist(), g)
        &&& perm_g.0.mode() == AtomicMode::SingleWriter
    }
}

pub struct WeakAtomicU8<K, G, Pred>
{
    #[doc(hidden)]
    pub patomic: PWeakAtomicU8,

    #[doc(hidden)]
    pub atomic_inv: Tracked<AtomicInvariant<(K, CellId), (AtomicPointsTo<u8>, G), WeakAtomicPredU8<Pred>>>,
}

impl<K, G, Pred> WeakAtomicU8<K, G, Pred>
    where Pred: AtomicInvariantPredicate<K, History<u8>, G>
{
    pub open spec fn well_formed(&self) -> bool {
        self.atomic_inv@.constant().1 == self.patomic.loc()
    }

    pub open spec fn constant(&self) -> K {
        self.atomic_inv@.constant().0
    }

    pub closed spec fn loc(&self) -> CellId {
        self.patomic.loc()
    }

    // todo - make const    
    #[inline(always)]
    pub /*const*/ fn new_single_writer(Ghost(k): Ghost<K>, u: u8, Tracked(g): Tracked<G>) -> (out: (Self, Tracked<SingleWriter<u8>>, Tracked<ViewSeen>, Ghost<nat>))
        requires 
            forall |ts, v| #[trigger] Pred::atomic_inv(k, History::singleton(ts, u, Some(v)), g),
        ensures 
            out.0.well_formed(), 
            out.0.constant() == k,
            out.0.loc() == out.1@.loc(),
            out.1@.hist() == History::singleton(out.3@, u, Some(out.2@.view()))
    {

        let (patomic, Tracked(perm), sw, vs, ts) = PWeakAtomicU8::new_single_writer(u);

        let tracked pair = (perm, g);
        let tracked atomic_inv = AtomicInvariant::new(
            (k, patomic.loc()), pair, 0);

        let at = WeakAtomicU8 {
            patomic,
            atomic_inv: Tracked(atomic_inv),
        };

        (at, sw, vs, ts)
    }

    #[inline(always)]
    pub fn into_inner(self) -> (res: (u8, Ghost<History<u8>>, Tracked<G>))
        requires 
            self.well_formed(),
        ensures 
            Pred::atomic_inv(self.constant(), res.1@, res.2@),
            res.0 == res.1@.value(res.1@.is_max_timestamp())
    {
        let Self { patomic, atomic_inv: Tracked(atomic_inv) } = self;
        let tracked (perm, g) = atomic_inv.into_inner();
        let ghost hist = perm.hist();
        let v = patomic.into_inner(Tracked(perm));
        (v, Ghost(hist), Tracked(g))
    }
}*/

/// Excl PCM
pub enum ExclCarrier {
    Excl,
    Empty,
    Invalid,
}

impl PCM for ExclCarrier {
    closed spec fn valid(self) -> bool {
        match self {
            ExclCarrier::Invalid => false,
            ExclCarrier::Empty | ExclCarrier::Excl => true,
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        match self {
            ExclCarrier::Invalid => ExclCarrier::Invalid,
            ExclCarrier::Empty => other,
            ExclCarrier::Excl => match other {
                ExclCarrier::Invalid | ExclCarrier::Excl => ExclCarrier::Invalid,
                ExclCarrier::Empty => self,
            },
        }
    }

    closed spec fn unit() -> Self {
        ExclCarrier::Empty
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

} // verus!
