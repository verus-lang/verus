use super::cell::CellId;
use super::prelude::*;
use super::resource::algebra;
use super::resource::pcm;

/// This trait should be implemented on types P such that objective(P) holds
// todo - add tests to ensure the (non-)implementations of this marker trait are as expected
pub unsafe auto trait Objective {}

verus! {

#[verifier::external_trait_specification]
pub trait ExObjective: std::marker::PointeeSized {
    type ExternalTraitSpecificationFor: Objective;
}

/// Represents a thread's subjective view of memory.
/// For non-atomic memory locations, the relationship between two views is modeled abstractly (i.e., no timestamps are compared).
/// For atomic memory locations, we can reason about the per-location timestamp contained in a view.
// This type will be defined with uninterp spec fns, so it should be treated abstractly by the verifier.
#[verifier::external_body]
pub ghost struct ThreadView;

impl ThreadView {
    /// The empty view.
    pub uninterp spec fn empty() -> Self;

    /// True when `other` is contained in `self`.
    pub uninterp spec fn contains(self, other: Self) -> bool;

    /// True when `other` is contained in `self` and `other` is not equal to `self`.
    pub uninterp spec fn contains_strict(self, other: Self) -> bool;

    /// Returns the union of `self` and `other`.
    pub uninterp spec fn join(self, other: Self) -> Self;

    pub broadcast axiom fn contains_refl(v: Self)
        ensures
            #[trigger] v.contains(v),
    ;

    pub broadcast axiom fn contains_anti_sym(v1: Self, v2: Self)
        requires
            #[trigger] v1.contains(v2),
            v1 != v2,
        ensures
            !(#[trigger] v2.contains(v1)),
    ;

    pub broadcast axiom fn contains_trans(v1: Self, v2: Self, v3: Self)
        requires
            #[trigger] v1.contains(v2),
            #[trigger] v2.contains(v3),
        ensures
            #[trigger] v1.contains(v3),
    ;

    pub broadcast axiom fn join_assoc(v1: Self, v2: Self, v3: Self)
        ensures
            #[trigger] v1.join(v2.join(v3)) =~= #[trigger] v1.join(v2).join(v3),
    ;

    pub broadcast axiom fn join_comm(v1: Self, v2: Self)
        ensures
            #[trigger] v1.join(v2) =~= v2.join(v1),
    ;

    pub broadcast axiom fn join_idemp(v: Self)
        ensures
            #[trigger] v.join(v) =~= v,
    ;

    pub broadcast axiom fn join_contains(v1: Self, v2: Self)
        ensures
            #[trigger] v1.join(v2).contains(v1),
    ;
}

pub broadcast group group_thread_view_axioms {
    ThreadView::contains_refl,
    ThreadView::contains_anti_sym,
    ThreadView::contains_trans,
    ThreadView::join_assoc,
    ThreadView::join_comm,
    ThreadView::join_idemp,
    ThreadView::join_contains,
}

/// Resource representing a thread's subjective view of memory.
/// Owning a `ViewSeen` is equivalent to having a lower-bound on the thread's current view.
#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct ViewSeen;

impl crate::view::View for ViewSeen {
    type V = ThreadView;

    open spec fn view(&self) -> ThreadView {
        self.thread_view()
    }
}

impl ViewSeen {
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    // VS_BOT
    pub axiom fn new() -> (tracked out: ViewSeen)
        ensures
            out@ == ThreadView::empty(),
    ;

    // VS-JOIN |-
    pub axiom fn split(tracked self, v1: ThreadView, v2: ThreadView) -> (tracked out: (Self, Self))
        requires
            self@ == v1.join(v2),
        ensures
            out.0@ == v1,
            out.1@ == v2,
    ;

    // VS-JOIN -|
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        ensures
            out@ == self@.join(other@),
    ;

    // VS-MONO
    pub axiom fn restrict(tracked self, v: ThreadView) -> (tracked out: Self)
        requires
            self@.contains(v),
        ensures
            out@ == v,
    ;
}

#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct ReleaseViewSeen;

impl crate::view::View for ReleaseViewSeen {
    type V = ThreadView;

    open spec fn view(&self) -> ThreadView {
        self.thread_view()
    }
}

impl ReleaseViewSeen {
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    pub axiom fn new() -> (tracked out: Self)
        ensures
            out@ == ThreadView::empty(),
    ;
}

#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct AcquireViewSeen;

impl crate::view::View for AcquireViewSeen {
    type V = ThreadView;

    open spec fn view(&self) -> ThreadView {
        self.thread_view()
    }
}

impl AcquireViewSeen {
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    pub axiom fn new() -> (tracked out: Self)
        ensures
            out@ == ThreadView::empty(),
    ;
}

impl !Objective for ViewSeen {

}

impl !Objective for AcquireViewSeen {

}

impl !Objective for ReleaseViewSeen {

}

// PCMs and RAs are objective
unsafe impl<P: pcm::PCM> Objective for pcm::Resource<P> {

}

unsafe impl<RA: algebra::ResourceAlgebra> Objective for algebra::Resource<RA> {

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

// note: the fact that tuples are Objective (above) suffices for OBJMOD-SEP
// OBJ with wand update
unsafe impl<'a, P: Objective, Q: Objective, F: ProofFnOnce> Objective for proof_fn<'a, F>(
    tracked p: P,
) -> tracked Q {

}

// ViewAt<T> is persistent when T is persistent
// the #[derive] attribute will ensure that ViewAt<T>: Copy only when T: Copy
#[derive(Copy)]
pub tracked struct ViewAt<T> {
    v: T,
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
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    pub uninterp spec fn value(&self) -> T;

    // VA-INTRO
    pub axiom fn new(tracked t: T) -> (tracked out: (Self, ViewSeen))
        ensures
            out.0.value() == t,
            out.0.thread_view() == out.1@,
    ;

    // VA-INTRO-INCL
    pub axiom fn new_incl(tracked t: T, tracked sn: ViewSeen) -> (tracked out: (Self, ViewSeen))
        ensures
            out.0.value() == t,
            out.0.thread_view() == out.1@,
            out.1.thread_view().contains(sn@),
    ;

    // VA-BOPS for the separating conjunction case
    pub axiom fn va_join<U>(tracked v0: ViewAt<T>, tracked v1: ViewAt<U>) -> (tracked out: ViewAt<
        (T, U),
    >)
        requires
            v0.thread_view() == v1.thread_view(),
        ensures
            out.thread_view() == v0.thread_view(),
            out.value().0 == v0.value(),
            out.value().1 == v1.value(),
    ;

    // We can strengthen the above rule by not requiring that the views match (we can just take the join of the views).
    // This is useful because it means we don't have to do as much view manipulation in proofs to apply this rule.
    pub proof fn va_join_strong<U>(tracked v0: ViewAt<T>, tracked v1: ViewAt<U>) -> (tracked out:
        ViewAt<(T, U)>)
        ensures
            out.thread_view() == v0.thread_view().join(v1.thread_view()),
            out.value().0 == v0.value(),
            out.value().1 == v1.value(),
    {
        let view0 = v0.thread_view();
        let view1 = v1.thread_view();
        let view_join = view0.join(view1);
        assert(view_join.contains(view0)) by {
            ThreadView::join_contains(view0, view1);
        }
        assert(view_join.contains(view1)) by {
            ThreadView::join_comm(view0, view1);
            ThreadView::join_contains(view1, view0);
        }
        let tracked v0 = v0.weaken(view_join);
        let tracked v1 = v1.weaken(view_join);
        ViewAt::va_join(v0, v1)
    }

    // VA-ELIM
    pub axiom fn into_inner(tracked self, tracked sn: ViewSeen) -> (tracked out: T)
        requires
            sn@.contains(self.thread_view()),
        ensures
            out == self.value(),
    ;

    // this is encoding view monotonicity
    pub axiom fn weaken(tracked self, v: ThreadView) -> (tracked out: Self)
        requires
            v.contains(self.thread_view()),
        ensures
            out.thread_view() == v,
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
            f.thread_view() == self.thread_view(),
        ensures
            f.value().ensures((self.value(),), out.value()),
            out.thread_view() == self.thread_view(),
    ;

    pub proof fn apply_fn_strong<U>(
        tracked self,
        tracked f: proof_fn[Once](tracked v1: T) -> tracked U,
    ) -> (tracked out: ViewAt<U>)
        requires
            f.requires((self.value(),)),
        ensures
            f.ensures((self.value(),), out.value()),
            out.thread_view().contains(self.thread_view()),
    {
        let tracked va_f = ViewAt::new(f).0;
        let view1 = va_f.thread_view();
        let view2 = self.thread_view();
        let view_join = view1.join(view2);
        assert(view_join.contains(view1)) by {
            ThreadView::join_contains(view1, view2);
        }
        assert(view_join.contains(view2)) by {
            ThreadView::join_comm(view1, view2);
            ThreadView::join_contains(view2, view1);
        }
        let tracked va_f = va_f.weaken(view_join);
        let tracked va_t = self.weaken(view_join);
        va_t.apply_fn(va_f)
    }
}

} // verus!
