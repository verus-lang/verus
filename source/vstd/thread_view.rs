use super::cell::CellId;
use super::prelude::*;
use super::resource::algebra;
use super::resource::pcm;
use super::view::*;

/// A type that implements `Objective` cannot carry permissions that depend on a thread's subjective view of memory,
/// as determined by Rust's weak memory model. This trait is only relevant in the weak memory setting.
// todo - add tests to ensure the (non-)implementations of this marker trait are as expected
#[cfg(verus_keep_ghost)]
pub unsafe auto trait Objective {}

verus! {

#[cfg(verus_keep_ghost)]
#[verifier::external_trait_specification]
pub trait ExObjective: core::marker::PointeeSized {
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

    /// View containment is reflexive.
    pub broadcast axiom fn contains_refl(v: Self)
        ensures
            #[trigger] v.contains(v),
    ;

    /// View containment is anti-symmetric.
    pub broadcast axiom fn contains_anti_sym(v1: Self, v2: Self)
        requires
            #[trigger] v1.contains(v2),
            v1 != v2,
        ensures
            !(#[trigger] v2.contains(v1)),
    ;

    /// View containment is transitive.
    pub broadcast axiom fn contains_trans(v1: Self, v2: Self, v3: Self)
        requires
            #[trigger] v1.contains(v2),
            #[trigger] v2.contains(v3),
        ensures
            #[trigger] v1.contains(v3),
    ;

    pub broadcast axiom fn contains_strict_contains(v1: Self, v2: Self)
        requires
            #[trigger] v1.contains_strict(v2),
        ensures
            v1.contains(v2),
    ;

    /// Joining of views is associative.
    pub broadcast axiom fn join_assoc(v1: Self, v2: Self, v3: Self)
        ensures
            #[trigger] v1.join(v2.join(v3)) =~= #[trigger] v1.join(v2).join(v3),
    ;

    /// Joining of views is commutative.
    pub broadcast axiom fn join_comm(v1: Self, v2: Self)
        ensures
            #[trigger] v1.join(v2) =~= v2.join(v1),
    ;

    /// Joining a view with itself results in the same view.
    pub broadcast axiom fn join_identity(v: Self)
        ensures
            #[trigger] v.join(v) =~= v,
    ;

    /// The result of joining a view with another view contains the original view.
    pub broadcast axiom fn join_contains(v1: Self, v2: Self)
        ensures
            #[trigger] v1.join(v2).contains(v1),
    ;
}

pub broadcast group group_thread_view_axioms {
    ThreadView::contains_refl,
    ThreadView::contains_anti_sym,
    ThreadView::contains_trans,
    ThreadView::contains_strict_contains,
    ThreadView::join_assoc,
    ThreadView::join_comm,
    ThreadView::join_identity,
    ThreadView::join_contains,
}

/// Resource representing a thread's subjective view of memory.
/// Owning a `ViewSeen` provides a lower-bound on the thread's current view.
#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct ViewSeen;

impl View for ViewSeen {
    type V = ThreadView;

    open spec fn view(&self) -> ThreadView {
        self.thread_view()
    }
}

impl ViewSeen {
    /// The view that this permission represents.
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    /// Creates a [`ViewSeen`] permission corresponding to the empty view.
    pub axiom fn new() -> (tracked out: ViewSeen)
        ensures
            out@ == ThreadView::empty(),
    ;

    /// Joins this [`ViewSeen`] permission with another [`ViewSeen`] to create a new [`ViewSeen`],
    /// representing the join of the two views.
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        ensures
            out@ == self@.join(other@),
    ;

    /// Creates a new [`ViewSeen`] representing a view which is contained in the view corresponding to the original [`ViewSeen`].
    pub axiom fn weaken(tracked self, v: ThreadView) -> (tracked out: Self)
        requires
            self@.contains(v),
        ensures
            out@ == v,
    ;
}

/// Resource representing the ``release view" in a thread's subjective view of memory, according to Rust's weak memory model.
/// If a thread holds a [`ReleaseViewSeen`], then that view that was held by a thread at some point that it performed a release fence in the past.
#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct ReleaseViewSeen;

impl View for ReleaseViewSeen {
    type V = ThreadView;

    open spec fn view(&self) -> ThreadView {
        self.thread_view()
    }
}

impl ReleaseViewSeen {
    /// The view that this permission represents.
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    /// Creates a new permission corresponding to the empty view.
    pub axiom fn new() -> (tracked out: Self)
        ensures
            out@ == ThreadView::empty(),
    ;
}

/// Resource representing the ``acquire view" in a thread's subjective view of memory, according to Rust's weak memory model.
/// If a thread holds an [`AcquireViewSeen`], then that permission represents a view that would be held by a thread
/// if it were to perform an acquire fence in the future.
#[derive(Clone, Copy)]
#[verifier::external_body]
pub tracked struct AcquireViewSeen;

impl View for AcquireViewSeen {
    type V = ThreadView;

    open spec fn view(&self) -> ThreadView {
        self.thread_view()
    }
}

impl AcquireViewSeen {
    /// The view that this permission represents.
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    /// Creates a new permission corresponding to the empty view.
    pub axiom fn new() -> (tracked out: Self)
        ensures
            out@ == ThreadView::empty(),
    ;
}

// ViewSeen permissions are not objective as they represent a thread's subjective view of memory.
#[cfg(verus_keep_ghost)]
impl !Objective for ViewSeen {

}

#[cfg(verus_keep_ghost)]
impl !Objective for AcquireViewSeen {

}

#[cfg(verus_keep_ghost)]
impl !Objective for ReleaseViewSeen {

}

// PCMs and RAs are objective
#[cfg(verus_keep_ghost)]
unsafe impl<P: pcm::PCM> Objective for pcm::Resource<P> {

}

#[cfg(verus_keep_ghost)]
unsafe impl<RA: algebra::ResourceAlgebra> Objective for algebra::Resource<RA> {

}

// primitive types are objective because they do not hold permissions
macro_rules! declare_primitive_is_objective {
    ($($a:ty),*) => {
        verus! {
            $(
                #[cfg(verus_keep_ghost)]
                unsafe impl Objective for $a {}
            )*
        }
    }
}

declare_primitive_is_objective!(bool, char, (), u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, int, nat, str);

// note: the fact that tuples are Objective (above) suffices for OBJMOD-SEP
// OBJ with wand update
#[cfg(verus_keep_ghost)]
unsafe impl<'a, P: Objective, Q: Objective, F: ProofFnOnce> Objective for proof_fn<'a, F>(
    tracked p: P,
) -> tracked Q {

}

/// Represents a permission of type `T` which is safe for a thread to own, provided that this thread has
/// seen a particular view.
#[derive(Copy)]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub tracked struct ViewAt<T> {
    _dummy: core::marker::PhantomData<T>,
}

impl<T: Clone> Clone for ViewAt<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

// ViewAt is objective, because it does not give direct access to memory permissions themselves
#[cfg(verus_keep_ghost)]
unsafe impl<T> Objective for ViewAt<T> {

}

impl<T> ViewAt<T> {
    /// View that a thread must synchronize with in order to safely start using the inner permission.
    pub uninterp spec fn thread_view(&self) -> ThreadView;

    /// The inner permission represented by this [`ViewAt`].
    pub uninterp spec fn value(&self) -> T;

    /// Creates a new [`ViewAt`] from the given permission.
    /// This permission will be safe to start using at an arbitrary view,
    /// represented by the [`ViewSeen`] returned by this operation.
    pub axiom fn new(tracked t: T) -> (tracked (va, vs): (Self, ViewSeen))
        ensures
            va.value() == t,
            va.thread_view() == vs@,
    ;

    /// Creates a new [`ViewAt`] from the given permission and lower bound on the synchronizing view.
    /// This permission will be safe to start using at some view that is larger than the given view `sn`,
    /// represented by the [`ViewSeen`] returned by this operation.
    pub proof fn new_incl(tracked t: T, tracked vs_0: ViewSeen) -> (tracked (va, vs): (
        Self,
        ViewSeen,
    ))
        ensures
            va.value() == t,
            va.thread_view() == vs@,
            va.thread_view().contains(vs_0@),
    {
        broadcast use group_thread_view_axioms;
        
        let tracked (va, vs) = ViewAt::new(t);
        let tracked vs = vs.join(vs_0);
        let tracked va = va.weaken(vs@);
        (va, vs)
    }

    // Weaker version of `join_tup`.
    axiom fn join_tup_inner<U>(tracked v0: ViewAt<T>, tracked v1: ViewAt<U>) -> (tracked out:
        ViewAt<(T, U)>)
        requires
            v0.thread_view() == v1.thread_view(),
        ensures
            out.thread_view() == v0.thread_view(),
            out.value().0 == v0.value(),
            out.value().1 == v1.value(),
    ;

    /// Given two [`ViewAt`] permissions, they can be joined into a single [`ViewAt`] permission,
    /// whose inner permission a tuple of the original inner permissions,
    /// and whose synchronizing view is the join of the original synchronizing views.
    pub proof fn join_tup<U>(tracked v0: ViewAt<T>, tracked v1: ViewAt<U>) -> (tracked out: ViewAt<
        (T, U),
    >)
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
        ViewAt::join_tup_inner(v0, v1)
    }

    /// Given a [`ViewAt`] permission, its synchronizing view can be weakened to a larger view.
    pub axiom fn weaken(tracked self, v: ThreadView) -> (tracked out: Self)
        requires
            v.contains(self.thread_view()),
        ensures
            out.thread_view() == v,
            out.value() == self.value(),
    ;

    /// Returns the inner permission, provided that the calling thread has obtained the synchronizing view `self.thread_view()`.
    pub axiom fn into_inner(tracked self, tracked sn: ViewSeen) -> (tracked out: T)
        requires
            sn@.contains(self.thread_view()),
        ensures
            out == self.value(),
    ;

    /// Weaker version of `apply_fn`.
    axiom fn apply_fn_inner<U>(
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

    /// Given a proof closure `f`, it can be applied to a resource `self` which is ``under" a [`ViewAt`].
    /// The resulting resource will be returned under a [`ViewAt`] at some larger view than the original resource.
    pub proof fn apply_fn<U>(
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
        va_t.apply_fn_inner(va_f)
    }
}

} // verus!
