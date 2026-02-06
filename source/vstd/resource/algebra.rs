use super::super::modes::*;
use super::super::prelude::*;
use super::super::set::*;
use super::Loc;
use super::option::*;
use super::pcm;
use super::pcm::PCM;
use super::relations::*;

verus! {

broadcast use super::super::set::group_set_axioms;

/// Interface for Resource Algebra ghost state.
#[verifier::accept_recursive_types(RA)]
pub tracked struct Resource<RA: ResourceAlgebra> {
    pcm: pcm::Resource<Option<RA>>,
}

#[verifier::accept_recursive_types(RA)]
pub tracked struct ResourceRef<'a, RA: ResourceAlgebra> {
    pcm: &'a pcm::Resource<Option<RA>>,
}

impl<RA: ResourceAlgebra> Resource<RA> {
    pub proof fn as_ref(tracked &self) -> (tracked r: ResourceRef<'_, RA>)
        ensures
            self.loc() == r.loc(),
            self.value() == r.value(),
    {
        use_type_invariant(self);
        ResourceRef { pcm: &self.pcm }
    }
}

/// A Resource Algebra operating on a type T
///
/// This construction is based off the [Iris from the Ground Up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)
/// report.
///
/// A striking difference is that we do not need a core for elements (the core is interesting in
/// Iris because of the persistent modality, which Verus does not have).
///
/// See [`Resource`] for more information.
// TODO(bsdinis): it should probably not be required that ghost things be sized, but that sounds
// like a relatively complicated change -- needs to be done across the codebase
pub trait ResourceAlgebra: Sized {
    /// Whether an element is valid
    spec fn valid(self) -> bool;

    /// Compose two elements
    ///
    /// Sometimes the notation `a · b` is used to represent `RA::op(a, b)`
    spec fn op(a: Self, b: Self) -> Self;

    /// The operation is associative
    proof fn associative(a: Self, b: Self, c: Self)
        ensures
            Self::op(a, Self::op(b, c)) == Self::op(Self::op(a, b), c),
    ;

    /// The operation is commutative
    proof fn commutative(a: Self, b: Self)
        ensures
            Self::op(a, b) == Self::op(b, a),
    ;

    /// The operation is closed under inclusion
    /// (i.e., if the result of the operation is valid then its parts are also valid)
    proof fn valid_op(a: Self, b: Self)
        requires
            Self::op(a, b).valid(),
        ensures
            a.valid(),
    ;
}

/// Implementation of a [`Resource`] based on a [`ResourceAlgebra`]
// This follows roughly the Iris from the Ground up construction
impl<RA: ResourceAlgebra> Resource<RA> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.pcm.value() is Some
    }

    /// The underlying value of the resource
    pub closed spec fn value(self) -> RA {
        self.pcm.value()->Some_0
    }

    /// The location of the resource
    pub closed spec fn loc(self) -> Loc {
        self.pcm.loc()
    }

    /// Allocate a new resource at a fresh location
    // GHOST-ALLOC rule
    pub proof fn alloc(value: RA) -> (tracked out: Self)
        requires
            value.valid(),
        ensures
            out.value() == value,
    {
        let tracked pcm = pcm::Resource::alloc(Some(value));
        Resource { pcm }
    }

    /// We can join together two resources at the same location, where we obtain the combination of
    /// the two
    // reverse implication in the GHOST-OP rule
    pub proof fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.value() == RA::op(self.value(), other.value()),
    {
        use_type_invariant(&self);
        use_type_invariant(&other);
        let tracked pcm = self.pcm.join(other.pcm);
        Resource { pcm }
    }

    /// If a resource holds the result of a composition, we can split it into the components
    // implication in the GHOST-OP rule
    pub proof fn split(tracked self, left: RA, right: RA) -> (tracked out: (Self, Self))
        requires
            self.value() == RA::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == left,
            out.1.value() == right,
    {
        use_type_invariant(&self);
        let tracked (left, right) = self.pcm.split(Some(left), Some(right));
        (Resource { pcm: left }, Resource { pcm: right })
    }

    /// Whenever we have a resource, that resource is valid. This intuitively (and inductively)
    /// holds because:
    ///     1. We only create valid resources (via [`alloc`]);
    ///     2. We can only update the value of a resource via a [`frame_preserving_update_opt`] (see
    ///        [`update`](Self::update) for more details. Because of the requirement of that
    ///        updates are frame preserving this means that `join`s remain valid.
    pub proof fn validate(tracked &self)
        ensures
            self.value().valid(),
    {
        use_type_invariant(self);
        self.pcm.validate();
    }

    /// This is a more general version of [`update`](Self::update).
    // GHOST-UPDATE rule
    pub proof fn update_nondeterministic(tracked self, new_values: Set<RA>) -> (tracked out: Self)
        requires
            frame_preserving_update_nondeterministic_opt(self.value(), new_values),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    {
        use_type_invariant(&self);
        let opt_new_values = new_values.map(|v| Some(v));
        lemma_frame_preserving_update_nondeterministic_opt(self.value(), new_values);
        let tracked pcm = self.pcm.update_nondeterministic(opt_new_values);
        Resource { pcm }
    }

    /// Update a resource to a new value. This can only be done if the update is frame preserving
    /// (i.e., any value that could be composed with the original value can still be composed with
    /// the new value).
    ///
    /// See [`frame_preserving_update`] for more information.
    // variant of the GHOST-UPDATE rule
    pub proof fn update(tracked self, new_value: RA) -> (tracked out: Self)
        requires
            frame_preserving_update_opt(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        let new_values = set![new_value];
        assert(new_values.contains(new_value));
        self.update_nondeterministic(new_values)
    }

    /// Extracts the resource from `r`, leaving `r` unspecified and returning
    /// a new resource holding the previous value of `r`.
    pub proof fn extract(tracked &mut self) -> (tracked other: Self)
        ensures
            other.loc() == old(self).loc(),
            other.value() == old(self).value(),
    {
        self.validate();
        let tracked mut other = Self::alloc(self.value());
        tracked_swap(self, &mut other);
        other
    }

    /// Validate two items at once. If we have two resources at the same location then its
    /// composition is valid.
    pub proof fn validate_2(tracked &mut self, tracked other: &ResourceRef<'_, RA>)
        requires
            old(self).loc() == other.loc(),
        ensures
            *self == *old(self),
            RA::op(self.value(), other.value()).valid(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.pcm.validate_2(&other.pcm);
    }

    /// We can do a similar update to [`update_with_shared`](Self::update_with_shared) for non-deterministic updates
    pub proof fn update_nondeterministic_with_shared(
        tracked self,
        tracked other: &ResourceRef<'_, RA>,
        new_values: Set<RA>,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_preserving_update_nondeterministic_opt(
                RA::op(self.value(), other.value()),
                set_op(new_values, other.value()),
            ),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        let a = RA::op(self.value(), other.value());
        let bs = set_op(new_values, other.value());

        lemma_frame_preserving_update_nondeterministic_opt(a, bs);
        lemma_set_op_opt(new_values, other.value());

        let new_values_opt = new_values.map(|v| Some(v));
        let tracked pcm = self.pcm.update_nondeterministic_with_shared(&other.pcm, new_values_opt);
        Resource { pcm }
    }

    /// If `x · y --> x · z` is a frame-perserving update, and we have a shared reference to `x`,
    /// we can update the `y` resource to `z`.
    pub proof fn update_with_shared(
        tracked self,
        tracked other: &ResourceRef<'_, RA>,
        new_value: RA,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_preserving_update_opt(
                RA::op(self.value(), other.value()),
                RA::op(new_value, other.value()),
            ),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        let new_values = set![new_value];
        let so = set_op(new_values, other.value());
        assert(new_values.contains(new_value));
        assert(so == set![new_value].map(|n| RA::op(new_value, other.value())));
        assert(so.contains(RA::op(new_value, other.value())));
        self.update_nondeterministic_with_shared(other, new_values)
    }
}

impl<'a, RA: ResourceAlgebra> ResourceRef<'a, RA> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.pcm.value() is Some
    }

    pub closed spec fn loc(self) -> Loc {
        self.pcm.loc()
    }

    pub closed spec fn value(self) -> RA {
        self.pcm.value()->Some_0
    }

    /// Whenever we have a resource, that resource is valid.
    /// See [`Resource::validate`] for more details
    pub proof fn validate(tracked &self)
        ensures
            self.value().valid(),
    {
        use_type_invariant(self);
        self.pcm.validate();
    }

    /// This is useful when you have two (or more) shared resources and want to learn
    /// that they agree, as you can combine this validate, e.g., `x.join_shared(y).validate()`.
    pub proof fn join_shared(tracked &self, tracked other: &Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            incl(self.value(), out.value()) || self.value() == out.value(),
            incl(other.value(), out.value()) || other.value() == out.value(),
    {
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked pcm = self.pcm.join_shared(&other.pcm);
        assert(pcm.value() is Some);
        assert(incl(Some(self.value()), pcm.value()));
        assert(incl(Some(other.value()), pcm.value()));
        lemma_incl_opt_rev(self.value(), pcm.value()->Some_0);
        lemma_incl_opt_rev(other.value(), pcm.value()->Some_0);
        ResourceRef { pcm }
    }

    /// Extract a shared reference to a preceding element in the extension order from a shared reference.
    pub proof fn weaken(tracked &self, target: RA) -> (tracked out: ResourceRef<'a, RA>)
        requires
            incl(target, self.value()),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    {
        use_type_invariant(self);
        lemma_incl_opt(target, self.value());
        let tracked pcm = self.pcm.weaken(Some(target));
        ResourceRef { pcm }
    }

    /// If `x --> x · y` is a frame-perserving update, and we have a shared reference to `x`,
    /// we can create a resource to y
    pub proof fn duplicate_previous(tracked &self, value: RA) -> (tracked out: Resource<RA>)
        requires
            frame_preserving_update_opt(self.value(), RA::op(value, self.value())),
        ensures
            out.loc() == self.loc(),
            out.value() == value,
    {
        use_type_invariant(self);
        let b = RA::op(value, self.value());
        lemma_frame_preserving_opt(self.value(), b);
        let tracked pcm = self.pcm.duplicate_previous(Some(value));
        Resource { pcm }
    }

    /// We can do a similar update to [`update_with_shared`](Resource::update_with_shared) for non-deterministic updates
    pub proof fn join_shared_to_target(
        tracked &self,
        tracked other: &Self,
        target: RA,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            conjunct_shared(Some(self.value()), Some(other.value()), Some(target)),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    {
        let tracked joined = self.join_shared(other);
        joined.validate();
        assert(Some(joined.value()).valid());
        if self.value() == joined.value() {
            Some(self.value()).op_unit();
            assert(incl(Some(self.value()), Some(joined.value())));
        } else {
            lemma_incl_opt(self.value(), joined.value());
        }
        if other.value() == joined.value() {
            Some(other.value()).op_unit();
            assert(incl(Some(other.value()), Some(joined.value())));
        } else {
            lemma_incl_opt(other.value(), joined.value());
        }
        assert(incl(Some(target), Some(joined.value())));
        lemma_incl_opt_rev(target, joined.value());
        if joined.value() == target {
            joined
        } else {
            joined.weaken(target)
        }
    }
}

} // verus!
