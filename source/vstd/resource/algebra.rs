use super::super::modes::*;
use super::super::prelude::*;
use super::super::set::*;
use super::Loc;
use super::Resource;

verus! {

broadcast use super::super::set::group_set_axioms;

/// A Resource Algebra operating on a type T
///
/// This construction is based off the [Iris from the Ground Up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)
/// report.
///
/// A striking difference is that we mandate that all elements have a core belonging to the set,
/// obviating the need for lifting the set (in this case, the type T) into a T ⨄ {⊥ }, so that bottom
/// can serve as the unit. This could be emulated by adding the bottom element (which can serve as
/// the core in the lifting for elements of T without a core)
///
/// See [`Resource`] for more information.
// TODO(bsdinis): it should probably not be required that ghost things be sized, but that sounds
// like a relatively complicated change -- needs to be done across the codebase
pub trait ResourceAlgebra: Sized {
    /// Whether an element is valid
    spec fn valid(self) -> bool;

    /// Compose two elements
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

/// This relation defines the extension order ≼. `a ≼ b` means that there is some element `c` such
/// that `RA::op(a, c) == b`.
pub open spec fn incl<RA: ResourceAlgebra>(a: RA, b: RA) -> bool {
    exists|c| RA::op(a, c) == b
}

/// A frame preserving update means that changing a carrier value `a` to `b` does not restrict the
/// set of values `c` that can compose with it, i.e., if `op(a, c)` was valid so will `op(b, c)`.
pub open spec fn frame_preserving_update<RA: ResourceAlgebra>(a: RA, b: RA) -> bool {
    forall|c| #![trigger RA::op(a, c), RA::op(b, c)] RA::op(a, c).valid() ==> RA::op(b, c).valid()
}

/// A non-deterministic frame preserving update. It is related to [`frame_preserving_update`] but
/// relates to a set of possible values `bs` that `a` can be updated into.
pub open spec fn frame_preserving_update_nondeterministic<RA: ResourceAlgebra>(
    a: RA,
    bs: Set<RA>,
) -> bool {
    forall|c|
        #![trigger RA::op(a, c)]
        RA::op(a, c).valid() ==> exists|b| #[trigger] bs.contains(b) && RA::op(b, c).valid()
}

/// This relation asserts the claim that if a valid p extends a and b, then it will also extend c.
/// See [`join_shared`](Resource::join_shared) and [`join_shared_to_target`](Resource::join_shared_to_target) for more details.
pub open spec fn conjunct_shared<RA: ResourceAlgebra>(a: RA, b: RA, c: RA) -> bool {
    forall|p: RA| p.valid() && incl::<RA>(a, p) && incl::<RA>(b, p) ==> #[trigger] incl::<RA>(c, p)
}

/// The set of values that can be constructed by combining a value in s with t
pub open spec fn set_op<RA: ResourceAlgebra>(s: Set<RA>, t: RA) -> Set<RA> {
    // s.map(|a| RA::op(a, t))
    Set::new(|v| exists|q| s.contains(q) && v == RA::op(q, t))
}

/// Implementation of a [`Resource`] based on a [`ResourceAlgebra`]
// This follows roughly the Iris from the Ground up construction
impl<RA: ResourceAlgebra> Resource<RA> {
    pub uninterp spec fn value(self) -> RA;

    pub uninterp spec fn loc(self) -> Loc;

    /// We can allocate a new resource at a fresh location
    // GHOST-ALLOC rule
    pub axiom fn alloc(value: RA) -> (tracked out: Self)
        requires
            value.valid(),
        ensures
            out.value() == value,
    ;

    /// We can join together two resources at the same location, where we obtain the combination of
    /// the two
    // reverse implication in the GHOST-OP rule
    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.value() == RA::op(self.value(), other.value()),
    ;

    /// If a resource holds the result of a composition, we can split it into the components
    // implication in the GHOST-OP rule
    pub axiom fn split(tracked self, left: RA, right: RA) -> (tracked out: (Self, Self))
        requires
            self.value() == RA::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == left,
            out.1.value() == right,
    ;

    /// Whenever we have a resource, that resource is valid. This intuitively holds because:
    ///     1. We only create valid resources (either via [`alloc`] or
    ///        [`create_unit`](Resource::create_unit)).
    ///     2. We can only update the value of a resource via a [`frame_preserving_update`] (see
    ///        [`update`](Self::update) for more details.
    // GHOST-VALID rule
    pub axiom fn validate(tracked &self)
        ensures
            self.value().valid(),
    ;

    /// If `x --> y` is a [`frame_preserving_update`] (i.e., anything that could compose with `x`
    /// can also compose with `y`), then we can update the resource to `y`.
    // variant of the GHOST-UPDATE rule
    pub proof fn update(tracked self, new_value: RA) -> (tracked out: Self)
        requires
            frame_preserving_update::<RA>(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        let new_values = set![new_value];
        assert(new_values.contains(new_value));
        self.update_nondeterministic(new_values)
    }

    /// This is a more general version of [`update`](Self::update).
    // GHOST-UPDATE rule
    pub axiom fn update_nondeterministic(tracked self, new_values: Set<RA>) -> (tracked out: Self)
        requires
            frame_preserving_update_nondeterministic::<RA>(self.value(), new_values),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    ;

    /// Extracts the resource from `r`, leaving `r` unspecified and returning a new resource
    /// holding the previous value of `r`.
    pub proof fn extract(tracked &mut self) -> (tracked out: Resource<RA>)
        ensures
            out.loc() == old(self).loc(),
            out.value() == old(self).value(),
    {
        self.validate();
        // allocate a new resource as a dummy
        let tracked mut out = Self::alloc(self.value());

        // and is swapped
        tracked_swap(self, &mut out);

        out
    }

    // Operations with shared references
    /// This is useful when you have two (or more) shared resources and want to learn
    /// that they agree, as you can combine this validate, e.g., `x.join_shared(y).validate()`.
    pub axiom fn join_shared<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked out:
        &'a Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            incl::<RA>(self.value(), out.value()),
            incl::<RA>(other.value(), out.value()),
    ;

    /// Similar to [`join_shared`](Self::join_shared) but with an explicit target given
    pub proof fn join_shared_to_target<'a>(
        tracked &'a self,
        tracked other: &'a Self,
        target: RA,
    ) -> (tracked out: &'a Self)
        requires
            self.loc() == other.loc(),
            conjunct_shared::<RA>(self.value(), other.value(), target),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    {
        let tracked j = self.join_shared(other);
        j.validate();
        j.weaken(target)
    }

    /// Given a shared reference to a resource, we can get a shared reference to any previous
    /// values (in the extension order)
    pub axiom fn weaken<'a>(tracked &'a self, target: RA) -> (tracked out: &'a Self)
        requires
            incl::<RA>(target, self.value()),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    ;

    /// Validate two items at once. If we have two resources at the same location then its
    /// composition is valid.
    pub axiom fn validate_2(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            self.loc() == old(self).loc(),
            self.value() == old(self).value(),
            RA::op(self.value(), other.value()).valid(),
    ;

    /// If `x · y --> x · z` is a frame-perserving update, and we have a shared reference to `x`,
    /// we can update the `y` resource to `z`.
    pub proof fn update_with_shared(
        tracked self,
        tracked other: &Self,
        new_value: RA,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_preserving_update::<RA>(
                RA::op(self.value(), other.value()),
                RA::op(new_value, other.value()),
            ),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        let new_values = set![new_value];
        let so = set_op::<RA>(new_values, other.value());
        assert(so.contains(RA::op(new_value, other.value())));
        self.update_nondeterministic_with_shared(other, new_values)
    }

    /// We can do a similar update to [`update_with_shared`](Self::update_with_shared) for non-deterministic updates
    pub axiom fn update_nondeterministic_with_shared(
        tracked self,
        tracked other: &Self,
        new_values: Set<RA>,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_preserving_update_nondeterministic::<RA>(
                RA::op(self.value(), other.value()),
                set_op::<RA>(new_values, other.value()),
            ),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    ;
}

} // verus!
