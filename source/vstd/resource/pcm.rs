use super::super::prelude::*;
use super::super::set::*;
use super::Loc;
use super::Resource;

verus! {

broadcast use super::super::set::group_set_axioms;

/// A Partial Commutative Monoid is a special type of `ResourceAlgebra`, where all elements have
/// the same core (which belongs in the carrier), the unit. For this reason, they are also called
/// unitary resource algebras[^note].
///
/// [^note]: This is slightly misleading. PCMs are partial in the sense that the operation is not
/// defined for certain inputs. Because Verus does not support partial functions, we model that
/// partiality with the validity predicate, which does make it a unitary resource algebra.
// TODO(bsdinis): it should probably not be required that ghost things be sized, but that sounds
// like a relatively complicated change -- needs to be done across the codebase
pub trait PCM: Sized {
    /// Whether an element is valid
    spec fn valid(self) -> bool;

    /// Compose two elements
    spec fn op(a: Self, b: Self) -> Self;

    /// The unit of the monoid, i.e., the carrier value that composed with any other carrier value
    /// yields the identity function
    spec fn unit() -> Self;

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

    /// The core of an element `a` is, by definition, some other element `x`
    /// such that `a op x = a`
    proof fn op_unit(self)
        ensures
            Self::op(self, Self::unit()) == self,
    ;

    /// The unit is always a valid element
    proof fn unit_valid()
        ensures
            Self::unit().valid(),
    ;
}

pub open spec fn incl<P: PCM>(a: P, b: P) -> bool {
    exists|c| P::op(a, c) == b
}

pub open spec fn conjunct_shared<P: PCM>(a: P, b: P, c: P) -> bool {
    forall|p: P| p.valid() && incl(a, p) && incl(b, p) ==> #[trigger] incl(c, p)
}

pub open spec fn frame_preserving_update<P: PCM>(a: P, b: P) -> bool {
    forall|c|
        #![trigger P::op(a, c), P::op(b, c)]
        P::op(a, c).valid() ==> P::op(b, c).valid()
}

pub open spec fn frame_preserving_update_nondeterministic<P: PCM>(a: P, bs: Set<P>) -> bool {
    forall|c|
        #![trigger P::op(a, c)]
        P::op(a, c).valid() ==> exists|b| #[trigger]
            bs.contains(b) && P::op(b, c).valid()
}

pub open spec fn set_op<P: PCM>(s: Set<P>, t: P) -> Set<P> {
    Set::new(|v| exists|q| s.contains(q) && v == P::op(q, t))
}

impl<P: PCM> Resource<P> {
    pub uninterp spec fn value(self) -> P;

    pub uninterp spec fn loc(self) -> Loc;

    pub axiom fn alloc(value: P) -> (tracked out: Self)
        requires
            value.valid(),
        ensures
            out.value() == value,
    ;

    pub axiom fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.value() == P::op(self.value(), other.value()),
    ;

    pub axiom fn split(tracked self, left: P, right: P) -> (tracked out: (Self, Self))
        requires
            self.value() == P::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == left,
            out.1.value() == right,
    ;

    pub axiom fn create_unit(loc: Loc) -> (tracked out: Self)
        ensures
            out.value() == P::unit(),
            out.loc() == loc,
    ;

    pub axiom fn validate(tracked &self)
        ensures
            self.value().valid(),
    ;

    pub proof fn update(tracked self, new_value: P) -> (tracked out: Self)
        requires
            frame_preserving_update(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        let new_values = set![new_value];
        assert(new_values.contains(new_value));
        self.update_nondeterministic(new_values)
    }

    pub axiom fn update_nondeterministic(tracked self, new_values: Set<P>) -> (tracked out: Self)
        requires
            frame_preserving_update_nondeterministic(self.value(), new_values),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    ;

    // Operations with shared references
    /// This is useful when you have two (or more) shared resources and want to learn
    /// that they agree, as you can combine this validate, e.g., `x.join_shared(y).validate()`.
    pub axiom fn join_shared<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked out:
        &'a Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            incl(self.value(), out.value()),
            incl(other.value(), out.value()),
    ;

    pub proof fn join_shared_to_target<'a>(
        tracked &'a self,
        tracked other: &'a Self,
        target: P,
    ) -> (tracked out: &'a Self)
        requires
            self.loc() == other.loc(),
            conjunct_shared(self.value(), other.value(), target),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    {
        let tracked j = self.join_shared(other);
        j.validate();
        j.weaken(target)
    }

    pub axiom fn weaken<'a>(tracked &'a self, target: P) -> (tracked out: &'a Self)
        requires
            incl(target, self.value()),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    ;

    pub axiom fn validate_2(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            *self == *old(self),
            P::op(self.value(), other.value()).valid(),
    ;

    /// If `x · y --> x · z` is a frame-perserving update, and we have a shared reference to `x`,
    /// we can update the `y` resource to `z`.
    pub proof fn update_with_shared(
        tracked self,
        tracked other: &Self,
        new_value: P,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_preserving_update(
                P::op(self.value(), other.value()),
                P::op(new_value, other.value()),
            ),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        let new_values = set![new_value];
        let so = set_op(new_values, other.value());
        assert(so.contains(P::op(new_value, other.value())));
        self.update_nondeterministic_with_shared(other, new_values)
    }

    pub axiom fn update_nondeterministic_with_shared(
        tracked self,
        tracked other: &Self,
        new_values: Set<P>,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_preserving_update_nondeterministic(
                P::op(self.value(), other.value()),
                set_op(new_values, other.value()),
            ),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    ;
}

} // verus!
