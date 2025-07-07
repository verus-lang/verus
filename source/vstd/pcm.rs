use super::prelude::*;
use super::set::*;

verus! {

broadcast use super::set::group_set_axioms;
/** Interface for PCM / Resource Algebra ghost state.

RA-based ghost state is a well-established theory that is especially
useful for verifying concurrent code. An introduction to the concept
can be found in
[Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning](https://iris-project.org/pdfs/2015-popl-iris1-final.pdf)
or
[Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf).

To embed the concept into Verus, we:
 * Use a trait, [`PCM`], to embed the well-formedness laws of a resource algebra
 * use a "tracked ghost" object, `Resource<P>` (this page) to represent ownership of a resource.

Most operations are fairly standard, just "translated" from the usual CSL presentation into Verus.

 * [`alloc`](Self::alloc) to allocate a resource.
 * [`join`](Self::join) to combine two resources via `P::op`, and [`split`](Self::split), its inverse.
 * [`validate`](Self::validate) to assert the validity of any held resource.
 * [`update`](Self::update) or [`update_nondeterministic`](Self::update_nondeterministic) to perform a frame-preserving update.

The interface also includes a nontrivial extension for working with _shared references_ to resources.
Shared resources do not compose in a "separating" way via `P::op`, but rather, in a "potentially overlapping" way ([`join_shared`](Self::join_shared)). Shared resources can also be used to "help" perform frame-preserving updates, as long as they themselves do not change ([`update_with_shared`](Self::update_with_shared)).

### Examples

See:
 * Any of the examples in [this directory](https://github.com/verus-lang/verus/tree/main/examples/pcm)
 * The source code for the [fractional resource library](super::tokens::frac::FracGhost)

### See also

The ["storage protocol"](super::storage_protocol::StorageResource) formalism
is an even more significant
extension with additional capabilities for interacting with shared resources.

[VerusSync](https://verus-lang.github.io/verus/state_machines/intro.html) provides a higher-level
"swiss army knife" for building useful ghost resources.
*/

#[verifier::external_body]
#[verifier::accept_recursive_types(P)]
pub tracked struct Resource<P> {
    p: core::marker::PhantomData<P>,
}

pub type Loc = int;

/// See [`Resource`] for more information.
pub trait PCM: Sized {
    spec fn valid(self) -> bool;

    spec fn op(self, other: Self) -> Self;

    spec fn unit() -> Self;

    proof fn closed_under_incl(a: Self, b: Self)
        requires
            Self::op(a, b).valid(),
        ensures
            a.valid(),
    ;

    proof fn commutative(a: Self, b: Self)
        ensures
            Self::op(a, b) == Self::op(b, a),
    ;

    proof fn associative(a: Self, b: Self, c: Self)
        ensures
            Self::op(a, Self::op(b, c)) == Self::op(Self::op(a, b), c),
    ;

    proof fn op_unit(a: Self)
        ensures
            Self::op(a, Self::unit()) == a,
    ;

    proof fn unit_valid()
        ensures
            Self::valid(Self::unit()),
    ;
}

pub open spec fn incl<P: PCM>(a: P, b: P) -> bool {
    exists|c| P::op(a, c) == b
}

pub open spec fn conjunct_shared<P: PCM>(a: P, b: P, c: P) -> bool {
    forall|p: P| p.valid() && incl(a, p) && incl(b, p) ==> #[trigger] incl(c, p)
}

pub open spec fn frame_preserving_update<P: PCM>(a: P, b: P) -> bool {
    forall|c| #![trigger P::op(a, c), P::op(b, c)] P::op(a, c).valid() ==> P::op(b, c).valid()
}

pub open spec fn frame_preserving_update_nondeterministic<P: PCM>(a: P, bs: Set<P>) -> bool {
    forall|c|
        #![trigger P::op(a, c)]
        P::op(a, c).valid() ==> exists|b| #[trigger] bs.contains(b) && P::op(b, c).valid()
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
