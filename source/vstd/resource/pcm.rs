use super::super::prelude::*;
use super::Loc;
use super::algebra::ResourceAlgebra;
use super::relations::*;
use super::trusted;

#[cfg(verus_keep_ghost)]
use super::super::modes::tracked_swap;

verus! {

broadcast use super::super::iset::group_iset_lemmas;

/// Interface for PCM / Resource Algebra ghost state.
///
/// RA-based ghost state is a well-established theory that is especially
/// useful for verifying concurrent code. An introduction to the concept
/// can be found in
/// [Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning](https://iris-project.org/pdfs/2015-popl-iris1-final.pdf)
/// or
/// [Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf).
///
/// To embed the concept into Verus, we:
///  * Use a trait, [`PCM`], to embed the well-formedness laws of a resource algebra
///  * use a "tracked ghost" object, `Resource<P>` (this page) to represent ownership of a resource.
///
/// Most operations are fairly standard, just "translated" from the usual CSL presentation into Verus.
///
///  * [`alloc`](Self::alloc) to allocate a resource.
///  * [`join`](Self::join) to combine two resources via `P::op`, and [`split`](Self::split), its inverse.
///  * [`validate`](Self::validate) to assert the validity of any held resource.
///  * [`update`](Self::update) or [`update_nondeterministic`](Self::update_nondeterministic) to perform a frame-preserving update.
///
/// The interface also includes a nontrivial extension for working with _shared references_ to resources.
/// Shared resources do not compose in a "separating" way via `P::op`, but rather, in a "potentially overlapping" way ([`join_shared`](Self::join_shared)). Shared resources can also be used to "help" perform frame-preserving updates, as long as they themselves do not change ([`update_with_shared`](Self::update_with_shared)).
///
/// ### Examples
///
/// See:
///  * Any of the examples in [this directory](https://github.com/verus-lang/verus/tree/main/examples/pcm)
///  * The source code for the [fractional resource library](super::frac::FracGhost)
///
/// ### See also
///
/// The ["storage protocol"](super::storage_protocol::StorageResource) formalism
/// is an even more significant
/// extension with additional capabilities for interacting with shared resources.
///
/// [VerusSync](https://verus-lang.github.io/verus/state_machines/intro.html) provides a higher-level
/// "swiss army knife" for building useful ghost resources.
#[verifier::accept_recursive_types(P)]
pub tracked struct Resource<P: PCM> {
    r: trusted::ra::Resource<P>,
}

#[cfg(verus_keep_ghost)]
#[verifier::external]
impl<P: PCM> !Copy for Resource<P> {

}

#[verifier::accept_recursive_types(P)]
pub tracked struct CopyableResource<P: PCM> {
    tracked r: trusted::ra::CopyableResource<P>,
}

impl<P: PCM> Copy for CopyableResource<P> {

}

impl<P: PCM> Clone for CopyableResource<P> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        *self
    }
}

/// A Partial Commutative Monoid is a special type of [`ResourceAlgebra`], where all elements have
/// the same core (which belongs in the carrier), the unit. For this reason, they are also called
/// unitary resource algebras[^note].
///
/// [^note]: This is slightly misleading. PCMs are partial in the sense that the operation is not
/// defined for certain inputs. Because Verus does not support partial functions, we model that
/// partiality with the validity predicate, which does make it a unitary resource algebra.
pub trait PCM: ResourceAlgebra {
    /// The unit of the monoid, i.e., the carrier value that composed with any other carrier value
    /// yields the identity function
    spec fn unit() -> Self;

    /// The core of an element `a` is, by definition, some other element `x`
    /// such that `a · x = a`
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

/// Every [`PCM`] is an [`RA`](trusted::ra::RA) in the sense of the trusted interface.
impl<P: PCM> trusted::ra::RA for P {
    open spec fn valid(self) -> bool {
        <P as ResourceAlgebra>::valid(self)
    }

    open spec fn op(a: Self, b: Self) -> Self {
        <P as ResourceAlgebra>::op(a, b)
    }

    open spec fn unit() -> Self {
        <P as PCM>::unit()
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        <P as ResourceAlgebra>::associative(a, b, c);
    }

    proof fn commutative(a: Self, b: Self) {
        <P as ResourceAlgebra>::commutative(a, b);
    }

    proof fn valid_op(a: Self, b: Self) {
        <P as ResourceAlgebra>::valid_op(a, b);
    }

    proof fn op_unit(self) {
        <P as PCM>::op_unit(self);
    }

    proof fn unit_valid() {
        <P as PCM>::unit_valid();
    }
}

impl<P: PCM> Resource<P> {
    /// The underlying value of the resource
    pub closed spec fn value(self) -> P {
        self.r.value()
    }

    /// The location of the resource
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    proof fn mk_ref<'a>(tracked r: &'a trusted::ra::Resource<P>) -> (tracked res: &'a Self)
        ensures
            res.r == r,
    {
        shr_ref_struct_wrap(r, &Self { r: arbitrary() }, "", "r")
    }

    /// Allocate a new resource at a fresh location
    // GHOST-ALLOC rule
    pub proof fn alloc(value: P) -> (tracked out: Self)
        requires
            value.valid(),
        ensures
            out.value() == value,
    {
        Resource { r: trusted::ra::Resource::alloc(value) }
    }

    /// We can join together two resources at the same location, where we obtain the combination of
    /// the two
    // reverse implication in the GHOST-OP rule
    pub proof fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.value() == P::op(self.value(), other.value()),
    {
        Resource { r: self.r.join(other.r) }
    }

    /// If a resource holds the result of a composition, we can split it into the components
    // implication in the GHOST-OP rule
    pub proof fn split(tracked self, left: P, right: P) -> (tracked out: (Self, Self))
        requires
            self.value() == P::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == left,
            out.1.value() == right,
    {
        let tracked (a, b) = self.r.split(left, right);
        (Resource { r: a }, Resource { r: b })
    }

    /// Create a unit at a particular location
    pub proof fn create_unit(loc: Loc) -> (tracked out: Self)
        ensures
            out.value() == P::unit(),
            out.loc() == loc,
    {
        Resource { r: trusted::ra::Resource::create_unit(loc) }
    }

    /// Whenever we have a resource, that resource is valid. This intuitively (and inductively)
    /// holds because:
    ///     1. We only create valid resources (either via [`alloc`] or
    ///        [`create_unit`](Self::create_unit)).
    ///     2. We can only update the value of a resource via a [`frame_preserving_update`] (see
    ///        [`update`](Self::update) for more details. Because of the requirement of that
    ///        updates are frame preserving this means that `join`s remain valid.
    // GHOST-VALID rule
    pub proof fn validate(tracked &self)
        ensures
            self.value().valid(),
    {
        self.r.validate()
    }

    /// This is a more general version of [`update`](Self::update).
    // GHOST-UPDATE rule
    pub proof fn update_nondeterministic(tracked self, new_values: ISet<P>) -> (tracked out: Self)
        requires
            frame_preserving_update_nondeterministic(self.value(), new_values),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    {
        let tracked u = Self::create_unit(self.loc());
        PCM::op_unit(self.value());
        assert(set_op(new_values, u.value()) =~= new_values) by {
            assert forall|x|
                set_op(new_values, u.value()).contains(x) <==> #[trigger] new_values.contains(
                    x,
                ) by {
                PCM::op_unit(x);
                if set_op(new_values, u.value()).contains(x) {
                    let q = choose|q| #[trigger] new_values.contains(q) && x == P::op(q, u.value());
                    PCM::op_unit(q);
                }
            }
        };
        self.update_nondeterministic_with_shared(&u, new_values)
    }

    // VERIFIED
    /// Update a resource to a new value. This can only be done if the update is frame preserving
    /// (i.e., any value that could be composed with the original value can still be composed with
    /// the new value).
    ///
    /// See [`frame_preserving_update`] for more information.
    // variant of the GHOST-UPDATE rule
    pub proof fn update(tracked self, new_value: P) -> (tracked out: Self)
        requires
            frame_preserving_update(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        let new_values = iset![new_value];
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

    // Operations with shared references
    /// This is useful when you have two (or more) shared resources and want to learn
    /// that they agree, as you can combine this validate, e.g., `x.join_shared(y).validate()`.
    pub proof fn join_shared<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked out:
        &'a Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            incl(self.value(), out.value()),
            incl(other.value(), out.value()),
    {
        Self::mk_ref(self.r.join_shared(&other.r))
    }

    /// Extract a shared reference to a preceding element in the extension order from a shared reference.
    pub proof fn weaken<'a>(tracked &'a self, target: P) -> (tracked out: &'a Self)
        requires
            incl(target, self.value()),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    {
        let c = choose|c| P::op(target, c) == self.value();
        assert(<P as trusted::ra::RA>::op(target, c) == self.value());
        Self::mk_ref(self.r.weaken(target))
    }

    /// Validate two items at once. If we have two resources at the same location then its
    /// composition is valid.
    pub proof fn validate_2(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            *final(self) == *old(self),
            P::op(final(self).value(), other.value()).valid(),
    {
        self.r.validate_2(&other.r)
    }

    /// We can do a similar update to [`update_with_shared`](Self::update_with_shared) for non-deterministic updates
    pub proof fn update_nondeterministic_with_shared(
        tracked self,
        tracked other: &Self,
        new_values: ISet<P>,
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
    {
        let ghost bs = set_op(new_values, other.value());
        let ghost f = |c: P| choose|b: P| #[trigger] bs.contains(b) && P::op(b, c).valid();
        assert(trusted::ra::set_op(new_values, other.value()) =~= bs);
        Resource { r: self.r.update_nondeterministic_with_shared(&other.r, new_values, f) }
    }

    // VERIFIED facts about shared references
    /// We can do a similar update to [`update_with_shared`](Self::update_with_shared) for non-deterministic updates
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
        let new_values = iset![new_value];
        let so = set_op(new_values, other.value());
        assert(so.contains(P::op(new_value, other.value())));
        self.update_nondeterministic_with_shared(other, new_values)
    }

    /// If `x --> x · y` is a frame-perserving update, and we have a shared reference to `x`,
    /// we can create a resource to y
    pub proof fn duplicate_previous(tracked &self, value: P) -> (tracked out: Self)
        requires
            frame_preserving_update(self.value(), P::op(value, self.value())),
        ensures
            out.loc() == self.loc(),
            out.value() == value,
    {
        let tracked mut unit = Self::create_unit(self.loc());
        self.value().op_unit();
        P::commutative(self.value(), unit.value());
        unit.update_with_shared(self, value)
    }

    /// Wrap this resource in a type that implements `Copy`,
    /// given that the resource is duplicable.
    pub proof fn into_copyable(tracked self, p: P) -> (tracked r: CopyableResource<P>)
        requires
            P::op(P::op(self.value(), self.value()), p) == self.value(),
        ensures
            r.loc() == self.loc(),
            r.value() == self.value(),
    {
        CopyableResource { r: self.r.into_copyable(p) }
    }
}

/// A variant of [`Resource`] that implements `Copy`.
///
/// Use [`Self::into_resource`] to get the underlying resource.
impl<P: PCM> CopyableResource<P> {
    /// The underlying value of the resource
    pub closed spec fn value(self) -> P {
        self.r.value()
    }

    /// The location of the resource
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub proof fn into_resource(tracked self) -> (tracked r: Resource<P>)
        ensures
            r.loc() == self.loc(),
            r.value() == self.value(),
    {
        Resource { r: self.r.into_resource() }
    }
}

} // verus!
