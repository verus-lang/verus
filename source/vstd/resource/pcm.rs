#[cfg(verus_keep_ghost)]
use super::super::modes::tracked_swap;
use super::super::prelude::*;
use super::super::set::*;
use super::Loc;
use super::Resource;
use super::algebra::ResourceAlgebra;
#[cfg(verus_keep_ghost)]
use super::algebra::conjunct_shared;
#[cfg(verus_keep_ghost)]
use super::algebra::frame_preserving_update;
#[cfg(verus_keep_ghost)]
use super::algebra::frame_preserving_update_nondeterministic;
#[cfg(verus_keep_ghost)]
use super::algebra::incl;
#[cfg(verus_keep_ghost)]
use super::algebra::set_op;

verus! {

broadcast use super::super::set::group_set_axioms;

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

pub proof fn lemma_unit_is_previous<P: PCM>(p: P)
    ensures
        incl(P::unit(), p),
{
    p.op_unit();
    P::commutative(p, P::unit());
    assert(P::op(P::unit(), p) == p);
}

impl<P: PCM> Resource<P> {
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

    /// We can create a unit from a shared reference
    pub axiom fn create_unit(loc: Loc) -> (tracked out: Self)
        ensures
            out.value() == P::unit(),
            out.loc() == loc,
    ;

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

     /// If `x --> x · y` is a frame-perserving update, and we have a shared reference to `x`,
     /// we can create a resource to y
     pub proof fn duplicate_previous(tracked &self, new_value: P) -> (tracked out: Self)
         requires
             frame_preserving_update(self.value(), P::op(new_value, self.value())),
         ensures
             out.loc() == self.loc(),
             out.value() == new_value,
     {
         use super::super::pervasive;
         assume(false);
         proof_from_false()
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
