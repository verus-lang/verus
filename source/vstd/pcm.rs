use super::prelude::*;
use super::set::*;

verus! {

/// Interface for ghost state that is consistent with the common
/// presentations of partially commutative monoids (PCMs) / resource algebras.
///
/// For applications, the general advice is to use the
/// [`tokenized_state_machine!` system](https://verus-lang.github.io/verus/state_machines/),
/// which lets you focus on updates and invariants rather than composition.
///
/// However, the PCM interface you'll find here may be more familiar to people.
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
    pub open spec fn value(self) -> P;

    pub open spec fn loc(self) -> Loc;

    #[verifier::external_body]
    pub proof fn alloc(value: P) -> (tracked out: Self)
        requires
            value.valid(),
        ensures
            out.value() == value,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.value() == P::op(self.value(), other.value()),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn split(tracked self, left: P, right: P) -> (tracked out: (Self, Self))
        requires
            self.value() == P::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == left,
            out.1.value() == right,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn create_unit(loc: Loc) -> (tracked out: Self)
        ensures
            out.value() == P::unit(),
            out.loc() == loc,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn validate(tracked &self)
        ensures
            self.value().valid(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn update(tracked self, new_value: P) -> (tracked out: Self)
        requires
            frame_preserving_update(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn update_nondeterministic(tracked self, new_values: Set<P>) -> (tracked out: Self)
        requires
            frame_preserving_update_nondeterministic(self.value(), new_values),
        ensures
            out.loc() == self.loc(),
            new_values.contains(out.value()),
    {
        unimplemented!();
    }

    // Operations with shared references
    #[verifier::external_body]
    pub proof fn join_shared<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked out:
        &'a Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            incl(self.value(), out.value()),
            incl(other.value(), out.value()),
    {
        unimplemented!();
    }

    #[verifier::external_body]
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
        self.join_shared(other).weaken(target)
    }

    #[verifier::external_body]
    pub proof fn weaken<'a>(tracked &'a self, target: P) -> (tracked out: &'a Self)
        requires
            incl(target, self.value()),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn validate_2(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            *self == *old(self),
            P::op(self.value(), other.value()).valid(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
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
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn update_nondeterministic_with_shared(
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
    {
        unimplemented!();
    }
}

} // verus!
