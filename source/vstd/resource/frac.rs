use super::super::modes::*;
use super::super::prelude::*;
use super::Loc;
use super::agree::AgreementRA;
use super::algebra::Resource;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;
use super::product::ProductRA;
use super::storage_protocol::*;
use super::*;

verus! {

broadcast use {super::super::map::group_map_axioms, super::super::set::group_set_axioms};

pub enum FractionRA {
    Frac(real),
    Invalid,
}

impl FractionRA {
    pub open spec fn new(f: real) -> Self
        recommends
            0real < f <= 1real,
    {
        FractionRA::Frac(f)
    }

    pub open spec fn frac(self) -> real
        recommends
            self is Frac,
    {
        self->Frac_0
    }
}

impl ResourceAlgebra for FractionRA {
    open spec fn valid(self) -> bool {
        match self {
            FractionRA::Invalid => false,
            FractionRA::Frac(frac) => (0 as real) < frac <= (1 as real),
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (FractionRA::Invalid, _) => FractionRA::Invalid,
            (_, FractionRA::Invalid) => FractionRA::Invalid,
            (FractionRA::Frac(a_frac), FractionRA::Frac(b_frac)) => {
                if !a.valid() || !b.valid() {
                    FractionRA::Invalid
                } else if a_frac + b_frac <= (1 as real) {
                    FractionRA::Frac(a_frac + b_frac)
                } else {
                    FractionRA::Invalid
                }
            },
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

pub proof fn lemma_whole_fraction_has_no_frame(a: FractionRA)
    requires
        a == FractionRA::Frac(1 as real),
    ensures
        forall|b: FractionRA|
            #![trigger FractionRA::op(a, b).valid()]
            !FractionRA::op(a, b).valid(),
{
    assert forall|b: FractionRA|
        #![trigger FractionRA::op(a, b).valid()]
        !FractionRA::op(a, b).valid() by {
        if FractionRA::op(a, b).valid() {
            FractionRA::commutative(a, b);
            FractionRA::valid_op(b, a);
            assert(b.valid());
            assert(b is Frac);
            assert((0 as real) < b->Frac_0 <= (1 as real));
            assert(a->Frac_0 + b->Frac_0 > (1 as real));  // CONTRADICTION
        };
    }
}

type FractionalCarrier<T> = ProductRA<FractionRA, AgreementRA<T>>;

/// An implementation of a resource for fractional ownership of a ghost variable.
///
/// If you just want to split the permission in half, you can also use the
/// [`GhostVar<T>`](super::ghost_var::GhostVar) and [`GhostVarAuth<T>`](super::ghost_var::GhostVarAuth) library.
///
/// ### Example
///
/// ```
/// fn example_use() {
///     let tracked mut r = FracGhost::<u64>::new(123);
///     assert(r@ == 123);
///     assert(r.frac() == 1 as real);
///     let tracked r2 = r.split();
///     assert(r@ == 123);
///     assert(r2@ == 123);
///     assert(r.frac() == (0.5 as real));
///     assert(r2.frac() == (0.5 as real));
///     proof {
///         r.combine(r2);
///         r.update(456);
///     }
///     assert(r@ == 456);
///     assert(r.frac() == 3 as real);
///
///     let tracked mut a = FracGhost::<u32>::new(5);
///     assert(a@ == 5);
///     assert(a.frac() == 1real);
///     let tracked mut b = a.split();
///     assert(a.frac() == (0.5 as real));
///     assert(b.frac() == (0.5 as real));
///     proof {
///         a.update_with(&mut b, 123);
///     }
///     assert(a@ == 123);
///
///     proof {
///         a.combine(b);
///         a.update(6);
///     }
///     assert(a@ == 6);
/// }
/// ```
pub tracked struct FracGhost<T> {
    r: Resource<FractionalCarrier<T>>,
}

impl<T> FracGhost<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().left is Frac
        &&& self.r.value().right is Agree
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> T {
        self.r.value().right->Agree_0
    }

    /// The fractional quantity of this permission
    pub closed spec fn frac(self) -> real {
        self.r.value().left->Frac_0
    }

    pub open spec fn valid(self, id: Loc, frac: real) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    /// Allocate a new resource with the given value.
    pub proof fn new(v: T) -> (tracked result: Self)
        ensures
            result.frac() == 1 as real,
            result@ == v,
    {
        let f = FractionalCarrier {
            left: FractionRA::Frac(1 as real),
            right: AgreementRA::Agree(v),
        };
        let tracked r = Resource::alloc(f);
        Self { r }
    }

    /// Two resources agree on their values.
    pub proof fn agree(tracked self: &Self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self@ == other@,
    {
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked joined = self.r.as_ref().join_shared(&other.r.as_ref());
        joined.validate()
    }

    /// Take a token out of a mutable reference, leaving a meaningless token behind.
    pub proof fn take(tracked &mut self) -> (tracked result: Self)
        ensures
            result == *old(self),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        mself
    }

    /// Split one resource into two. Both the returned resource and self have half of the original
    /// fraction.
    pub proof fn split_to(tracked &mut self, result_frac: real) -> (tracked result: Self)
        requires
            (0 as real) < result_frac < old(self).frac(),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            self@ == old(self)@,
            result@ == old(self)@,
            self.frac() == old(self).frac() - result_frac,
            result.frac() == result_frac,
    {
        self.bounded();
        let self_frac = self.frac();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        let tracked (r1, r2) = mself.r.split(
            FractionalCarrier {
                left: FractionRA::Frac(self_frac - result_frac),
                right: AgreementRA::Agree(mself@),
            },
            FractionalCarrier {
                left: FractionRA::Frac(result_frac),
                right: AgreementRA::Agree(mself@),
            },
        );
        self.r = r1;
        Self { r: r2 }
    }

    /// Split one resource into two. Both the returned resource and self have half of the original
    /// fraction.
    pub proof fn split(tracked &mut self) -> (tracked result: Self)
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            self@ == old(self)@,
            result@ == old(self)@,
            self.frac() == old(self).frac() / 2 as real,
            result.frac() == old(self).frac() / 2 as real,
    {
        self.bounded();
        self.split_to(self.frac() / 2 as real)
    }

    /// Combine two resources, summing their quantities.
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@ == other@,
            self.frac() == old(self).frac() + other.frac(),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        use_type_invariant(&other);
        let tracked mut r = mself.r;
        r.validate_2(&other.r.as_ref());
        *self = Self { r: r.join(other.r) };
    }

    /// Update the value of the resource. This requires having ALL the permissions,
    pub proof fn update(tracked &mut self, v: T)
        requires
            old(self).frac() == (1 as real),
        ensures
            self.id() == old(self).id(),
            self@ == v,
            self.frac() == old(self).frac(),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        let tracked mut r = mself.r;
        let f = FractionalCarrier {
            left: FractionRA::Frac(1 as real),
            right: AgreementRA::Agree(v),
        };
        lemma_whole_fraction_has_no_frame(r.value().left);
        *self = Self { r: r.update(f) };
    }

    /// Update the value of the token. This requires having ALL the permissions (i.e., a fractional
    /// authority of 1),
    pub proof fn update_with(tracked &mut self, tracked other: &mut Self, v: T)
        requires
            old(self).id() == old(other).id(),
            old(self).frac() + old(other).frac() == 1 as real,
        ensures
            self.id() == old(self).id(),
            other.id() == old(other).id(),
            self.frac() == old(self).frac(),
            other.frac() == old(other).frac(),
            old(self)@ == old(other)@,
            self@ == v,
            other@ == v,
    {
        let ghost other_frac = other.frac();
        other.bounded();

        let tracked mut xother = Self::dummy();
        tracked_swap(other, &mut xother);
        self.bounded();
        self.combine(xother);
        self.update(v);

        let tracked mut xother = self.split_to(other_frac);
        tracked_swap(other, &mut xother);
    }

    /// Allowed values for a resource's fractional component.
    pub proof fn bounded(tracked &self)
        ensures
            (0 as real) < self.frac() <= (1 as real),
    {
        use_type_invariant(self);
        self.r.validate()
    }

    /// Obtain an arbitrary resource with no information about it.
    /// Useful if you need a well-typed placeholder.
    pub proof fn dummy() -> (tracked result: Self) {
        Self::new(arbitrary())
    }
}

} // verus!
