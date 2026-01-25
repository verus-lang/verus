use super::super::modes::*;
use super::super::prelude::*;
use super::Loc;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;
use super::pcm::Resource;
use super::storage_protocol::*;
use super::*;

verus! {

broadcast use {super::super::map::group_map_axioms, super::super::set::group_set_axioms};

enum FractionalCarrier<T> {
    Value { v: T, frac: real },
    Empty,
    Invalid,
}

impl<T> FractionalCarrier<T> {
    spec fn new(v: T) -> Self {
        FractionalCarrier::Value { v: v, frac: (1 as real) }
    }
}

impl<T> ResourceAlgebra for FractionalCarrier<T> {
    closed spec fn valid(self) -> bool {
        match self {
            FractionalCarrier::Invalid => false,
            FractionalCarrier::Empty => true,
            FractionalCarrier::Value { frac, .. } => (0 as real) < frac <= (1 as real),
        }
    }

    closed spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (FractionalCarrier::Invalid, _) => FractionalCarrier::Invalid,
            (_, FractionalCarrier::Invalid) => FractionalCarrier::Invalid,
            (FractionalCarrier::Empty, _) => b,
            (_, FractionalCarrier::Empty) => a,
            (
                FractionalCarrier::Value { v: a_v, frac: a_frac },
                FractionalCarrier::Value { v: b_v, frac: b_frac },
            ) => {
                if a_v != b_v {
                    FractionalCarrier::Invalid
                } else if a_frac <= (0 as real) || b_frac <= (0 as real) {
                    FractionalCarrier::Invalid
                } else if a_frac + b_frac > (1 as real) {
                    FractionalCarrier::Invalid
                } else {
                    FractionalCarrier::Value { v: a_v, frac: a_frac + b_frac }
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

impl<T> PCM for FractionalCarrier<T> {
    closed spec fn unit() -> Self {
        FractionalCarrier::Empty
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

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
        self.r.value() is Value
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> T {
        self.r.value()->v
    }

    /// The fractional quantity of this permission
    pub closed spec fn frac(self) -> real {
        self.r.value()->frac
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
        let f = FractionalCarrier::<T>::new(v);
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
        let tracked joined = self.r.join_shared(&other.r);
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
            FractionalCarrier::Value { v: mself.r.value()->v, frac: self_frac - result_frac },
            FractionalCarrier::Value { v: mself.r.value()->v, frac: result_frac },
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
        r.validate_2(&other.r);
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
        let f = FractionalCarrier::<T>::Value { v, frac: (1 as real) };
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
