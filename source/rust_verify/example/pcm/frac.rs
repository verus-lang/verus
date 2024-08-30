use builtin::*;
use vstd::pcm::*;
use vstd::prelude::*;

// This implements a resource for fractional ownership of a ghost variable.
// The fractions are represented as some number out of a compile-time const
// Total value; you can have any fractions from 1 up to Total, and if you
// have Total, you can update the ghost variable.

verus! {
    // Too bad that `nat` and `int` are forbidden as the type of a const generic parameter
    pub enum Fractional<T, const Total: u64> {
        Value { v: T, n: int },
        Empty,
        Invalid,
    }

    impl<T, const Total: u64> Fractional<T, Total> {
        pub open spec fn new(v: T) -> Self {
            Fractional::Value { v: v, n: Total as int }
        }
    }

    impl<T, const Total: u64> PCM for Fractional<T, Total> {
        open spec fn valid(self) -> bool {
            match self {
                Fractional::Invalid => false,
                Fractional::Empty => true,
                Fractional::Value { v: v, n: n } => 0 < n <= Total,
            }
        }

        open spec fn op(self, other: Self) -> Self {
            match self {
                Fractional::Invalid => Fractional::Invalid,
                Fractional::Empty => other,
                Fractional::Value { v: sv, n: sn } => match other {
                    Fractional::Invalid => Fractional::Invalid,
                    Fractional::Empty => self,
                    Fractional::Value { v: ov, n: on } => {
                        if sv != ov {
                            Fractional::Invalid
                        } else if sn <= 0 || on <= 0 {
                            Fractional::Invalid
                        } else {
                            Fractional::Value { v: sv, n: sn+on }
                        }
                    },
                },
            }
        }

        open spec fn unit() -> Self {
            Fractional::Empty
        }

        proof fn closed_under_incl(a: Self, b: Self) {
        }

        proof fn commutative(a: Self, b: Self) {
        }

        proof fn associative(a: Self, b: Self, c: Self) {
        }

        proof fn op_unit(a: Self) {
        }

        proof fn unit_valid() {
        }
    }

    pub struct FractionalResource<T, const Total: u64> {
        r: Resource<Fractional<T, Total>>,
    }

    impl<T, const Total: u64> FractionalResource<T, Total> {
        pub closed spec fn inv(self) -> bool
        {
            self.r.value() is Value
        }

        pub closed spec fn id(self) -> Loc
        {
            self.r.loc()
        }

        pub closed spec fn view(self) -> (T, int)
        {
            (self.r.value()->v, self.r.value()->n)
        }

        pub proof fn alloc(v: T) -> (tracked result: FractionalResource<T, Total>)
            requires
                Total > 0,
            ensures
                result.inv(),
                result@ == (v, Total as int),
        {
            let f = Fractional::<T, Total>::new(v);
            let tracked r = Resource::alloc(f);
            FractionalResource { r }
        }

        pub proof fn agree(tracked self: &mut FractionalResource<T, Total>, tracked other: &FractionalResource<T, Total>)
            requires
                old(self).inv(),
                other.inv(),
                old(self).id() == other.id(),
            ensures
                self.id() == old(self).id(),
                self.inv(),
                self@ == old(self)@,
                self@.0 == other@.0,
        {
            self.r.validate_2(&other.r)
        }

        pub proof fn split(tracked self, n: int) ->
            (tracked result: (FractionalResource<T, Total>, FractionalResource<T, Total>))
            requires
                self.inv(),
                0 < n < self@.1
            ensures
                result.0.id() == result.1.id() == self.id(),
                result.0.inv(),
                result.1.inv(),
                result.0@.0 == self@.0,
                result.1@.0 == self@.0,
                result.0@.1 + result.1@.1 == self@.1,
                result.1@.1 == n,
        {
            let tracked (r1, r2) = self.r.split(Fractional::Value { v: self.r.value()->v,
                                                                    n: self.r.value()->n - n },
                                                Fractional::Value { v: self.r.value()->v,
                                                                    n: n });
            (FractionalResource { r: r1 }, FractionalResource { r: r2 })
        }

        pub proof fn combine(tracked self, tracked other: FractionalResource<T, Total>) -> (tracked result: FractionalResource<T, Total>)
            requires
                self.inv(),
                other.inv(),
                self.id() == other.id(),
            ensures
                result.id() == self.id(),
                result.inv(),
                result@.0 == self@.0,
                result@.0 == other@.0,
                result@.1 == self@.1 + other@.1,
        {
            let tracked mut mself = self;
            mself.r.validate_2(&other.r);
            let tracked r = mself.r.join(other.r);
            FractionalResource { r: r }
        }

        pub proof fn update(tracked self, v: T) -> (tracked result: FractionalResource<T, Total>)
            requires
                self.inv(),
                self@.1 == Total,
            ensures
                result.id() == self.id(),
                result.inv(),
                result@.0 == v,
                result@.1 == self@.1,
        {
            let f = Fractional::<T, Total>::Value { v: v, n: Total as int };
            let tracked r = self.r.update(f);
            FractionalResource { r: r }
        }
    }

    fn main()
    {
        let tracked r = FractionalResource::<u64, 3>::alloc(123);
        assert(r@.0 == 123);
        assert(r@.1 == 3);
        let tracked (r1, r2) = r.split(2);
        assert(r1@.0 == 123);
        assert(r2@.0 == 123);
        assert(r1@.1 == 1);
        assert(r2@.1 == 2);
        let tracked r3 = r1.combine(r2);
        let tracked r4 = r3.update(456);
        assert(r4@.0 == 456);
        assert(r4@.1 == 3);
        ()
    }
}
