use super::super::modes::*;
use super::super::prelude::*;
use super::*;

verus! {

// Too bad that `nat` and `int` are forbidden as the type of a const generic parameter
enum FractionalCarrier<T, const TOTAL: u64> {
    Value { v: T, n: int },
    Empty,
    Invalid,
}

impl<T, const TOTAL: u64> FractionalCarrier<T, TOTAL> {
    spec fn new(v: T) -> Self {
        FractionalCarrier::Value { v: v, n: TOTAL as int }
    }
}

impl<T, const TOTAL: u64> PCM for FractionalCarrier<T, TOTAL> {
    closed spec fn valid(self) -> bool {
        match self {
            FractionalCarrier::Invalid => false,
            FractionalCarrier::Empty => true,
            FractionalCarrier::Value { v: v, n: n } => 0 < n <= TOTAL,
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        match self {
            FractionalCarrier::Invalid => FractionalCarrier::Invalid,
            FractionalCarrier::Empty => other,
            FractionalCarrier::Value { v: sv, n: sn } => match other {
                FractionalCarrier::Invalid => FractionalCarrier::Invalid,
                FractionalCarrier::Empty => self,
                FractionalCarrier::Value { v: ov, n: on } => {
                    if sv != ov {
                        FractionalCarrier::Invalid
                    } else if sn <= 0 || on <= 0 {
                        FractionalCarrier::Invalid
                    } else {
                        FractionalCarrier::Value { v: sv, n: sn + on }
                    }
                },
            },
        }
    }

    closed spec fn unit() -> Self {
        FractionalCarrier::Empty
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

/** An implementation of a resource for fractional ownership of a ghost variable.

While most presentations of fractional permissions use the fractional total of 1,
with fractions being arbitrary rational numbers, this library represents fractional
permissions as integers, totalling to some compile-time constant `TOTAL`.
Thus, you can have any fractions from 1 up to `TOTAL`, and if you
have `TOTAL`, you can update the ghost variable.

If you just want to split the permission in half, you can also use the
[`GhostVar<T>`] and [`GhostVarAuth<T>`] library.

### Example

```
fn example_use() {
    let tracked mut r = FracGhost::<u64, 3>::new(123);
    assert(r@ == 123);
    assert(r.frac() == 3);
    let tracked r2 = r.split(2);
    assert(r@ == 123);
    assert(r2@ == 123);
    assert(r.frac() == 1);
    assert(r2.frac() == 2);
    proof {
        r.combine(r2);
        r.update(456);
    }
    assert(r@ == 456);
    assert(r.frac() == 3);

    let tracked mut a = FracGhost::<u32>::new(5);
    assert(a@ == 5);
    assert(a.frac() == 2);
    let tracked mut b = a.split(1);
    assert(a.frac() == 1);
    assert(b.frac() == 1);
    proof {
        a.update_with(&mut b, 123);
    }
    assert(a@ == 123);

    proof {
        a.combine(b);
        a.update(6);
    }
    assert(a@ == 6);
}
```
*/

pub struct FracGhost<T, const TOTAL: u64 = 2> {
    r: Resource<FractionalCarrier<T, TOTAL>>,
}

impl<T, const TOTAL: u64> FracGhost<T, TOTAL> {
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

    /// The fractional quantity of this permission. The "fraction" is represented as an integer,
    /// out of `TOTAL`.
    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    /// Allocate a new token with the given value. The returned token represents
    /// the `TOTAL` quantity.
    pub proof fn new(v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL as int,
            result@ == v,
    {
        let f = FractionalCarrier::<T, TOTAL>::new(v);
        let tracked r = Resource::alloc(f);
        Self { r }
    }

    /// Two tokens agree on their values.
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

    /// Split one token into two tokens whose quantities sum to the original.
    /// The returned token has quantity `n`; the new value of the input token has
    /// quantity `old(self).frac() - n`.
    pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            result.id() == self.id() == old(self).id(),
            self@ == old(self)@,
            result@ == old(self)@,
            self.frac() + result.frac() == old(self).frac(),
            result.frac() == n,
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        let tracked (r1, r2) = mself.r.split(
            FractionalCarrier::Value { v: mself.r.value()->v, n: mself.r.value()->n - n },
            FractionalCarrier::Value { v: mself.r.value()->v, n: n },
        );
        self.r = r1;
        Self { r: r2 }
    }

    /// Combine two tokens, summing their quantities.
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

    /// Update the value of the token. This requires having ALL the permissions,
    /// i.e., a quantity total of `TOTAL`.
    pub proof fn update(tracked &mut self, v: T)
        requires
            old(self).frac() == TOTAL,
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
        let f = FractionalCarrier::<T, TOTAL>::Value { v: v, n: TOTAL as int };
        *self = Self { r: r.update(f) };
    }

    /// Update the value of the token. This requires having ALL the permissions,
    /// i.e., the tokens together must have a quantity total of `TOTAL`.
    pub proof fn update_with(tracked &mut self, tracked other: &mut Self, v: T)
        requires
            old(self).id() == old(other).id(),
            old(self).frac() + old(other).frac() == TOTAL,
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

        let tracked mut xother = self.split(other_frac);
        tracked_swap(other, &mut xother);
    }

    /// Allowed values for a token's quantity.
    pub proof fn bounded(tracked &self)
        ensures
            0 < self.frac() <= TOTAL,
    {
        use_type_invariant(self);
        self.r.validate()
    }

    /// Obtain an arbitrary token with no information about it.
    /// Useful if you need a well-typed placeholder.
    pub proof fn dummy() -> (tracked result: Self)
        requires
            TOTAL > 0,
    {
        Self::new(arbitrary())
    }
}

/// See [`GhostVarAuth<T>`] for more information.
pub struct GhostVar<T> {
    frac: FracGhost<T>,
}

impl<T> GhostVar<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.frac.frac() == 1
    }

    pub closed spec fn id(self) -> int {
        self.frac.id()
    }

    pub closed spec fn view(self) -> T {
        self.frac.view()
    }
}

/** `GhostVarAuth<T>` is one half of a pair of tokens—the other being [`GhostVar<T>`].
These tokens each track a value, and they can only be allocated or updated together.
Thus, the pair of tokens always agree on the value, but they can be owned separately.

One possible application is to have a library which
keeps `GhostVarAuth<T>` and maintains an invariant relating the implementation's
abstract state to the value of `GhostVarAuth<T>`.  Both `GhostVarAuth<T>`
and [`GhostVar<T>`] are needed together to update the value, but either one alone
allows reasoning about the current state.

These tokens can be implemented using fractional permissions, e.g., [`FracGhost`].

### Example

```
fn example() {
    let tracked (mut gauth, mut gvar) = GhostVarAuth::<u64>::new(1);
    assert(gauth@ == 1);
    assert(gvar@ == 1);
    proof {
        gauth.update(&mut gvar, 2);
    }
    assert(gauth@ == 2);
    assert(gvar@ == 2);
}
```
*/

pub struct GhostVarAuth<T> {
    frac: FracGhost<T>,
}

impl<T> GhostVarAuth<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.frac.frac() == 1
    }

    pub closed spec fn id(self) -> int {
        self.frac.id()
    }

    pub closed spec fn view(self) -> T {
        self.frac.view()
    }

    /// Allocate a new pair of tokens, each initialized to the given value.
    pub proof fn new(v: T) -> (tracked result: (GhostVarAuth<T>, GhostVar<T>))
        ensures
            result.0.id() == result.1.id(),
            result.0@ == v,
            result.1@ == v,
    {
        let tracked mut f = FracGhost::<T>::new(v);
        let tracked v = GhostVar::<T> { frac: f.split(1) };
        let tracked a = GhostVarAuth::<T> { frac: f };
        (a, v)
    }

    /// Ensure that both tokens agree on the value.
    pub proof fn agree(tracked &self, tracked v: &GhostVar<T>)
        requires
            self.id() == v.id(),
        ensures
            self@ == v@,
    {
        self.frac.agree(&v.frac)
    }

    /// Update the value on each token.
    pub proof fn update(tracked &mut self, tracked v: &mut GhostVar<T>, new_val: T)
        requires
            old(self).id() == old(v).id(),
        ensures
            self.id() == old(self).id(),
            v.id() == old(v).id(),
            old(self)@ == old(v)@,
            self@ == new_val,
            v@ == new_val,
    {
        let tracked (mut ms, mut mv) = Self::new(new_val);
        tracked_swap(self, &mut ms);
        tracked_swap(v, &mut mv);
        use_type_invariant(&ms);
        use_type_invariant(&mv);
        let tracked mut msfrac = ms.frac;
        msfrac.combine(mv.frac);
        msfrac.update(new_val);
        let tracked mut nv = GhostVar::<T> { frac: msfrac.split(1) };
        let tracked mut ns = Self { frac: msfrac };
        tracked_swap(self, &mut ns);
        tracked_swap(v, &mut nv);
    }
}

} // verus!
