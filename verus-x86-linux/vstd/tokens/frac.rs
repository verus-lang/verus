use super::super::modes::*;
use super::super::pcm::*;
use super::super::prelude::*;
use super::super::storage_protocol::*;
use super::*;

verus! {

broadcast use {super::super::map::group_map_axioms, super::super::set::group_set_axioms};
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

/////// Fractional tokens that allow borrowing of resources
enum FractionalCarrierOpt<T, const TOTAL: u64> {
    Value { v: Option<T>, n: int },
    Empty,
    Invalid,
}

impl<T, const TOTAL: u64> Protocol<(), T> for FractionalCarrierOpt<T, TOTAL> {
    closed spec fn op(self, other: Self) -> Self {
        match self {
            FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
            FractionalCarrierOpt::Empty => other,
            FractionalCarrierOpt::Value { v: sv, n: sn } => match other {
                FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
                FractionalCarrierOpt::Empty => self,
                FractionalCarrierOpt::Value { v: ov, n: on } => {
                    if sv != ov {
                        FractionalCarrierOpt::Invalid
                    } else if sn <= 0 || on <= 0 {
                        FractionalCarrierOpt::Invalid
                    } else {
                        FractionalCarrierOpt::Value { v: sv, n: sn + on }
                    }
                },
            },
        }
    }

    closed spec fn rel(self, s: Map<(), T>) -> bool {
        match self {
            FractionalCarrierOpt::Value { v, n } => {
                (match v {
                    Some(v0) => s.dom().contains(()) && s[()] == v0,
                    None => s =~= map![],
                }) && n == TOTAL && n != 0
            },
            FractionalCarrierOpt::Empty => false,
            FractionalCarrierOpt::Invalid => false,
        }
    }

    closed spec fn unit() -> Self {
        FractionalCarrierOpt::Empty
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

/// Token that maintains fractional access to some resource.
/// This allows multiple clients to obtain shared references to some resource
/// via `borrow`.
pub struct Frac<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

/// Token that represents the "empty" state of a fractional resource system.
/// See [`Frac`] for more information.
pub struct Empty<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

impl<T, const TOTAL: u64> Frac<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. }
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn resource(self) -> T {
        self.r.value()->v.unwrap()
    }

    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    /// Create a fractional token that maintains shared access to the input resource.
    pub proof fn new(tracked v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL as int,
            result.resource() == v,
    {
        let f = FractionalCarrierOpt::<T, TOTAL>::Value { v: Some(v), n: TOTAL as int };
        let tracked mut m = Map::<(), T>::tracked_empty();
        m.tracked_insert((), v);
        let tracked r = StorageResource::alloc(f, m);
        Self { r }
    }

    /// Two tokens agree on values of the underlying resource.
    pub proof fn agree(tracked self: &Self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self.resource() == other.resource(),
    {
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked joined = self.r.join_shared(&other.r);
        joined.validate();
    }

    /// Split one token into two tokens whose quantities sum to the original.
    /// The returned token has quantity `n`; the new value of the input token has
    /// quantity `old(self).frac() - n`.
    pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            result.id() == self.id() == old(self).id(),
            self.resource() == old(self).resource(),
            result.resource() == old(self).resource(),
            self.frac() + result.frac() == old(self).frac(),
            result.frac() == n,
    {
        use_type_invariant(&*self);
        Self::split_helper(&mut self.r, n)
    }

    proof fn split_helper(
        tracked r: &mut StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
        n: int,
    ) -> (tracked result: Self)
        requires
            0 < n < old(r).value()->n,
            old(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
        ensures
            result.id() == r.loc() == old(r).loc(),
            r.value()->v.unwrap() == old(r).value()->v.unwrap(),
            result.resource() == old(r).value()->v.unwrap(),
            r.value()->n + result.frac() == old(r).value()->n,
            result.frac() == n,
            r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        r.validate();
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, n: TOTAL as int },
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        let tracked (r1, r2) = r1.split(
            FractionalCarrierOpt::Value { v: r1.value()->v, n: r1.value()->n - n },
            FractionalCarrierOpt::Value { v: r1.value()->v, n: n },
        );
        *r = r1;
        Self { r: r2 }
    }

    /// Combine two tokens, summing their quantities.
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self.resource() == old(self).resource(),
            self.resource() == other.resource(),
            self.frac() == old(self).frac() + other.frac(),
    {
        use_type_invariant(&*self);
        Self::combine_helper(&mut self.r, other)
    }

    proof fn combine_helper(
        tracked r: &mut StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
        tracked other: Self,
    )
        requires
            old(r).loc() == other.id(),
            old(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
        ensures
            r.loc() == old(r).loc(),
            r.value()->v.unwrap() == old(r).value()->v.unwrap(),
            r.value()->v.unwrap() == other.resource(),
            r.value()->n == old(r).value()->n + other.frac(),
            r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        r.validate();
        use_type_invariant(&other);
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, n: TOTAL as int },
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        r1.validate_with_shared(&other.r);
        *r = StorageResource::join(r1, other.r);
    }

    /// Allowed values for a token's quantity.
    pub proof fn bounded(tracked &self)
        ensures
            0 < self.frac() <= TOTAL,
    {
        use_type_invariant(self);
        let (x, _) = self.r.validate();
    }

    /// Obtain shared access to the underlying resource.
    pub proof fn borrow(tracked &self) -> (tracked ret: &T)
        ensures
            ret == self.resource(),
    {
        use_type_invariant(self);
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(())
    }

    /// Reclaim full ownership of the underlying resource.
    pub proof fn take_resource(tracked self) -> (tracked pair: (T, Empty<T, TOTAL>))
        requires
            self.frac() == TOTAL,
        ensures
            pair.0 == self.resource(),
            pair.1.id() == self.id(),
    {
        use_type_invariant(&self);
        self.r.validate();

        let p1 = self.r.value();
        let p2 = FractionalCarrierOpt::Value { v: None, n: TOTAL as int };
        let b2 = map![() => self.resource()];
        assert forall|q: FractionalCarrierOpt<T, TOTAL>, t1: Map<(), T>|
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p1, q), t1) implies exists|
            t2: Map<(), T>,
        |
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2) && t2.dom().disjoint(
                b2.dom(),
            ) && t1 =~= t2.union_prefer_right(b2) by {
            let t2 = map![];
            assert(FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2));
            assert(t2.dom().disjoint(b2.dom()));
            assert(t1 =~= t2.union_prefer_right(b2));
        }

        let tracked Self { r } = self;
        let tracked (new_r, mut m) = r.withdraw(p2, b2);
        let tracked emp = Empty { r: new_r };
        let tracked resource = m.tracked_remove(());
        (resource, emp)
    }
}

impl<T, const TOTAL: u64> Empty<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() matches FractionalCarrierOpt::Value { v: None, n }
        &&& n == TOTAL
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub proof fn new(tracked v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
    {
        let f = FractionalCarrierOpt::<T, TOTAL>::Value { v: None, n: TOTAL as int };
        let tracked mut m = Map::<(), T>::tracked_empty();
        let tracked r = StorageResource::alloc(f, m);
        Self { r }
    }

    /// Give up ownership of a resource and obtain a [`Frac`] token.
    pub proof fn put_resource(tracked self, tracked resource: T) -> (tracked frac: Frac<T, TOTAL>)
        ensures
            frac.id() == self.id(),
            frac.resource() == resource,
            frac.frac() == TOTAL,
    {
        use_type_invariant(&self);
        self.r.validate();

        let p1 = self.r.value();
        let b1 = map![() => resource];
        let p2 = FractionalCarrierOpt::Value { v: Some(resource), n: TOTAL as int };

        assert forall|q: FractionalCarrierOpt<T, TOTAL>, t1: Map<(), T>|
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p1, q), t1) implies exists|
            t2: Map<(), T>,
        |
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2) && t1.dom().disjoint(
                b1.dom(),
            ) && t1.union_prefer_right(b1) =~= t2 by {
            let t2 = map![() => resource];
            assert(FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2)
                && t1.dom().disjoint(b1.dom()) && t1.union_prefer_right(b1) =~= t2);
        }

        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), resource);
        let tracked Self { r } = self;
        let tracked new_r = r.deposit(m, p2);
        let tracked f = Frac { r: new_r };
        f
    }
}

} // verus!
