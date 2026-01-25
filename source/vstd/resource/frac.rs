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
///     assert(a.frac() == 2);
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

/// See [`GhostVarAuth<T>`] for more information.
pub struct GhostVar<T> {
    frac: FracGhost<T>,
}

impl<T> GhostVar<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.frac.frac() == 1 as real
    }

    pub closed spec fn id(self) -> Loc {
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
        self.frac.frac() == 1 as real
    }

    pub closed spec fn id(self) -> Loc {
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
        let tracked v = GhostVar::<T> { frac: f.split() };
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
        let tracked mut nv = GhostVar::<T> { frac: msfrac.split() };
        let tracked mut ns = Self { frac: msfrac };
        tracked_swap(self, &mut ns);
        tracked_swap(v, &mut nv);
    }
}

/////// Fractional tokens that allow borrowing of resources
enum FractionalCarrierOpt<T> {
    Value { v: Option<T>, frac: real },
    Empty,
    Invalid,
}

impl<T> Protocol<(), T> for FractionalCarrierOpt<T> {
    closed spec fn op(self, other: Self) -> Self {
        match self {
            FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
            FractionalCarrierOpt::Empty => other,
            FractionalCarrierOpt::Value { v: sv, frac: s_frac } => match other {
                FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
                FractionalCarrierOpt::Empty => self,
                FractionalCarrierOpt::Value { v: ov, frac: o_frac } => {
                    if sv != ov {
                        FractionalCarrierOpt::Invalid
                    } else if s_frac <= 0 as real || o_frac <= 0 as real || s_frac + o_frac
                        > 1 as real {
                        FractionalCarrierOpt::Invalid
                    } else {
                        FractionalCarrierOpt::Value { v: sv, frac: s_frac + o_frac }
                    }
                },
            },
        }
    }

    closed spec fn rel(self, s: Map<(), T>) -> bool {
        match self {
            FractionalCarrierOpt::Value { v, frac } => {
                (match v {
                    Some(v0) => s.dom().contains(()) && s[()] == v0,
                    None => s =~= map![],
                }) && frac == 1 as real
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
pub struct Frac<T> {
    r: StorageResource<(), T, FractionalCarrierOpt<T>>,
}

/// Token that represents the "empty" state of a fractional resource system.
/// See [`Frac`] for more information.
pub struct Empty<T> {
    r: StorageResource<(), T, FractionalCarrierOpt<T>>,
}

impl<T> Frac<T> {
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

    pub closed spec fn frac(self) -> real {
        self.r.value()->frac
    }

    pub open spec fn valid(self, id: Loc, frac: real) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    /// Create a fractional token that maintains shared access to the input resource.
    pub proof fn new(tracked v: T) -> (tracked result: Self)
        ensures
            result.frac() == 1 as real,
            result.resource() == v,
    {
        let f = FractionalCarrierOpt::<T>::Value { v: Some(v), frac: 1 as real };
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

    // This helper is needed to bypass the type invariant temporarily
    proof fn split_to_helper(
        tracked r: &mut StorageResource<(), T, FractionalCarrierOpt<T>>,
        frac: real,
    ) -> (tracked result: Self)
        requires
            (0 as real) < frac < old(r).value()->frac,
            old(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
        ensures
            r.loc() == old(r).loc(),
            result.id() == old(r).loc(),
            r.value()->v.unwrap() == old(r).value()->v.unwrap(),
            result.resource() == old(r).value()->v.unwrap(),
            r.value()->frac + result.frac() == old(r).value()->frac,
            result.frac() == frac,
            r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        r.validate();
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, frac: 1 as real },
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        let tracked (r1, r2) = r1.split(
            FractionalCarrierOpt::Value { v: r1.value()->v, frac: r1.value()->frac - frac },
            FractionalCarrierOpt::Value { v: r1.value()->v, frac: frac },
        );
        *r = r1;
        Self { r: r2 }
    }

    /// Split one resource into two resources whose quantities sum to the original.
    /// The returned token has quantity `result_frac`; the new value of the input token has
    /// quantity `old(self).frac() - result_frac`.
    pub proof fn split_to(tracked &mut self, result_frac: real) -> (tracked result: Self)
        requires
            0 as real < result_frac < old(self).frac(),
        ensures
            self.id() == old(self).id(),
            result.id() == old(self).id(),
            self.resource() == old(self).resource(),
            result.resource() == old(self).resource(),
            self.frac() == old(self).frac() - result_frac,
            result.frac() == result_frac,
    {
        use_type_invariant(&*self);
        Self::split_to_helper(&mut self.r, result_frac)
    }

    /// Split one resource by half into two resources whose quantities sum to the original.
    /// The returned token has quantity `n`; the new value of the input token has
    /// quantity `old(self).frac() - n`.
    pub proof fn split(tracked &mut self) -> (tracked result: Self)
        ensures
            self.id() == old(self).id(),
            result.id() == old(self).id(),
            self.resource() == old(self).resource(),
            result.resource() == old(self).resource(),
            self.frac() == old(self).frac() / 2 as real,
            result.frac() == old(self).frac() / 2 as real,
    {
        use_type_invariant(&*self);
        self.r.validate();
        self.split_to(self.frac() / 2 as real)
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
        Self::combine_helper(&mut self.r, other);
    }

    // This helper is needed to temporarily bypass the type invariant
    proof fn combine_helper(
        tracked r: &mut StorageResource<(), T, FractionalCarrierOpt<T>>,
        tracked other: Self,
    )
        requires
            old(r).loc() == other.id(),
            old(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
        ensures
            r.loc() == old(r).loc(),
            r.value()->v.unwrap() == old(r).value()->v.unwrap(),
            r.value()->v.unwrap() == other.resource(),
            r.value()->frac == old(r).value()->frac + other.frac(),
            r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        use_type_invariant(&other);
        r.validate();
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, frac: 1 as real },
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        r1.validate_with_shared(&other.r);
        *r = StorageResource::join(r1, other.r);
    }

    /// Allowed values for a token's quantity.
    pub proof fn bounded(tracked &self)
        ensures
            0 as real < self.frac() <= 1 as real,
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
    pub proof fn take_resource(tracked self) -> (tracked pair: (T, Empty<T>))
        requires
            self.frac() == 1 as real,
        ensures
            pair.0 == self.resource(),
            pair.1.id() == self.id(),
    {
        use_type_invariant(&self);
        self.r.validate();

        let p1 = self.r.value();
        let p2 = FractionalCarrierOpt::Value { v: None, frac: 1 as real };
        let b2 = map![() => self.resource()];
        assert forall|q: FractionalCarrierOpt<T>, t1: Map<(), T>|
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

impl<T> Empty<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() matches FractionalCarrierOpt::Value { v: None, frac }
        &&& frac == 1 as real
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub proof fn new(tracked v: T) -> (tracked result: Self) {
        let f = FractionalCarrierOpt::<T>::Value { v: None, frac: 1 as real };
        let tracked mut m = Map::<(), T>::tracked_empty();
        let tracked r = StorageResource::alloc(f, m);
        Self { r }
    }

    /// Give up ownership of a resource and obtain a [`Frac`] token.
    pub proof fn put_resource(tracked self, tracked resource: T) -> (tracked frac: Frac<T>)
        ensures
            frac.id() == self.id(),
            frac.resource() == resource,
            frac.frac() == 1 as real,
    {
        use_type_invariant(&self);
        self.r.validate();

        let p1 = self.r.value();
        let b1 = map![() => resource];
        let p2 = FractionalCarrierOpt::Value { v: Some(resource), frac: 1 as real };

        assert forall|q: FractionalCarrierOpt<T>, t1: Map<(), T>|
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
