use super::super::modes::*;
use super::super::prelude::*;
use super::Loc;
use super::storage_protocol::*;

verus! {

broadcast use {super::super::map::group_map_axioms, super::super::set::group_set_axioms};

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
                    } else if s_frac <= (0 as real) || o_frac <= (0 as real) || s_frac + o_frac > (
                    1 as real) {
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
        let f = FractionalCarrierOpt::<T>::Value { v: Some(v), frac: (1 as real) };
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
            FractionalCarrierOpt::Value { v: None, frac: (1 as real) },
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
            (0 as real) < result_frac < old(self).frac(),
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
            FractionalCarrierOpt::Value { v: None, frac: (1 as real) },
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        r1.validate_with_shared(&other.r);
        *r = StorageResource::join(r1, other.r);
    }

    /// Allowed values for a token's quantity.
    pub proof fn bounded(tracked &self)
        ensures
            (0 as real) < self.frac() <= (1 as real),
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
        let p2 = FractionalCarrierOpt::Value { v: None, frac: (1 as real) };
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
        let f = FractionalCarrierOpt::<T>::Value { v: None, frac: (1 as real) };
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
        let p2 = FractionalCarrierOpt::Value { v: Some(resource), frac: (1 as real) };

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
