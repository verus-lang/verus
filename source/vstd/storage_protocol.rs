use crate::prelude::*;
use crate::pcm::Loc;

verus!{

/// Interface for "storage protocol" ghost state.
/// This is an extension-slash-variant on the more well-known concept
/// of "PCM" ghost state, which we also have an interface for [here](crate::pcm::Resource).
/// The unique feature of a storage protocol is the ability to use [`guard`](StorageResource::guard)
/// to manipulate _shared_ references of ghost state.
///
/// Storage protocols are based on
/// [_Leaf: Modularity for Temporary Sharing in Separation Logic_](https://dl.acm.org/doi/10.1145/3622798).
///
/// The reference for the laws and operations we're embedding here can be found at:
/// <https://github.com/secure-foundations/leaf/blob/70c391162fa4c0198b0581ae274e68cc97204388/src/guarding/protocol.v#L31>
///
/// The reference version requires two monoids, the "protocol monoid" and the "base monoid".
/// In this interface, we fix the base monoid to be of the form [`Map<K, V>`](crate::map::Map).
/// (with composition of overlapping maps being undefined), which has all the necessary properties.
/// Note that there's no `create_unit` (it's not sound to do this for an arbitrary location unless you
/// already know a protocol was initialized at that location).

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(P)]
#[verifier::accept_recursive_types(V)]
pub tracked struct StorageResource<K, V, P> {
    p: core::marker::PhantomData<(K, V, P)>,
}

/// See [`StorageResource`] for more information.

pub trait Protocol<K, V> : Sized {
    spec fn op(self, other: Self) -> Self;

    /// Note that `inv`, in contrast to [`PCM::valid`](crate::pcm::PCM::valid), is not
    /// necessarily closed under inclusion.
    spec fn inv(self) -> bool;
    spec fn unit() -> Self;
    spec fn interp(self) -> Map<K, V>;

    proof fn commutative(a: Self, b: Self)
        ensures Self::op(a, b) == Self::op(b, a);

    proof fn associative(a: Self, b: Self, c: Self)
        ensures Self::op(a, Self::op(b, c))
            == Self::op(Self::op(a, b), c);

    proof fn op_unit(a: Self)
        ensures Self::op(a, Self::unit()) == a;

    // Don't need this - any Map<K, V> is always valid
    //proof fn inv_implies_valid(self)
    //    requires self.inv(),
    //    ensures self.interp().valid();
}

pub open spec fn incl<K, V, P: Protocol<K, V>>(a: P, b: P) -> bool {
    exists |c| P::op(a, c) == b
}

pub open spec fn conjunct_shared<K, V, P: Protocol<K, V>>(a: P, b: P, c: P) -> bool {
    forall |p: P| p.inv() && #[trigger] incl(a, p) && #[trigger] incl(b, p) ==> #[trigger] incl(c, p)
}

pub open spec fn guards<K, V, P: Protocol<K, V>>(p: P, b: Map<K, V>) -> bool {
    forall |q: P| #![all_triggers] P::op(p, q).inv() ==> b.submap_of(P::op(p, q).interp())
}

pub open spec fn exchanges<K, V, P: Protocol<K, V>>(p1: P, b1: Map<K, V>, p2: P, b2: Map<K, V>) -> bool {
    forall |q: P| #![all_triggers] P::op(p1, q).inv() ==> P::op(p2, q).inv()
        && P::op(p1, q).interp().dom().disjoint(b1.dom())
        && P::op(p2, q).interp().dom().disjoint(b2.dom())
        && P::op(p1, q).interp().union_prefer_right(b1)
            =~= P::op(p2, q).interp().union_prefer_right(b2)
}

pub open spec fn deposits<K, V, P: Protocol<K, V>>(p1: P, b1: Map<K, V>, p2: P) -> bool {
    forall |q: P| #![all_triggers] P::op(p1, q).inv() ==> P::op(p2, q).inv()
        && P::op(p1, q).interp().dom().disjoint(b1.dom())
        && P::op(p1, q).interp().union_prefer_right(b1)
            =~= P::op(p2, q).interp()
}

pub open spec fn withdraws<K, V, P: Protocol<K, V>>(p1: P, p2: P, b2: Map<K, V>) -> bool {
    forall |q: P| #![all_triggers] P::op(p1, q).inv() ==> P::op(p2, q).inv()
        && P::op(p2, q).interp().dom().disjoint(b2.dom())
        && P::op(p1, q).interp()
            =~= P::op(p2, q).interp().union_prefer_right(b2)
}

pub open spec fn updates<K, V, P: Protocol<K, V>>(p1: P, p2: P) -> bool {
    forall |q: P| #![all_triggers]  P::op(p1, q).inv() ==> P::op(p2, q).inv()
        && P::op(p1, q).interp() =~= P::op(p2, q).interp()
}

impl<K, V, P: Protocol<K, V>> StorageResource<K, V, P> {
    pub open spec fn value(self) -> P;
    pub open spec fn loc(self) -> Loc;

    #[verifier::external_body]
    pub proof fn alloc(value: P) -> (tracked out: Self)
        requires value.inv(),
        ensures
            out.value() == value,
    { unimplemented!(); }

    #[verifier::external_body]
    pub proof fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires self.loc() == other.loc(),
        ensures out.loc() == self.loc(),
            out.value() == P::op(self.value(), other.value()),
    { unimplemented!(); }

    #[verifier::external_body]
    pub proof fn split(tracked self, left: P, right: P) -> (tracked out: (Self, Self))
        requires self.value() == P::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == left,
            out.1.value() == right,
    { unimplemented!(); }

    /// Since `inv` isn't closed under inclusion, validity for an element
    /// is defined as the inclusion-closure of invariant, i.e., an element
    /// is valid if there exists another element `x` that, added to it,
    /// meets the invariant.
    #[verifier::external_body]
    pub proof fn is_valid(tracked &self) -> (x: P)
        ensures P::op(self.value(), x).inv(),
    { unimplemented!(); }

    // Updates and guards

    /// Most general kind of update, potentially depositing and withdrawing
    #[verifier::external_body]
    pub proof fn exchange(tracked self, tracked base: Map<K, V>, new_value: P, new_base: Map<K, V>) -> (tracked out: (Self, Map<K,V>))
        requires exchanges(self.value(), base, new_value, new_base)
        ensures
            out.0.loc() == self.loc(),
            out.0.value() == new_value,
            out.1 == new_base,
    { unimplemented!(); }

    #[verifier::external_body]
    pub proof fn deposit(tracked self, tracked base: Map<K, V>, new_value: P) -> (tracked out: Self)
        requires deposits(self.value(), base, new_value)
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        self.exchange(base, new_value, Map::empty()).0
    }

    #[verifier::external_body]
    pub proof fn withdraw(tracked self, new_value: P, new_base: Map<K, V>) -> (tracked out: (Self, Map<K,V>))
        requires withdraws(self.value(), new_value, new_base)
        ensures
            out.0.loc() == self.loc(),
            out.0.value() == new_value,
            out.1 == new_base,
    {
        self.exchange(Map::tracked_empty(), new_value, new_base)
    }

    /// "Normal" update, no depositing or withdrawing
    #[verifier::external_body]
    pub proof fn update(tracked self, new_value: P) -> (tracked out: Self)
        requires updates(self.value(), new_value)
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        self.exchange(Map::tracked_empty(), new_value, Map::empty()).0
    }

    #[verifier::external_body]
    pub proof fn guard(tracked &self, b: Map<K, V>) -> (tracked out: &Map<K,V>)
        requires guards(self.value(), b),
        ensures out == b,
    { unimplemented!(); }

    // Operations with shared references

    #[verifier::external_body]
    pub proof fn join_shared<'a>(tracked &'a self, tracked other: &'a Self, target: P) -> (tracked out: &'a Self)
        requires
            self.loc() == other.loc(),
            conjunct_shared(self.value(), other.value(), target),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    { unimplemented!(); }

    #[verifier::external_body]
    pub proof fn weaken<'a>(tracked &'a self, target: P) -> (tracked out: &'a Self)
        requires
            incl(target, self.value()),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    { unimplemented!(); }

    #[verifier::external_body]
    pub proof fn is_valid_2(tracked &mut self, tracked other: &Self) -> (x: P)
        requires
            old(self).loc() == other.loc(),
        ensures
            *self == *old(self),
            P::op(P::op(self.value(), other.value()), x).inv()
    { unimplemented!(); }

    // See `logic_exchange_with_extra_guard`
    // https://github.com/secure-foundations/leaf/blob/70c391162fa4c0198b0581ae274e68cc97204388/src/guarding/protocol.v#L503

    #[verifier::external_body]
    pub proof fn exchange_with_shared(tracked self, tracked other: &Self, tracked base: Map<K, V>, new_value: P, new_base: Map<K, V>) -> (tracked out: (Self, Map<K,V>))
        requires
            self.loc() == other.loc(),
            exchanges(P::op(self.value(), other.value()), base, P::op(new_value, other.value()), new_base)
        ensures
            out.0.loc() == self.loc(),
            out.0.value() == new_value,
            out.1 == new_base,
    { unimplemented!(); }
}

}
