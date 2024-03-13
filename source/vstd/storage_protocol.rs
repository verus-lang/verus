use crate::pcm::Loc;
use crate::prelude::*;

verus! {

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
/// <https://github.com/secure-foundations/leaf/blob/a51725deedecc88294057ac1502a7c7ff2104a69/src/guarding/protocol.v#L31>
///
/// The reference version requires two monoids, the "protocol monoid" and the "base monoid".
/// In this interface, we fix the base monoid to be of the form [`Map<K, V>`](crate::map::Map).
/// (with composition of overlapping maps being undefined), which has all the necessary properties.
/// Note that there's no `create_unit` (it's not sound to do this for an arbitrary location unless you
/// already know a protocol was initialized at that location).
///
/// For applications, I generally advise using the
/// [`tokenized_state_machine!` system](https://verus-lang.github.io/verus/state_machines/),
/// rather than using this interface directly.
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(P)]
#[verifier::accept_recursive_types(V)]
pub tracked struct StorageResource<K, V, P> {
    _p: core::marker::PhantomData<(K, V, P)>,
    _send_sync: crate::state_machine_internal::SyncSendIfSyncSend<Map<K, V>>,
}

/// See [`StorageResource`] for more information.
pub trait Protocol<K, V>: Sized {
    spec fn op(self, other: Self) -> Self;

    /// Note that `inv`, in contrast to [`PCM::valid`](crate::pcm::PCM::valid), is not
    /// necessarily closed under inclusion.
    spec fn inv(self) -> bool;

    spec fn unit() -> Self;

    spec fn interp(self) -> Map<K, V>;

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
    // Don't need this - any Map<K, V> is always valid
    //proof fn inv_implies_valid(self)
    //    requires self.inv(),
    //    ensures self.interp().valid();

}

pub open spec fn incl<K, V, P: Protocol<K, V>>(a: P, b: P) -> bool {
    exists|c| P::op(a, c) == b
}

pub open spec fn conjunct_shared<K, V, P: Protocol<K, V>>(a: P, b: P, c: P) -> bool {
    forall|p: P| p.inv() && #[trigger] incl(a, p) && #[trigger] incl(b, p) ==> #[trigger] incl(c, p)
}

pub open spec fn guards<K, V, P: Protocol<K, V>>(p: P, b: Map<K, V>) -> bool {
    forall|q: P| #![all_triggers] P::op(p, q).inv() ==> b.submap_of(P::op(p, q).interp())
}

pub open spec fn exchanges<K, V, P: Protocol<K, V>>(
    p1: P,
    b1: Map<K, V>,
    p2: P,
    b2: Map<K, V>,
) -> bool {
    forall|q: P|
        #![all_triggers]
        P::op(p1, q).inv() ==> P::op(p2, q).inv() && P::op(p1, q).interp().dom().disjoint(b1.dom())
            && P::op(p2, q).interp().dom().disjoint(b2.dom()) && P::op(
            p1,
            q,
        ).interp().union_prefer_right(b1) =~= P::op(p2, q).interp().union_prefer_right(b2)
}

pub open spec fn exchanges_nondeterministic<K, V, P: Protocol<K, V>>(
    p1: P,
    b1: Map<K, V>,
    new_values: Set<(P, Map<K, V>)>,
) -> bool {
    forall|q: P|
        #![all_triggers]
        P::op(p1, q).inv() ==> exists|p2, b2|
            #![all_triggers]
            new_values.contains((p2, b2)) && P::op(p2, q).inv() && P::op(
                p1,
                q,
            ).interp().dom().disjoint(b1.dom()) && P::op(p2, q).interp().dom().disjoint(b2.dom())
                && P::op(p1, q).interp().union_prefer_right(b1) =~= P::op(
                p2,
                q,
            ).interp().union_prefer_right(b2)
}

pub open spec fn deposits<K, V, P: Protocol<K, V>>(p1: P, b1: Map<K, V>, p2: P) -> bool {
    forall|q: P|
        #![all_triggers]
        P::op(p1, q).inv() ==> P::op(p2, q).inv() && P::op(p1, q).interp().dom().disjoint(b1.dom())
            && P::op(p1, q).interp().union_prefer_right(b1) =~= P::op(p2, q).interp()
}

pub open spec fn withdraws<K, V, P: Protocol<K, V>>(p1: P, p2: P, b2: Map<K, V>) -> bool {
    forall|q: P|
        #![all_triggers]
        P::op(p1, q).inv() ==> P::op(p2, q).inv() && P::op(p2, q).interp().dom().disjoint(b2.dom())
            && P::op(p1, q).interp() =~= P::op(p2, q).interp().union_prefer_right(b2)
}

pub open spec fn updates<K, V, P: Protocol<K, V>>(p1: P, p2: P) -> bool {
    forall|q: P|
        #![all_triggers]
        P::op(p1, q).inv() ==> P::op(p2, q).inv() && P::op(p1, q).interp() =~= P::op(p2, q).interp()
}

pub open spec fn set_op<K, V, P: Protocol<K, V>>(s: Set<(P, Map<K, V>)>, t: P) -> Set<
    (P, Map<K, V>),
> {
    Set::new(|v: (P, Map<K, V>)| exists|q| s.contains((q, v.1)) && v.0 == #[trigger] P::op(q, t))
}

impl<K, V, P: Protocol<K, V>> StorageResource<K, V, P> {
    pub open spec fn value(self) -> P;

    pub open spec fn loc(self) -> Loc;

    #[verifier::external_body]
    pub proof fn alloc(value: P) -> (tracked out: Self)
        requires
            value.inv(),
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

    /// Since `inv` isn't closed under inclusion, validity for an element
    /// is defined as the inclusion-closure of invariant, i.e., an element
    /// is valid if there exists another element `x` that, added to it,
    /// meets the invariant.
    #[verifier::external_body]
    pub proof fn is_valid(tracked &self) -> (x: P)
        ensures
            P::op(self.value(), x).inv(),
    {
        unimplemented!();
    }

    // Updates and guards
    /// Most general kind of update, potentially depositing and withdrawing
    pub proof fn exchange(
        tracked self,
        tracked base: Map<K, V>,
        new_value: P,
        new_base: Map<K, V>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            exchanges(self.value(), base, new_value, new_base),
        ensures
            out.0.loc() == self.loc(),
            out.0.value() == new_value,
            out.1 == new_base,
    {
        let s = set![(new_value, new_base)];
        self.exchange_nondeterministic(base, s)
    }

    pub proof fn deposit(tracked self, tracked base: Map<K, V>, new_value: P) -> (tracked out: Self)
        requires
            deposits(self.value(), base, new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        self.exchange(base, new_value, Map::empty()).0
    }

    pub proof fn withdraw(tracked self, new_value: P, new_base: Map<K, V>) -> (tracked out: (
        Self,
        Map<K, V>,
    ))
        requires
            withdraws(self.value(), new_value, new_base),
        ensures
            out.0.loc() == self.loc(),
            out.0.value() == new_value,
            out.1 == new_base,
    {
        self.exchange(Map::tracked_empty(), new_value, new_base)
    }

    /// "Normal" update, no depositing or withdrawing
    pub proof fn update(tracked self, new_value: P) -> (tracked out: Self)
        requires
            updates(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        self.exchange(Map::tracked_empty(), new_value, Map::empty()).0
    }

    pub proof fn exchange_nondeterministic(
        tracked self,
        tracked base: Map<K, V>,
        new_values: Set<(P, Map<K, V>)>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            exchanges_nondeterministic(self.value(), base, new_values),
        ensures
            out.0.loc() == self.loc(),
            new_values.contains((out.0.value(), out.1)),
    {
        P::op_unit(self.value());
        let tracked (selff, unit) = self.split(self.value(), P::unit());
        let new_values0 = set_op(new_values, P::unit());
        crate::set_lib::assert_sets_equal!(new_values0, new_values, v => {
            P::op_unit(v.0);
            if new_values.contains(v) {
                assert(new_values0.contains(v));
            }
            if new_values0.contains(v) {
                let q = choose |q| new_values.contains((q, v.1)) && v.0 == #[trigger] P::op(q, P::unit());
                P::op_unit(q);
                assert(new_values.contains(v));
            }
        });
        selff.exchange_nondeterministic_with_shared(&unit, base, new_values)
    }

    #[verifier::external_body]
    pub proof fn guard(tracked &self, b: Map<K, V>) -> (tracked out: &Map<K, V>)
        requires
            guards(self.value(), b),
        ensures
            out == b,
    {
        unimplemented!();
    }

    // Operations with shared references
    #[verifier::external_body]
    pub proof fn join_shared<'a>(
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
        unimplemented!();
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
    pub proof fn is_valid_2(tracked &mut self, tracked other: &Self) -> (x: P)
        requires
            old(self).loc() == other.loc(),
        ensures
            *self == *old(self),
            P::op(P::op(self.value(), other.value()), x).inv(),
    {
        unimplemented!();
    }

    // See `logic_exchange_with_extra_guard`
    // https://github.com/secure-foundations/leaf/blob/a51725deedecc88294057ac1502a7c7ff2104a69/src/guarding/protocol.v#L720
    pub proof fn exchange_with_shared(
        tracked self,
        tracked other: &Self,
        tracked base: Map<K, V>,
        new_value: P,
        new_base: Map<K, V>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            self.loc() == other.loc(),
            exchanges(
                P::op(self.value(), other.value()),
                base,
                P::op(new_value, other.value()),
                new_base,
            ),
        ensures
            out.0.loc() == self.loc(),
            out.0.value() == new_value,
            out.1 == new_base,
    {
        let s = set![(new_value, new_base)];
        self.exchange_nondeterministic_with_shared(other, base, s)
    }

    // See `logic_exchange_with_extra_guard_nondeterministic`
    // https://github.com/secure-foundations/leaf/blob/a51725deedecc88294057ac1502a7c7ff2104a69/src/guarding/protocol.v#L834
    /// Most general kind of update, potentially depositing and withdrawing
    #[verifier::external_body]
    pub proof fn exchange_nondeterministic_with_shared(
        tracked self,
        tracked other: &Self,
        tracked base: Map<K, V>,
        new_values: Set<(P, Map<K, V>)>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            self.loc() == other.loc(),
            exchanges_nondeterministic(
                P::op(self.value(), other.value()),
                base,
                set_op(new_values, other.value()),
            ),
        ensures
            out.0.loc() == self.loc(),
            new_values.contains((out.0.value(), out.1)),
    {
        unimplemented!();
    }
}

} // verus!
