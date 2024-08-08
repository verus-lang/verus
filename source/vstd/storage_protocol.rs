use super::pcm::Loc;
use super::prelude::*;

verus! {

broadcast use super::set::group_set_axioms, super::map::group_map_axioms;
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
/// <https://github.com/secure-foundations/leaf/blob/9d72b880feb6af0a7e752b2b2a43806a0812ad56/src/guarding/protocol_relational.v>
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
    _send_sync: super::state_machine_internal::SyncSendIfSyncSend<Map<K, V>>,
}

/// See [`StorageResource`] for more information.
pub trait Protocol<K, V>: Sized {
    spec fn op(self, other: Self) -> Self;

    /// Note that `rel`, in contrast to [`PCM::valid`](crate::pcm::PCM::valid), is not
    /// necessarily closed under inclusion.
    spec fn rel(self, s: Map<K, V>) -> bool;

    spec fn unit() -> Self;

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
}

pub open spec fn incl<K, V, P: Protocol<K, V>>(a: P, b: P) -> bool {
    exists|c| P::op(a, c) == b
}

pub open spec fn guards<K, V, P: Protocol<K, V>>(p: P, b: Map<K, V>) -> bool {
    forall|q: P, t: Map<K, V>| #![all_triggers] P::rel(P::op(p, q), t) ==> b.submap_of(t)
}

pub open spec fn exchanges<K, V, P: Protocol<K, V>>(
    p1: P,
    b1: Map<K, V>,
    p2: P,
    b2: Map<K, V>,
) -> bool {
    forall|q: P, t1: Map<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> exists|t2: Map<K, V>|
            #![all_triggers]
            P::rel(P::op(p2, q), t2) && t1.dom().disjoint(b1.dom()) && t2.dom().disjoint(b2.dom())
                && t1.union_prefer_right(b1) =~= t2.union_prefer_right(b2)
}

pub open spec fn exchanges_nondeterministic<K, V, P: Protocol<K, V>>(
    p1: P,
    s1: Map<K, V>,
    new_values: Set<(P, Map<K, V>)>,
) -> bool {
    forall|q: P, t1: Map<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> exists|p2: P, s2: Map<K, V>, t2: Map<K, V>|
            #![all_triggers]
            new_values.contains((p2, s2)) && P::rel(P::op(p2, q), t2) && t1.dom().disjoint(s1.dom())
                && t2.dom().disjoint(s2.dom()) && t1.union_prefer_right(s1)
                =~= t2.union_prefer_right(s2)
}

pub open spec fn deposits<K, V, P: Protocol<K, V>>(p1: P, b1: Map<K, V>, p2: P) -> bool {
    forall|q: P, t1: Map<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> exists|t2: Map<K, V>|
            #![all_triggers]
            P::rel(P::op(p2, q), t2) && t1.dom().disjoint(b1.dom()) && t1.union_prefer_right(b1)
                =~= t2
}

pub open spec fn withdraws<K, V, P: Protocol<K, V>>(p1: P, p2: P, b2: Map<K, V>) -> bool {
    forall|q: P, t1: Map<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> exists|t2: Map<K, V>|
            #![all_triggers]
            P::rel(P::op(p2, q), t2) && t2.dom().disjoint(b2.dom()) && t1 =~= t2.union_prefer_right(
                b2,
            )
}

pub open spec fn updates<K, V, P: Protocol<K, V>>(p1: P, p2: P) -> bool {
    forall|q: P, t1: Map<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> P::rel(P::op(p2, q), t1)
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
    pub proof fn alloc(p: P, tracked s: Map<K, V>) -> (tracked out: Self)
        requires
            P::rel(p, s),
        ensures
            out.value() == p,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn join(tracked a: Self, tracked b: Self) -> (tracked out: Self)
        requires
            a.loc() == b.loc(),
        ensures
            out.loc() == a.loc(),
            out.value() == P::op(a.value(), b.value()),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn split(tracked self, a_value: P, b_value: P) -> (tracked out: (Self, Self))
        requires
            self.value() == P::op(a_value, b_value),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == a_value,
            out.1.value() == b_value,
    {
        unimplemented!();
    }

    /// Since `inv` isn't closed under inclusion, validity for an element
    /// is defined as the inclusion-closure of invariant, i.e., an element
    /// is valid if there exists another element `x` that, added to it,
    /// meets the invariant.
    #[verifier::external_body]
    pub proof fn validate(tracked a: &Self) -> (out: (P, Map<K, V>))
        ensures
            ({
                let (q, t) = out;
                P::rel(P::op(a.value(), q), t)
            }),
    {
        unimplemented!();
    }

    // Updates and guards
    /// Most general kind of update, potentially depositing and withdrawing
    pub proof fn exchange(
        tracked p: Self,
        tracked s: Map<K, V>,
        new_p_value: P,
        new_s_value: Map<K, V>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            exchanges(p.value(), s, new_p_value, new_s_value),
        ensures
            ({
                let (new_p, new_s) = out;
                new_p.loc() == p.loc() && new_p.value() == new_p_value && new_s == new_s_value
            }),
    {
        let se = set![(new_p_value, new_s_value)];
        Self::exchange_nondeterministic(p, s, se)
    }

    pub proof fn deposit(tracked self, tracked base: Map<K, V>, new_value: P) -> (tracked out: Self)
        requires
            deposits(self.value(), base, new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        Self::exchange(self, base, new_value, Map::empty()).0
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
        Self::exchange(self, Map::tracked_empty(), new_value, new_base)
    }

    /// "Normal" update, no depositing or withdrawing
    pub proof fn update(tracked self, new_value: P) -> (tracked out: Self)
        requires
            updates(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        Self::exchange(self, Map::tracked_empty(), new_value, Map::empty()).0
    }

    pub proof fn exchange_nondeterministic(
        tracked p: Self,
        tracked s: Map<K, V>,
        new_values: Set<(P, Map<K, V>)>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            exchanges_nondeterministic(p.value(), s, new_values),
        ensures
            ({
                let (new_p, new_s) = out;
                new_p.loc() == p.loc() && new_values.contains((new_p.value(), new_s))
            }),
    {
        P::op_unit(p.value());
        let tracked (selff, unit) = p.split(p.value(), P::unit());
        let new_values0 = set_op(new_values, P::unit());
        super::set_lib::assert_sets_equal!(new_values0, new_values, v => {
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
        Self::exchange_nondeterministic_with_shared(selff, &unit, s, new_values)
    }

    #[verifier::external_body]
    pub proof fn guard(tracked p: &Self, s_value: Map<K, V>) -> (tracked s: &Map<K, V>)
        requires
            guards(p.value(), s_value),
        ensures
            s == s_value,
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
    pub proof fn validate_with_shared(tracked p: &mut Self, tracked x: &Self) -> (res: (
        P,
        Map<K, V>,
    ))
        requires
            old(p).loc() == x.loc(),
        ensures
            *p == *old(p),
            ({
                let (q, t) = res;
                { P::rel(P::op(P::op(p.value(), x.value()), q), t) }
            }),
    {
        unimplemented!();
    }

    // See `logic_exchange_with_extra_guard`
    // https://github.com/secure-foundations/leaf/blob/a51725deedecc88294057ac1502a7c7ff2104a69/src/guarding/protocol.v#L720
    pub proof fn exchange_with_shared(
        tracked p: Self,
        tracked x: &Self,
        tracked s: Map<K, V>,
        new_p_value: P,
        new_s_value: Map<K, V>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            p.loc() == x.loc(),
            exchanges(P::op(p.value(), x.value()), s, P::op(new_p_value, x.value()), new_s_value),
        ensures
            out.0.loc() == p.loc(),
            out.0.value() == new_p_value,
            out.1 == new_s_value,
    {
        let se = set![(new_p_value, new_s_value)];
        Self::exchange_nondeterministic_with_shared(p, x, s, se)
    }

    // See `logic_exchange_with_extra_guard_nondeterministic`
    // https://github.com/secure-foundations/leaf/blob/a51725deedecc88294057ac1502a7c7ff2104a69/src/guarding/protocol.v#L834
    /// Most general kind of update, potentially depositing and withdrawing
    #[verifier::external_body]
    pub proof fn exchange_nondeterministic_with_shared(
        tracked p: Self,
        tracked x: &Self,
        tracked s: Map<K, V>,
        new_values: Set<(P, Map<K, V>)>,
    ) -> (tracked out: (Self, Map<K, V>))
        requires
            p.loc() == x.loc(),
            exchanges_nondeterministic(
                P::op(p.value(), x.value()),
                s,
                set_op(new_values, x.value()),
            ),
        ensures
            ({
                let (new_p, new_s) = out;
                new_p.loc() == p.loc() && new_values.contains((new_p.value(), new_s))
            }),
    {
        unimplemented!();
    }
}

} // verus!
