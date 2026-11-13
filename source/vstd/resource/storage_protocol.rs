use super::super::prelude::*;
use super::Loc;
use super::trusted;

verus! {

broadcast use {super::super::iset::group_iset_lemmas, super::super::imap::group_imap_lemmas};

/// Interface for "storage protocol" ghost state.
/// This is an extension-slash-variant on the more well-known concept
/// of "PCM" ghost state, which we also have an interface for [here](crate::resource::pcm::Resource).
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
/// In this interface, we fix the base monoid to be of the form [`IMap<K, V>`](crate::imap::IMap).
/// (with composition of overlapping maps being undefined), which has all the necessary properties.
/// Note that there's no `create_unit` (it's not sound to do this for an arbitrary location unless you
/// already know a protocol was initialized at that location).
///
/// For applications, I generally advise using the
/// [`tokenized_state_machine!` system](https://verus-lang.github.io/verus/state_machines/),
/// rather than using this interface directly.
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(P)]
#[verifier::accept_recursive_types(V)]
pub tracked struct StorageResource<K, V, P> {
    r: trusted::protocol::StorageResource<K, V, P>,
}

#[cfg(verus_keep_ghost)]
#[verifier::external]
impl<K, V, P> !Copy for StorageResource<K, V, P> {

}

#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(P)]
#[verifier::accept_recursive_types(V)]
pub tracked struct CopyableStorageResource<K, V, P> {
    r: trusted::protocol::CopyableStorageResource<K, V, P>,
}

impl<K, V, P> Copy for CopyableStorageResource<K, V, P> {

}

impl<K, V, P> Clone for CopyableStorageResource<K, V, P> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        *self
    }
}

/// See [`StorageResource`] for more information.
pub trait Protocol<K, V>: Sized {
    spec fn op(self, other: Self) -> Self;

    /// Note that `rel`, in contrast to [`PCM::valid`](crate::resource::algebra::ResourceAlgebra::valid), is not
    /// necessarily closed under inclusion.
    spec fn rel(self, s: IMap<K, V>) -> bool;

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

pub open spec fn guards<K, V, P: Protocol<K, V>>(p: P, b: IMap<K, V>) -> bool {
    forall|q: P, t: IMap<K, V>| #![all_triggers] P::rel(P::op(p, q), t) ==> b.submap_of(t)
}

pub open spec fn exchanges<K, V, P: Protocol<K, V>>(
    p1: P,
    b1: IMap<K, V>,
    p2: P,
    b2: IMap<K, V>,
) -> bool {
    forall|q: P, t1: IMap<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> {
            &&& P::rel(P::op(p2, q), t1.union_prefer_right(b1).remove_keys(b2.dom()))
            &&& t1.dom().disjoint(b1.dom())
            &&& b2.submap_of(t1.union_prefer_right(b1))
        }
}

pub open spec fn exchanges_nondeterministic<K, V, P: Protocol<K, V>>(
    p1: P,
    s1: IMap<K, V>,
    new_values: ISet<(P, IMap<K, V>)>,
) -> bool {
    forall|q: P, t1: IMap<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> exists|p2: P, s2: IMap<K, V>, t2: IMap<K, V>|
            #![all_triggers]
            {
                &&& new_values.contains((p2, s2))
                &&& P::rel(P::op(p2, q), t2)
                &&& t1.dom().disjoint(s1.dom())
                &&& t2.dom().disjoint(s2.dom())
                &&& t1.union_prefer_right(s1) =~= t2.union_prefer_right(s2)
            }
}

pub open spec fn deposits<K, V, P: Protocol<K, V>>(p1: P, b1: IMap<K, V>, p2: P) -> bool {
    forall|q: P, t1: IMap<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> {
            &&& P::rel(P::op(p2, q), t1.union_prefer_right(b1))
            &&& t1.dom().disjoint(b1.dom())
        }
}

pub open spec fn withdraws<K, V, P: Protocol<K, V>>(p1: P, p2: P, b2: IMap<K, V>) -> bool {
    forall|q: P, t1: IMap<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> {
            &&& P::rel(P::op(p2, q), t1.remove_keys(b2.dom()))
            &&& b2.submap_of(t1)
        }
}

pub open spec fn updates<K, V, P: Protocol<K, V>>(p1: P, p2: P) -> bool {
    forall|q: P, t1: IMap<K, V>|
        #![all_triggers]
        P::rel(P::op(p1, q), t1) ==> P::rel(P::op(p2, q), t1)
}

pub open spec fn set_op<K, V, P: Protocol<K, V>>(s: ISet<(P, IMap<K, V>)>, t: P) -> ISet<
    (P, IMap<K, V>),
> {
    s.map(|q: (P, IMap<K, V>)| (P::op(q.0, t), q.1))
}

/// Every [`Protocol`] is a [`Protocol`](trusted::protocol::Protocol) in the sense of the trusted interface.
impl<K, V, P: Protocol<K, V>> trusted::protocol::Protocol<K, V> for P {
    open spec fn op(self, other: Self) -> Self {
        <P as Protocol<K, V>>::op(self, other)
    }

    open spec fn rel(self, s: IMap<K, V>) -> bool {
        <P as Protocol<K, V>>::rel(self, s)
    }

    open spec fn unit() -> Self {
        <P as Protocol<K, V>>::unit()
    }

    proof fn commutative(a: Self, b: Self) {
        <P as Protocol<K, V>>::commutative(a, b);
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        <P as Protocol<K, V>>::associative(a, b, c);
    }

    proof fn op_unit(a: Self) {
        <P as Protocol<K, V>>::op_unit(a);
    }
}

impl<K, V, P: Protocol<K, V>> StorageResource<K, V, P> {
    pub closed spec fn value(self) -> P {
        self.r.value()
    }

    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    proof fn mk_ref<'a>(tracked r: &'a trusted::protocol::StorageResource<K, V, P>) -> (tracked res:
        &'a Self)
        ensures
            res.r == r,
    {
        shr_ref_struct_wrap(r, &Self { r: arbitrary() }, "", "r")
    }

    pub proof fn alloc(p: P, tracked s: IMap<K, V>) -> (tracked out: Self)
        requires
            P::rel(p, s),
        ensures
            out.value() == p,
    {
        StorageResource { r: trusted::protocol::StorageResource::alloc(p, s) }
    }

    pub proof fn join(tracked a: Self, tracked b: Self) -> (tracked out: Self)
        requires
            a.loc() == b.loc(),
        ensures
            out.loc() == a.loc(),
            out.value() == P::op(a.value(), b.value()),
    {
        StorageResource { r: trusted::protocol::StorageResource::join(a.r, b.r) }
    }

    pub proof fn split(tracked self, a_value: P, b_value: P) -> (tracked out: (Self, Self))
        requires
            self.value() == P::op(a_value, b_value),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.value() == a_value,
            out.1.value() == b_value,
    {
        let tracked (a, b) = self.r.split(a_value, b_value);
        (StorageResource { r: a }, StorageResource { r: b })
    }

    /// Since `inv` isn't closed under inclusion, validity for an element
    /// is defined as the inclusion-closure of invariant, i.e., an element
    /// is valid if there exists another element `x` that, added to it,
    /// meets the invariant.
    pub proof fn validate(tracked self: &Self) -> (out: (P, IMap<K, V>))
        ensures
            ({
                let (q, t) = out;
                P::rel(P::op(self.value(), q), t)
            }),
    {
        trusted::protocol::StorageResource::validate(&self.r)
    }

    // Helper lemma saying that unioning with an empty map is a no-op.
    proof fn lemma_union_prefer_right_empty_is_noop_forall()
        ensures
            forall|m: IMap<K, V>| #[trigger] m.union_prefer_right(IMap::empty()) == m,
    {
        assert forall|m: IMap<K, V>| #[trigger] m.union_prefer_right(IMap::empty()) == m by {
            assert(m.union_prefer_right(IMap::empty()) =~= m);
        }
    }

    // Helper lemma saying that removing the empty set of keys from a map is a no-op.
    proof fn lemma_removing_empty_keys_is_noop_forall()
        ensures
            forall|m: IMap<K, V>| #[trigger] m.remove_keys(ISet::empty()) == m,
    {
        assert forall|m: IMap<K, V>| m.remove_keys(ISet::empty()) == m by {
            assert(m.remove_keys(ISet::empty()) =~= m);
        }
    }

    // Updates and guards
    /// Most general kind of update, potentially depositing and withdrawing
    pub proof fn exchange(
        tracked p: Self,
        tracked s: IMap<K, V>,
        new_p_value: P,
        new_s_value: IMap<K, V>,
    ) -> (tracked out: (Self, IMap<K, V>))
        requires
            exchanges(p.value(), s, new_p_value, new_s_value),
        ensures
            ({
                let (new_p, new_s) = out;
                new_p.loc() == p.loc() && new_p.value() == new_p_value && new_s == new_s_value
            }),
    {
        let se = iset![(new_p_value, new_s_value)];
        Self::exchange_nondeterministic(p, s, se)
    }

    pub proof fn deposit(tracked self, tracked base: IMap<K, V>, new_value: P) -> (tracked out:
        Self)
        requires
            deposits(self.value(), base, new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        Self::lemma_removing_empty_keys_is_noop_forall();
        Self::exchange(self, base, new_value, IMap::empty()).0
    }

    pub proof fn withdraw(tracked self, new_value: P, new_base: IMap<K, V>) -> (tracked out: (
        Self,
        IMap<K, V>,
    ))
        requires
            withdraws(self.value(), new_value, new_base),
        ensures
            out.0.loc() == self.loc(),
            out.0.value() == new_value,
            out.1 == new_base,
    {
        Self::lemma_union_prefer_right_empty_is_noop_forall();
        Self::exchange(self, IMap::tracked_empty(), new_value, new_base)
    }

    /// "Normal" update, no depositing or withdrawing
    pub proof fn update(tracked self, new_value: P) -> (tracked out: Self)
        requires
            updates(self.value(), new_value),
        ensures
            out.loc() == self.loc(),
            out.value() == new_value,
    {
        Self::lemma_union_prefer_right_empty_is_noop_forall();
        Self::lemma_removing_empty_keys_is_noop_forall();
        Self::exchange(self, IMap::tracked_empty(), new_value, IMap::empty()).0
    }

    pub proof fn exchange_nondeterministic(
        tracked p: Self,
        tracked s: IMap<K, V>,
        new_values: ISet<(P, IMap<K, V>)>,
    ) -> (tracked out: (Self, IMap<K, V>))
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
        super::super::iset_lib::assert_isets_equal!(new_values0, new_values, v => {
            P::op_unit(v.0);
            if new_values.contains(v) {
                assert(new_values0.contains(v));
            }
            if new_values0.contains(v) {
                let q = choose |q| #[trigger] new_values.contains(q) && v == (P::op(q.0, P::unit()), q.1);
                assert(P::op(q.0, P::unit()) == q.0) by { P::op_unit(q.0) }
                assert(v =~= q);
                assert(new_values.contains(v));
            }
        });
        Self::exchange_nondeterministic_with_shared(selff, &unit, s, new_values)
    }

    pub proof fn guard(tracked p: &Self, s_value: IMap<K, V>) -> (tracked s: &IMap<K, V>)
        requires
            guards(p.value(), s_value),
        ensures
            s == s_value,
    {
        trusted::protocol::StorageResource::guard(&p.r, s_value)
    }

    // Operations with shared references
    pub proof fn join_shared<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked out:
        &'a Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            incl(self.value(), out.value()),
            incl(other.value(), out.value()),
    {
        Self::mk_ref(self.r.join_shared(&other.r))
    }

    pub proof fn weaken<'a>(tracked &'a self, target: P) -> (tracked out: &'a Self)
        requires
            incl(target, self.value()),
        ensures
            out.loc() == self.loc(),
            out.value() == target,
    {
        let c = choose|c| P::op(target, c) == self.value();
        assert(<P as trusted::protocol::Protocol<K, V>>::op(target, c) == self.value());
        Self::mk_ref(self.r.weaken(target))
    }

    pub proof fn validate_with_shared(tracked self: &mut Self, tracked x: &Self) -> (res: (
        P,
        IMap<K, V>,
    ))
        requires
            old(self).loc() == x.loc(),
        ensures
            *final(self) == *old(self),
            ({
                let (q, t) = res;
                { P::rel(P::op(P::op(final(self).value(), x.value()), q), t) }
            }),
    {
        trusted::protocol::StorageResource::validate_with_shared(&mut self.r, &x.r)
    }

    // See `logic_exchange_with_extra_guard`
    // https://github.com/secure-foundations/leaf/blob/a51725deedecc88294057ac1502a7c7ff2104a69/src/guarding/protocol.v#L720
    pub proof fn exchange_with_shared(
        tracked p: Self,
        tracked x: &Self,
        tracked s: IMap<K, V>,
        new_p_value: P,
        new_s_value: IMap<K, V>,
    ) -> (tracked out: (Self, IMap<K, V>))
        requires
            p.loc() == x.loc(),
            exchanges(P::op(p.value(), x.value()), s, P::op(new_p_value, x.value()), new_s_value),
        ensures
            out.0.loc() == p.loc(),
            out.0.value() == new_p_value,
            out.1 == new_s_value,
    {
        let se = iset![(new_p_value, new_s_value)];
        assert(exchanges_nondeterministic(P::op(p.value(), x.value()), s, set_op(se, x.value())))
            by {
            let new_values = set_op(se, x.value());
            assert(se.contains((new_p_value, new_s_value)));
            assert(new_values.contains((P::op(new_p_value, x.value()), new_s_value)));
        }
        Self::exchange_nondeterministic_with_shared(p, x, s, se)
    }

    // See `logic_exchange_with_extra_guard_nondeterministic`
    // https://github.com/secure-foundations/leaf/blob/a51725deedecc88294057ac1502a7c7ff2104a69/src/guarding/protocol.v#L834
    /// Most general kind of update, potentially depositing and withdrawing
    pub proof fn exchange_nondeterministic_with_shared(
        tracked p: Self,
        tracked x: &Self,
        tracked s: IMap<K, V>,
        new_values: ISet<(P, IMap<K, V>)>,
    ) -> (tracked out: (Self, IMap<K, V>))
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
        let ghost new_values0 = set_op(new_values, x.value());
        let ghost f = |q: P, t1: IMap<K, V>|
            choose|r: (P, IMap<K, V>, IMap<K, V>)|
                {
                    &&& #[trigger] new_values0.contains((r.0, r.1))
                    &&& P::rel(P::op(r.0, q), r.2)
                    &&& t1.dom().disjoint(s.dom())
                    &&& r.2.dom().disjoint(r.1.dom())
                    &&& t1.union_prefer_right(s) =~= r.2.union_prefer_right(r.1)
                };
        assert(trusted::protocol::set_op(new_values, x.value()) =~= new_values0);
        let ghost a = P::op(p.value(), x.value());
        assert forall|q: P, t1: IMap<K, V>| P::rel(P::op(a, q), t1) implies {
            let (p2, s2, t2) = f(q, t1);
            &&& new_values0.contains((p2, s2))
            &&& P::rel(P::op(p2, q), t2)
            &&& t1.dom().disjoint(s.dom())
            &&& t2.dom().disjoint(s2.dom())
            &&& t1.union_prefer_right(s) =~= t2.union_prefer_right(s2)
        } by {
            let (p2, s2, t2) = choose|p2: P, s2: IMap<K, V>, t2: IMap<K, V>|
                #![all_triggers]
                {
                    &&& new_values0.contains((p2, s2))
                    &&& P::rel(P::op(p2, q), t2)
                    &&& t1.dom().disjoint(s.dom())
                    &&& t2.dom().disjoint(s2.dom())
                    &&& t1.union_prefer_right(s) =~= t2.union_prefer_right(s2)
                };
            assert(new_values0.contains((p2, s2)));
        }
        let tracked (r, s) =
            trusted::protocol::StorageResource::exchange_nondeterministic_with_shared(
            p.r,
            &x.r,
            s,
            new_values,
            f,
        );
        (StorageResource { r }, s)
    }

    /// Wrap this resource in a type that implements `Copy`,
    /// given that the resource is duplicable.
    pub proof fn into_copyable(tracked self, p: P) -> (tracked r: CopyableStorageResource<K, V, P>)
        requires
            P::op(P::op(self.value(), self.value()), p) == self.value(),
        ensures
            r.loc() == self.loc(),
            r.value() == self.value(),
    {
        CopyableStorageResource { r: self.r.into_copyable(p) }
    }
}

/// A variant of [`StorageResource`] that implements `Copy`.
///
/// Use [`Self::into_resource`] to get the underlying resource.
impl<K, V, P: Protocol<K, V>> CopyableStorageResource<K, V, P> {
    /// The underlying value of the resource
    pub closed spec fn value(self) -> P {
        self.r.value()
    }

    /// The location of the resource
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub proof fn into_resource(tracked self) -> (tracked r: StorageResource<K, V, P>)
        ensures
            r.loc() == self.loc(),
            r.value() == self.value(),
    {
        StorageResource { r: self.r.into_resource() }
    }
}

} // verus!
