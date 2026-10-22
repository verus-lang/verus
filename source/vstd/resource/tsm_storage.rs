//! Storage resources for proof-producing tokenized state machines.
//!
//! The protocol relation describes a complete invariant-satisfying state. The
//! existing storage-protocol primitives supply fragment ownership and borrowed
//! guards; machine transitions prove their exchanges for every possible frame.
use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;
use super::storage_protocol::{self, Protocol, StorageResource};
use super::tsm::{completes, fragment_included, Machine};
use super::Loc;

verus! {

broadcast use {super::super::iset::group_iset_lemmas, super::super::imap::group_imap_lemmas};

/// A machine embedding separates its token fragments from its stored resources.
pub trait StorageMachine: Machine {
    type Key;
    type Value;

    spec fn storage(state: Self::State) -> IMap<Self::Key, Self::Value>;
}

/// Adding an empty ownership frame preserves the set of exchange outputs.
pub proof fn storage_outputs_unit<M: StorageMachine>(
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
)
    ensures
        outputs.map(
            |pair: (M::Fragment, IMap<M::Key, M::Value>)|
                (M::Fragment::op(pair.0, M::Fragment::unit()), pair.1),
        ) == outputs,
{
    let lifted = outputs.map(
        |pair: (M::Fragment, IMap<M::Key, M::Value>)|
            (M::Fragment::op(pair.0, M::Fragment::unit()), pair.1),
    );
    assert forall|pair: (M::Fragment, IMap<M::Key, M::Value>)|
        lifted.contains(pair) == outputs.contains(pair) by {
        if lifted.contains(pair) {
            let original = choose|original: (M::Fragment, IMap<M::Key, M::Value>)|
                outputs.contains(original) && pair == (
                    M::Fragment::op(original.0, M::Fragment::unit()),
                    original.1,
                );
            original.0.op_unit();
            assert(pair == original);
        }
        if outputs.contains(pair) {
            pair.0.op_unit();
            assert(exists|original: (M::Fragment, IMap<M::Key, M::Value>)|
                outputs.contains(original) && pair == (
                    M::Fragment::op(original.0, M::Fragment::unit()),
                    original.1,
                ));
        }
    };
    assert(super::super::prelude::ext_equal(lifted, outputs));
}

/// Divide stored ownership into retained resources and their exact remainder.
/// Generated exchanges apply this to the old base extended by the deposit.
pub proof fn storage_partition<K, V>(whole: IMap<K, V>, retained: IMap<K, V>)
    requires
        retained.submap_of(whole),
    ensures
        retained.dom().disjoint(whole.remove_keys(retained.dom()).dom()),
        whole =~= retained.union_prefer_right(whole.remove_keys(retained.dom())),
        whole.remove_keys(retained.dom()).submap_of(whole),
{
    let remainder = whole.remove_keys(retained.dom());
    assert(retained.dom().disjoint(remainder.dom())) by {
        assert forall|key: K| #[trigger] retained.contains_key(key)
            implies !remainder.contains_key(key) by {};
    }
    assert(whole =~= retained.union_prefer_right(remainder)) by {
        assert forall|key: K| #[trigger] whole.contains_key(key)
            <==> retained.union_prefer_right(remainder).contains_key(key) by {};
        assert forall|key: K| #[trigger] whole.contains_key(key)
            implies whole[key] == retained.union_prefer_right(remainder)[key] by {
            if retained.contains_key(key) {
                assert(retained[key] == whole[key]);
            }
        };
    }
}

/// An exchange between agreeing maps deposits exactly the newly present keys.
pub proof fn storage_delta<K, V>(old: IMap<K, V>, new: IMap<K, V>)
    requires
        old.agrees(new),
    ensures
        old.dom().disjoint(new.remove_keys(old.dom()).dom()),
        new.submap_of(old.union_prefer_right(new.remove_keys(old.dom()))),
{
    let deposit = new.remove_keys(old.dom());
    assert(old.dom().disjoint(deposit.dom())) by {
        assert forall|key: K| #[trigger] old.contains_key(key)
            implies !deposit.contains_key(key) by {};
    }
    assert(new.submap_of(old.union_prefer_right(deposit))) by {
        assert forall|key: K| #[trigger] new.contains_key(key) implies {
            &&& old.union_prefer_right(deposit).contains_key(key)
            &&& new[key] == old.union_prefer_right(deposit)[key]
        } by {
            if old.contains_key(key) {
                assert(old[key] == new[key]);
            }
        };
    }
}

/// A step that only adds storage (its deposit is the newly present keys)
/// withdraws nothing.
pub proof fn storage_withdrawn_none<K, V>(old: IMap<K, V>, new: IMap<K, V>, deposit: IMap<K, V>)
    requires
        old.submap_of(new),
        deposit == new.remove_keys(old.dom()),
    ensures
        old.union_prefer_right(deposit).remove_keys(new.dom()) == IMap::<K, V>::empty(),
{
    let withdrawn = old.union_prefer_right(deposit).remove_keys(new.dom());
    assert forall|key: K| !#[trigger] withdrawn.contains_key(key) by {};
    assert(super::super::prelude::ext_equal(withdrawn, IMap::<K, V>::empty()));
}

/// One frame of a generated exchange: for the complete state `pre` around
/// `op(op(owned, h), z)`, some output `new` (withdrawing what the step from
/// `pre` to `post` leaves out of the old base and the deposit) completes to the
/// invariant state `post` with the same borrowed fragment `h` and frame `z`.
#[verifier::opaque]
pub open spec fn exchange_point<M: StorageMachine>(
    owned: M::Fragment,
    h: M::Fragment,
    z: M::Fragment,
    pre: M::State,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
) -> bool {
    exists|new: M::Fragment, post: M::State|
        {
            &&& #[trigger] outputs.contains(
                (new, M::storage(pre).union_prefer_right(deposit).remove_keys(M::storage(post).dom())),
            )
            &&& M::invariant(post)
            &&& M::Fragment::op(M::Fragment::op(new, h), z) == M::embed(post)
            &&& M::storage(pre).dom().disjoint(deposit.dom())
            &&& M::storage(post).submap_of(M::storage(pre).union_prefer_right(deposit))
        }
}

/// Introduces [`exchange_point`] for the witnesses `new` and `post`.
pub proof fn exchange_point_intro<M: StorageMachine>(
    owned: M::Fragment,
    h: M::Fragment,
    z: M::Fragment,
    pre: M::State,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
    new: M::Fragment,
    post: M::State,
)
    requires
        outputs.contains(
            (new, M::storage(pre).union_prefer_right(deposit).remove_keys(M::storage(post).dom())),
        ),
        M::invariant(post),
        M::Fragment::op(M::Fragment::op(new, h), z) == M::embed(post),
        M::storage(pre).dom().disjoint(deposit.dom()),
        M::storage(post).submap_of(M::storage(pre).union_prefer_right(deposit)),
    ensures
        exchange_point::<M>(owned, h, z, pre, deposit, outputs),
{
    reveal(exchange_point);
}

/// Introduces [`exchange_point`] for a step between agreeing storage maps whose
/// deposit is exactly the newly present keys.
pub proof fn exchange_point_intro_delta<M: StorageMachine>(
    owned: M::Fragment,
    h: M::Fragment,
    z: M::Fragment,
    pre: M::State,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
    new: M::Fragment,
    post: M::State,
)
    requires
        outputs.contains(
            (new, M::storage(pre).union_prefer_right(deposit).remove_keys(M::storage(post).dom())),
        ),
        M::invariant(post),
        M::Fragment::op(M::Fragment::op(new, h), z) == M::embed(post),
        M::storage(pre).agrees(M::storage(post)),
        deposit == M::storage(post).remove_keys(M::storage(pre).dom()),
    ensures
        exchange_point::<M>(owned, h, z, pre, deposit, outputs),
{
    storage_delta(M::storage(pre), M::storage(post));
    exchange_point_intro::<M>(owned, h, z, pre, deposit, outputs, new, post);
}

/// Introduces [`exchange_point`] for a step that only adds storage (between
/// agreeing maps, depositing exactly the newly present keys) and withdraws
/// nothing.
pub proof fn exchange_point_intro_monotone<M: StorageMachine>(
    owned: M::Fragment,
    h: M::Fragment,
    z: M::Fragment,
    pre: M::State,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
    new: M::Fragment,
    post: M::State,
)
    requires
        outputs.contains((new, IMap::<M::Key, M::Value>::empty())),
        M::invariant(post),
        M::Fragment::op(M::Fragment::op(new, h), z) == M::embed(post),
        M::storage(pre).agrees(M::storage(post)),
        M::storage(pre).submap_of(M::storage(post)),
        deposit == M::storage(post).remove_keys(M::storage(pre).dom()),
    ensures
        exchange_point::<M>(owned, h, z, pre, deposit, outputs),
{
    storage_withdrawn_none(M::storage(pre), M::storage(post), deposit);
    exchange_point_intro_delta::<M>(owned, h, z, pre, deposit, outputs, new, post);
}

/// The frame obligation of a generated exchange, from its proof for each
/// frame: the outputs are lifted by the borrowed fragment `h`.
pub proof fn frame_exchange_by_points<M: StorageMachine>(
    owned: M::Fragment,
    h: M::Fragment,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
)
    requires
        forall|z: M::Fragment, pre: M::State|
            M::invariant(pre) && M::Fragment::op(M::Fragment::op(owned, h), z) == M::embed(pre)
                ==> #[trigger] exchange_point::<M>(owned, h, z, pre, deposit, outputs),
    ensures
        frame_exchange_nondeterministic::<M>(
            M::Fragment::op(owned, h),
            deposit,
            outputs.map(
                |pair: (M::Fragment, IMap<M::Key, M::Value>)|
                    (M::Fragment::op(pair.0, h), pair.1),
            ),
        ),
{
    reveal(exchange_point);
    reveal(frame_exchange_nondeterministic);
    let lifted = outputs.map(
        |pair: (M::Fragment, IMap<M::Key, M::Value>)| (M::Fragment::op(pair.0, h), pair.1),
    );
    assert forall|z: M::Fragment, pre: M::State|
        M::invariant(pre) && M::Fragment::op(M::Fragment::op(owned, h), z) == M::embed(
            pre,
        ) implies exists|new: M::Fragment, withdraw: IMap<M::Key, M::Value>, next: M::State|
        {
            &&& lifted.contains((new, withdraw))
            &&& M::invariant(next)
            &&& M::Fragment::op(new, z) == M::embed(next)
            &&& M::storage(pre).dom().disjoint(deposit.dom())
            &&& M::storage(next).dom().disjoint(withdraw.dom())
            &&& M::storage(pre).union_prefer_right(deposit) =~= M::storage(
                next,
            ).union_prefer_right(withdraw)
        } by {
        assert(exchange_point::<M>(owned, h, z, pre, deposit, outputs));
        let (new, post) = choose|new: M::Fragment, post: M::State|
            {
                &&& #[trigger] outputs.contains(
                    (
                        new,
                        M::storage(pre).union_prefer_right(deposit).remove_keys(
                            M::storage(post).dom(),
                        ),
                    ),
                )
                &&& M::invariant(post)
                &&& M::Fragment::op(M::Fragment::op(new, h), z) == M::embed(post)
                &&& M::storage(pre).dom().disjoint(deposit.dom())
                &&& M::storage(post).submap_of(M::storage(pre).union_prefer_right(deposit))
            };
        let whole = M::storage(pre).union_prefer_right(deposit);
        storage_partition(whole, M::storage(post));
        let withdraw = whole.remove_keys(M::storage(post).dom());
        assert(lifted.contains((M::Fragment::op(new, h), withdraw)));
    }
}

/// The storage-protocol carrier of a machine `M` with fragment type `F`.
///
/// The declaration has no trait bounds and mentions no associated types, so a
/// concrete carrier type does not depend on the `StorageMachine` impl of `M` in
/// Verus's type graph. A machine whose stored values contain its own tokens
/// therefore forms an ordinary cycle of datatypes, which the strict-positivity
/// check accepts or rejects, rather than a cycle through a trait impl.
/// The protocol is only implemented for `F == M::Fragment` (see [`Carrier`]).
#[verifier::accept_recursive_types(M)]
#[verifier::reject_recursive_types_in_ground_variants(F)]
pub struct StorageCarrier<M, F> {
    pub fragment: F,
    pub machine: core::marker::PhantomData<M>,
}

/// The carrier used by [`StorageToken`].
pub type Carrier<M> = StorageCarrier<M, <M as Machine>::Fragment>;

/// The carrier value holding `fragment`.
pub open spec fn carrier_of<M: StorageMachine>(fragment: M::Fragment) -> Carrier<M> {
    StorageCarrier { fragment, machine: core::marker::PhantomData }
}

impl<M: StorageMachine> Protocol<M::Key, M::Value> for StorageCarrier<M, M::Fragment> {
    open spec fn op(self, other: Self) -> Self {
        carrier_of::<M>(M::Fragment::op(self.fragment, other.fragment))
    }

    open spec fn rel(self, base: IMap<M::Key, M::Value>) -> bool {
        exists|state: M::State| M::invariant(state)
            && self.fragment == M::embed(state) && base == M::storage(state)
    }

    open spec fn unit() -> Self {
        carrier_of::<M>(M::Fragment::unit())
    }

    proof fn commutative(a: Self, b: Self) {
        M::Fragment::commutative(a.fragment, b.fragment);
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        M::Fragment::associative(a.fragment, b.fragment, c.fragment);
    }

    proof fn op_unit(a: Self) {
        M::Fragment::op_unit(a.fragment);
    }
}

/// Deposit and withdrawal preserve every untouched token fragment.
#[verifier::opaque]
pub open spec fn frame_exchange<M: StorageMachine>(
    old: M::Fragment,
    deposit: IMap<M::Key, M::Value>,
    new: M::Fragment,
    withdraw: IMap<M::Key, M::Value>,
) -> bool {
    forall|frame: M::Fragment, state: M::State|
        M::invariant(state) && M::Fragment::op(old, frame) == M::embed(state) ==> {
            &&& M::storage(state).dom().disjoint(deposit.dom())
            &&& withdraw.submap_of(M::storage(state).union_prefer_right(deposit))
            &&& exists|next: M::State| M::invariant(next)
                && M::Fragment::op(new, frame) == M::embed(next)
                && M::storage(next)
                    == M::storage(state).union_prefer_right(deposit).remove_keys(withdraw.dom())
        }
}

/// Nondeterministic exchanges can choose an output using the full state.
#[verifier::opaque]
pub open spec fn frame_exchange_nondeterministic<M: StorageMachine>(
    old: M::Fragment,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
) -> bool {
    forall|frame: M::Fragment, state: M::State|
        M::invariant(state) && M::Fragment::op(old, frame) == M::embed(state)
            ==> exists|new: M::Fragment, withdraw: IMap<M::Key, M::Value>, next: M::State| {
                &&& outputs.contains((new, withdraw))
                &&& M::invariant(next)
                &&& M::Fragment::op(new, frame) == M::embed(next)
                &&& M::storage(state).dom().disjoint(deposit.dom())
                &&& M::storage(next).dom().disjoint(withdraw.dom())
                &&& M::storage(state).union_prefer_right(deposit)
                    =~= M::storage(next).union_prefer_right(withdraw)
            }
}

/// A borrowed fragment guarantees that a specified resource stays stored.
pub open spec fn frame_guard<M: StorageMachine>(
    fragment: M::Fragment,
    guarded: IMap<M::Key, M::Value>,
) -> bool {
    forall|frame: M::Fragment, state: M::State|
        M::invariant(state) && M::Fragment::op(fragment, frame) == M::embed(state)
            ==> guarded.submap_of(M::storage(state))
}

/// An exchange that preserves every frame also preserves an explicitly borrowed
/// fragment. This lets generated operations reuse their ordinary frame proof.
pub proof fn frame_exchange_with_extra<M: StorageMachine>(
    old: M::Fragment,
    deposit: IMap<M::Key, M::Value>,
    new: M::Fragment,
    withdraw: IMap<M::Key, M::Value>,
    extra: M::Fragment,
)
    requires
        frame_exchange::<M>(old, deposit, new, withdraw),
    ensures
        frame_exchange::<M>(
            M::Fragment::op(old, extra),
            deposit,
            M::Fragment::op(new, extra),
            withdraw,
        ),
{
    reveal(frame_exchange);
    assert forall|frame: M::Fragment, state: M::State|
        M::invariant(state)
            && M::Fragment::op(M::Fragment::op(old, extra), frame) == M::embed(state)
        implies {
            &&& M::storage(state).dom().disjoint(deposit.dom())
            &&& withdraw.submap_of(M::storage(state).union_prefer_right(deposit))
            &&& exists|next: M::State| M::invariant(next)
                && M::Fragment::op(M::Fragment::op(new, extra), frame) == M::embed(next)
                && M::storage(next)
                    == M::storage(state).union_prefer_right(deposit).remove_keys(withdraw.dom())
        } by {
        M::Fragment::associative(old, extra, frame);
        let next = choose|next: M::State| M::invariant(next)
            && M::Fragment::op(new, M::Fragment::op(extra, frame)) == M::embed(next)
            && M::storage(next)
                == M::storage(state).union_prefer_right(deposit).remove_keys(withdraw.dom());
        M::Fragment::associative(new, extra, frame);
    }
}

/// A checked frame exchange of machine fragments is a storage-protocol exchange of their
/// carriers.
pub proof fn frame_exchange_sound<M: StorageMachine>(
    old: M::Fragment,
    deposit: IMap<M::Key, M::Value>,
    new: M::Fragment,
    withdraw: IMap<M::Key, M::Value>,
)
    requires
        frame_exchange::<M>(old, deposit, new, withdraw),
    ensures
        storage_protocol::exchanges(
            carrier_of::<M>(old),
            deposit,
            carrier_of::<M>(new),
            withdraw,
        ),
{
    reveal(frame_exchange);
    assert forall|frame: Carrier<M>, base: IMap<M::Key, M::Value>|
        #[trigger] Carrier::<M>::op(carrier_of::<M>(old), frame).rel(base) implies {
            &&& Carrier::<M>::op(carrier_of::<M>(new), frame).rel(
                base.union_prefer_right(deposit).remove_keys(withdraw.dom()),
            )
            &&& base.dom().disjoint(deposit.dom())
            &&& withdraw.submap_of(base.union_prefer_right(deposit))
        } by {
        let state = choose|state: M::State| M::invariant(state)
            && M::Fragment::op(old, frame.fragment) == M::embed(state)
            && base == M::storage(state);
        let next = choose|next: M::State| M::invariant(next)
            && M::Fragment::op(new, frame.fragment) == M::embed(next)
            && M::storage(next)
                == base.union_prefer_right(deposit).remove_keys(withdraw.dom());
        assert(Carrier::<M>::op(carrier_of::<M>(new), frame).rel(
            base.union_prefer_right(deposit).remove_keys(withdraw.dom()),
        ));
    }
}

/// A checked nondeterministic frame exchange of machine fragments is a nondeterministic
/// storage-protocol exchange of their carriers.
pub proof fn frame_exchange_nondeterministic_sound<M: StorageMachine>(
    old: M::Fragment,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
)
    requires
        frame_exchange_nondeterministic::<M>(old, deposit, outputs),
    ensures
        storage_protocol::exchanges_nondeterministic(
            carrier_of::<M>(old),
            deposit,
            ISet::new(
                |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
                    outputs.contains((pair.0.fragment, pair.1)),
            ),
        ),
{
    reveal(frame_exchange_nondeterministic);
    let wrapped = ISet::new(
        |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
            outputs.contains((pair.0.fragment, pair.1)),
    );
    assert forall|frame: Carrier<M>, base: IMap<M::Key, M::Value>|
        #[trigger] Carrier::<M>::op(carrier_of::<M>(old), frame).rel(base)
            implies exists|new: Carrier<M>, withdraw: IMap<M::Key, M::Value>,
                next_base: IMap<M::Key, M::Value>| {
                    &&& wrapped.contains((new, withdraw))
                    &&& Carrier::<M>::op(new, frame).rel(next_base)
                    &&& base.dom().disjoint(deposit.dom())
                    &&& next_base.dom().disjoint(withdraw.dom())
                    &&& base.union_prefer_right(deposit)
                        =~= next_base.union_prefer_right(withdraw)
                } by {
        let state = choose|state: M::State| M::invariant(state)
            && M::Fragment::op(old, frame.fragment) == M::embed(state)
            && base == M::storage(state);
        let (new, withdraw, next) = choose|new: M::Fragment,
            withdraw: IMap<M::Key, M::Value>, next: M::State| {
                &&& outputs.contains((new, withdraw))
                &&& M::invariant(next)
                &&& M::Fragment::op(new, frame.fragment) == M::embed(next)
                &&& M::storage(state).dom().disjoint(deposit.dom())
                &&& M::storage(next).dom().disjoint(withdraw.dom())
                &&& M::storage(state).union_prefer_right(deposit)
                    =~= M::storage(next).union_prefer_right(withdraw)
            };
        let carrier = carrier_of::<M>(new);
        assert(wrapped.contains((carrier, withdraw)));
        assert(Carrier::<M>::op(carrier, frame).rel(M::storage(next)));
    }
}

/// `frame_exchange_nondeterministic_sound` for an exchange whose frame includes a shared
/// fragment.
pub proof fn frame_exchange_nondeterministic_shared_sound<M: StorageMachine>(
    old: M::Fragment,
    shared: M::Fragment,
    deposit: IMap<M::Key, M::Value>,
    outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
)
    requires
        frame_exchange_nondeterministic::<M>(
            M::Fragment::op(old, shared),
            deposit,
            outputs.map(|pair: (M::Fragment, IMap<M::Key, M::Value>)|
                (M::Fragment::op(pair.0, shared), pair.1)),
        ),
    ensures
        storage_protocol::exchanges_nondeterministic(
            Carrier::<M>::op(carrier_of::<M>(old), carrier_of::<M>(shared)),
            deposit,
            storage_protocol::set_op(
                ISet::new(
                    |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
                        outputs.contains((pair.0.fragment, pair.1)),
                ),
                carrier_of::<M>(shared),
            ),
        ),
{
    let lifted = outputs.map(|pair: (M::Fragment, IMap<M::Key, M::Value>)|
        (M::Fragment::op(pair.0, shared), pair.1));
    frame_exchange_nondeterministic_sound::<M>(
        M::Fragment::op(old, shared), deposit, lifted,
    );
    let wrapped = ISet::new(
        |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
            outputs.contains((pair.0.fragment, pair.1)),
    );
    let wrapped_lifted = ISet::new(
        |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
            lifted.contains((pair.0.fragment, pair.1)),
    );
    let combined = storage_protocol::set_op(wrapped, carrier_of::<M>(shared));
    assert(wrapped_lifted =~= combined) by {
        assert forall|pair: (Carrier<M>, IMap<M::Key, M::Value>)|
            #[trigger] wrapped_lifted.contains(pair) <==> combined.contains(pair) by {
            if wrapped_lifted.contains(pair) {
                let source = choose|source: (M::Fragment, IMap<M::Key, M::Value>)|
                    outputs.contains(source)
                        && (pair.0.fragment, pair.1)
                            == (M::Fragment::op(source.0, shared), source.1);
                let carrier = carrier_of::<M>(source.0);
                assert(wrapped.contains((carrier, source.1)));
                assert(pair == (Carrier::<M>::op(carrier, carrier_of::<M>(shared)), source.1));
                assert(combined.contains(pair));
            }
            if combined.contains(pair) {
                let source = choose|source: (Carrier<M>, IMap<M::Key, M::Value>)|
                    #[trigger] wrapped.contains(source)
                        && pair == (Carrier::<M>::op(source.0, carrier_of::<M>(shared)), source.1);
                assert(lifted.contains((pair.0.fragment, pair.1)));
                assert(wrapped_lifted.contains(pair));
            }
        };
    }
}

/// A checked frame guard of a machine fragment is a storage-protocol guard of its carrier.
pub proof fn frame_guard_sound<M: StorageMachine>(
    fragment: M::Fragment,
    guarded: IMap<M::Key, M::Value>,
)
    requires
        frame_guard::<M>(fragment, guarded),
    ensures
        storage_protocol::guards(carrier_of::<M>(fragment), guarded),
{
    assert forall|frame: Carrier<M>, base: IMap<M::Key, M::Value>|
        #[trigger] Carrier::<M>::op(carrier_of::<M>(fragment), frame).rel(base)
            implies guarded.submap_of(base) by {
        let state = choose|state: M::State| M::invariant(state)
            && M::Fragment::op(fragment, frame.fragment) == M::embed(state)
            && base == M::storage(state);
    }
}

/// Ownership of a machine fragment whose protocol also stores tracked resources.
///
/// Like [`StorageCarrier`], the declaration is free of trait bounds and
/// associated types: the key, value and fragment types are direct parameters,
/// fixed by the [`StorageToken`] alias. Stored values may then contain tokens of
/// the same machine, subject to Verus's strict-positivity check on datatypes.
#[verifier::accept_recursive_types(M)]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
#[verifier::accept_recursive_types(F)]
pub tracked struct StorageTokenOf<M, K, V, F> {
    resource: StorageResource<K, V, StorageCarrier<M, F>>,
}

/// Ownership of a fragment of the storage machine `M`.
pub type StorageToken<M> = StorageTokenOf<
    M,
    <M as StorageMachine>::Key,
    <M as StorageMachine>::Value,
    <M as Machine>::Fragment,
>;

// The observers carry no trait bound, so spec functions that only read a
// token (e.g. instance ids of field tokens) do not depend on the machine's
// `StorageMachine` implementation, whose invariant may mention them.
impl<M, K, V, F> StorageTokenOf<M, K, V, F> {
    pub closed spec fn fragment(self) -> F {
        self.resource.value().fragment
    }

    pub closed spec fn loc(self) -> Loc {
        self.resource.loc()
    }
}

impl<M: StorageMachine> StorageTokenOf<M, M::Key, M::Value, M::Fragment> {

    pub proof fn alloc_state(state: M::State, tracked base: IMap<M::Key, M::Value>)
        -> (tracked out: Self)
        requires
            M::invariant(state),
            base == M::storage(state),
        ensures
            out.fragment() == M::embed(state),
    {
        let carrier = carrier_of::<M>(M::embed(state));
        assert(carrier.rel(base));
        let tracked resource = StorageResource::alloc(carrier, base);
        Self { resource }
    }

    pub proof fn validate(tracked &self)
        ensures
            completes::<M>(self.fragment()),
    {
        let (frame, base) = self.resource.validate();
        let state = choose|state: M::State| M::invariant(state)
            && M::Fragment::op(self.fragment(), frame.fragment) == M::embed(state)
            && base == M::storage(state);
    }

    /// Observe the separating composition with a borrowed token while retaining
    /// ownership of this token and preserving its value.
    pub proof fn validate_2(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            *final(self) == *old(self),
            completes::<M>(M::Fragment::op(final(self).fragment(), other.fragment())),
    {
        let (frame, base) = self.resource.validate_with_shared(&other.resource);
        let state = choose|state: M::State| M::invariant(state)
            && M::Fragment::op(
                M::Fragment::op(self.fragment(), other.fragment()),
                frame.fragment,
            ) == M::embed(state)
            && base == M::storage(state);
    }

    /// Validate the separating composition with an actual borrowed observation.
    pub proof fn validate_with_observation(
        tracked &mut self,
        tracked other: &StorageObservation<M>,
    )
        requires
            old(self).loc() == other.loc(),
        ensures
            *final(self) == *old(self),
            completes::<M>(M::Fragment::op(final(self).fragment(), other.fragment())),
    {
        let (frame, base) = self.resource.validate_with_shared(other.resource);
        let state = choose|state: M::State| M::invariant(state)
            && M::Fragment::op(
                M::Fragment::op(self.fragment(), other.fragment()),
                frame.fragment,
            ) == M::embed(state)
            && base == M::storage(state);
    }

    /// Read-only references can overlap. Recover one invariant state with an
    /// independent completion frame for each borrowed fragment.
    pub proof fn compatible_with(tracked &self, tracked other: &Self)
        -> (out: (M::State, M::Fragment, M::Fragment))
        requires
            self.loc() == other.loc(),
        ensures
            M::invariant(out.0),
            M::Fragment::op(self.fragment(), out.1) == M::embed(out.0),
            M::Fragment::op(other.fragment(), out.2) == M::embed(out.0),
    {
        let tracked upper = self.resource.join_shared(&other.resource);
        let (frame, base) = upper.validate();
        let left = choose|left: Carrier<M>|
            Carrier::<M>::op(self.resource.value(), left) == upper.value();
        let right = choose|right: Carrier<M>|
            Carrier::<M>::op(other.resource.value(), right) == upper.value();
        let state = choose|state: M::State|
            M::invariant(state)
                && M::Fragment::op(upper.value().fragment, frame.fragment) == M::embed(state)
                && base == M::storage(state);
        M::Fragment::associative(self.fragment(), left.fragment, frame.fragment);
        M::Fragment::associative(other.fragment(), right.fragment, frame.fragment);
        (
            state,
            M::Fragment::op(left.fragment, frame.fragment),
            M::Fragment::op(right.fragment, frame.fragment),
        )
    }

    /// Proves `fact` from every completion compatible with both tokens.
    pub proof fn facts_2(tracked &self, tracked other: &Self, fact: bool)
        requires
            self.loc() == other.loc(),
            forall|left_frame: M::Fragment, right_frame: M::Fragment, state: M::State|
                M::invariant(state)
                    && M::Fragment::op(self.fragment(), left_frame) == M::embed(state)
                    && M::Fragment::op(other.fragment(), right_frame) == M::embed(state)
                    ==> fact,
        ensures
            fact,
    {
        let (state, left_frame, right_frame) = self.compatible_with(other);
    }

    /// Three potentially overlapping references have one compatible storage
    /// state, with a separate completion remainder for each reference.
    pub proof fn compatible_3(tracked &self, tracked second: &Self, tracked third: &Self)
        -> (out: (M::State, M::Fragment, M::Fragment, M::Fragment))
        requires
            self.loc() == second.loc(),
            self.loc() == third.loc(),
        ensures
            M::invariant(out.0),
            M::Fragment::op(self.fragment(), out.1) == M::embed(out.0),
            M::Fragment::op(second.fragment(), out.2) == M::embed(out.0),
            M::Fragment::op(third.fragment(), out.3) == M::embed(out.0),
    {
        let tracked first_two = self.resource.join_shared(&second.resource);
        let tracked upper = first_two.join_shared(&third.resource);
        let (frame, base) = upper.validate();
        let first_remainder = choose|remainder: Carrier<M>|
            Carrier::<M>::op(self.resource.value(), remainder) == first_two.value();
        let second_remainder = choose|remainder: Carrier<M>|
            Carrier::<M>::op(second.resource.value(), remainder) == first_two.value();
        let common_remainder = choose|remainder: Carrier<M>|
            Carrier::<M>::op(first_two.value(), remainder) == upper.value();
        let third_remainder = choose|remainder: Carrier<M>|
            Carrier::<M>::op(third.resource.value(), remainder) == upper.value();
        let state = choose|state: M::State|
            M::invariant(state)
                && M::Fragment::op(upper.value().fragment, frame.fragment) == M::embed(state)
                && base == M::storage(state);
        M::Fragment::associative(
            self.fragment(),
            first_remainder.fragment,
            common_remainder.fragment,
        );
        M::Fragment::associative(
            second.fragment(),
            second_remainder.fragment,
            common_remainder.fragment,
        );
        let first_remainder = M::Fragment::op(
            first_remainder.fragment,
            common_remainder.fragment,
        );
        let second_remainder = M::Fragment::op(
            second_remainder.fragment,
            common_remainder.fragment,
        );
        M::Fragment::associative(self.fragment(), first_remainder, frame.fragment);
        M::Fragment::associative(second.fragment(), second_remainder, frame.fragment);
        M::Fragment::associative(third.fragment(), third_remainder.fragment, frame.fragment);
        (
            state,
            M::Fragment::op(first_remainder, frame.fragment),
            M::Fragment::op(second_remainder, frame.fragment),
            M::Fragment::op(third_remainder.fragment, frame.fragment),
        )
    }

    /// Proves `fact` from every completion compatible with all three tokens.
    pub proof fn facts_3(tracked &self, tracked second: &Self, tracked third: &Self, fact: bool)
        requires
            self.loc() == second.loc(),
            self.loc() == third.loc(),
            forall|first_frame: M::Fragment, second_frame: M::Fragment,
                third_frame: M::Fragment, state: M::State|
                M::invariant(state)
                    && M::Fragment::op(self.fragment(), first_frame) == M::embed(state)
                    && M::Fragment::op(second.fragment(), second_frame) == M::embed(state)
                    && M::Fragment::op(third.fragment(), third_frame) == M::embed(state)
                    ==> fact,
        ensures
            fact,
    {
        let (state, first_frame, second_frame, third_frame) = self.compatible_3(second, third);
    }

    pub proof fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.fragment() == M::Fragment::op(self.fragment(), other.fragment()),
    {
        let tracked resource = StorageResource::join(self.resource, other.resource);
        Self { resource }
    }

    pub proof fn split(tracked self, left: M::Fragment, right: M::Fragment)
        -> (tracked out: (Self, Self))
        requires
            self.fragment() == M::Fragment::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.fragment() == left,
            out.1.fragment() == right,
    {
        let tracked (left, right) = self.resource.split(
            carrier_of::<M>(left),
            carrier_of::<M>(right),
        );
        (Self { resource: left }, Self { resource: right })
    }

    pub proof fn exchange(
        tracked self,
        tracked deposit: IMap<M::Key, M::Value>,
        new: M::Fragment,
        withdraw: IMap<M::Key, M::Value>,
    ) -> (tracked out: (Self, IMap<M::Key, M::Value>))
        requires
            frame_exchange::<M>(self.fragment(), deposit, new, withdraw),
        ensures
            out.0.loc() == self.loc(),
            out.0.fragment() == new,
            out.1 == withdraw,
    {
        frame_exchange_sound::<M>(self.fragment(), deposit, new, withdraw);
        let tracked (resource, base) = StorageResource::exchange(
            self.resource,
            deposit,
            carrier_of::<M>(new),
            withdraw,
        );
        (Self { resource }, base)
    }

    pub proof fn exchange_with_shared(
        tracked self,
        tracked other: &Self,
        tracked deposit: IMap<M::Key, M::Value>,
        new: M::Fragment,
        withdraw: IMap<M::Key, M::Value>,
    ) -> (tracked out: (Self, IMap<M::Key, M::Value>))
        requires
            self.loc() == other.loc(),
            frame_exchange::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                deposit,
                M::Fragment::op(new, other.fragment()),
                withdraw,
            ),
        ensures
            out.0.loc() == self.loc(),
            out.0.fragment() == new,
            out.1 == withdraw,
    {
        frame_exchange_sound::<M>(
            M::Fragment::op(self.fragment(), other.fragment()),
            deposit,
            M::Fragment::op(new, other.fragment()),
            withdraw,
        );
        let tracked (resource, base) = StorageResource::exchange_with_shared(
            self.resource,
            &other.resource,
            deposit,
            carrier_of::<M>(new),
            withdraw,
        );
        (Self { resource }, base)
    }

    pub proof fn exchange_nondeterministic(
        tracked self,
        tracked deposit: IMap<M::Key, M::Value>,
        outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
    ) -> (tracked out: (Self, IMap<M::Key, M::Value>))
        requires
            frame_exchange_nondeterministic::<M>(self.fragment(), deposit, outputs),
        ensures
            out.0.loc() == self.loc(),
            outputs.contains((out.0.fragment(), out.1)),
    {
        frame_exchange_nondeterministic_sound::<M>(self.fragment(), deposit, outputs);
        let wrapped = ISet::new(
            |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
                outputs.contains((pair.0.fragment, pair.1)),
        );
        let tracked (resource, base) = StorageResource::exchange_nondeterministic(
            self.resource,
            deposit,
            wrapped,
        );
        (Self { resource }, base)
    }

    pub proof fn exchange_nondeterministic_with_shared(
        tracked self,
        tracked other: &Self,
        tracked deposit: IMap<M::Key, M::Value>,
        outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
    ) -> (tracked out: (Self, IMap<M::Key, M::Value>))
        requires
            self.loc() == other.loc(),
            frame_exchange_nondeterministic::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                deposit,
                outputs.map(|pair: (M::Fragment, IMap<M::Key, M::Value>)|
                    (M::Fragment::op(pair.0, other.fragment()), pair.1)),
            ),
        ensures
            out.0.loc() == self.loc(),
            outputs.contains((out.0.fragment(), out.1)),
    {
        frame_exchange_nondeterministic_shared_sound::<M>(
            self.fragment(), other.fragment(), deposit, outputs,
        );
        let wrapped = ISet::new(
            |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
                outputs.contains((pair.0.fragment, pair.1)),
        );
        let tracked (resource, base) = StorageResource::exchange_nondeterministic_with_shared(
            self.resource, &other.resource, deposit, wrapped,
        );
        (Self { resource }, base)
    }

    /// The result's lifetime is tied to the borrowed token, permitting guards
    /// to survive operations on other fragments at the same protocol location.
    pub proof fn guard(tracked &self, guarded: IMap<M::Key, M::Value>)
        -> (tracked out: &IMap<M::Key, M::Value>)
        requires
            frame_guard::<M>(self.fragment(), guarded),
        ensures
            *out == guarded,
    {
        frame_guard_sound::<M>(self.fragment(), guarded);
        StorageResource::guard(&self.resource, guarded)
    }

    /// Proves `fact` from every completion of the token.
    pub proof fn facts(tracked &self, fact: bool)
        requires
            forall|frame: M::Fragment, state: M::State|
                M::invariant(state)
                    && M::Fragment::op(self.fragment(), frame) == M::embed(state) ==> fact,
        ensures
            fact,
    {
        self.validate();
    }
}

/// A read of an actual storage-protocol resource, tied to its owner's lifetime.
#[verifier::accept_recursive_types(M)]
pub tracked struct StorageObservation<'a, M: StorageMachine> {
    resource: &'a StorageResource<M::Key, M::Value, Carrier<M>>,
}

impl<'a, M: StorageMachine> StorageObservation<'a, M> {
    pub closed spec fn loc(self) -> Loc {
        self.resource.loc()
    }

    pub closed spec fn fragment(self) -> M::Fragment {
        self.resource.value().fragment
    }

    /// Each input is included separately; overlapping reads are not added.
    pub proof fn join(tracked &self, tracked other: &Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            fragment_included::<M>(self.fragment(), out.fragment()),
            fragment_included::<M>(other.fragment(), out.fragment()),
    {
        let tracked upper = self.resource.join_shared(other.resource);
        let left = choose|frame: Carrier<M>|
            Carrier::<M>::op(self.resource.value(), frame) == upper.value();
        let right = choose|frame: Carrier<M>|
            Carrier::<M>::op(other.resource.value(), frame) == upper.value();
        assert(M::Fragment::op(self.fragment(), left.fragment) == upper.value().fragment);
        assert(M::Fragment::op(other.fragment(), right.fragment) == upper.value().fragment);
        StorageObservation { resource: upper }
    }

    pub proof fn validate(tracked &self)
        ensures
            completes::<M>(self.fragment()),
    {
        let (frame, base) = self.resource.validate();
        let state = choose|state: M::State|
            M::invariant(state) && M::Fragment::op(self.fragment(), frame.fragment) == M::embed(
                state,
            ) && base == M::storage(state);
    }

    /// Narrow the borrowed fragment without creating an owned capability.
    pub proof fn weaken(tracked &self, target: M::Fragment) -> (tracked out: Self)
        requires
            fragment_included::<M>(target, self.fragment()),
        ensures
            out.loc() == self.loc(),
            out.fragment() == target,
    {
        let frame = choose|frame: M::Fragment| M::Fragment::op(target, frame) == self.fragment();
        assert(Carrier::<M>::op(carrier_of::<M>(target), carrier_of::<M>(frame))
            == self.resource.value());
        let tracked resource = self.resource.weaken(carrier_of::<M>(target));
        StorageObservation { resource }
    }

    /// The guard refers to the same stored permission and retains its lifetime.
    pub proof fn guard(tracked &self, guarded: IMap<M::Key, M::Value>) -> (tracked out: &'a IMap<
        M::Key,
        M::Value,
    >)
        requires
            frame_guard::<M>(self.fragment(), guarded),
        ensures
            *out == guarded,
    {
        frame_guard_sound::<M>(self.fragment(), guarded);
        StorageResource::guard(self.resource, guarded)
    }
}

impl<M: StorageMachine> StorageTokenOf<M, M::Key, M::Value, M::Fragment> {
    pub proof fn observe<'a>(tracked &'a self) -> (tracked out: StorageObservation<'a, M>)
        ensures
            out.loc() == self.loc(),
            out.fragment() == self.fragment(),
    {
        StorageObservation { resource: &self.resource }
    }

    /// Exchange owned rights and physical permissions while retaining the read.
    pub proof fn exchange_with_observation(
        tracked self,
        tracked other: &StorageObservation<M>,
        tracked deposit: IMap<M::Key, M::Value>,
        new: M::Fragment,
        withdraw: IMap<M::Key, M::Value>,
    ) -> (tracked out: (Self, IMap<M::Key, M::Value>))
        requires
            self.loc() == other.loc(),
            frame_exchange::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                deposit,
                M::Fragment::op(new, other.fragment()),
                withdraw,
            ),
        ensures
            out.0.loc() == self.loc(),
            out.0.fragment() == new,
            out.1 == withdraw,
    {
        frame_exchange_sound::<M>(
            M::Fragment::op(self.fragment(), other.fragment()),
            deposit,
            M::Fragment::op(new, other.fragment()),
            withdraw,
        );
        let tracked (resource, base) = StorageResource::exchange_with_shared(
            self.resource,
            other.resource,
            deposit,
            carrier_of::<M>(new),
            withdraw,
        );
        (Self { resource }, base)
    }

    pub proof fn exchange_nondeterministic_with_observation(
        tracked self,
        tracked other: &StorageObservation<M>,
        tracked deposit: IMap<M::Key, M::Value>,
        outputs: ISet<(M::Fragment, IMap<M::Key, M::Value>)>,
    ) -> (tracked out: (Self, IMap<M::Key, M::Value>))
        requires
            self.loc() == other.loc(),
            frame_exchange_nondeterministic::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                deposit,
                outputs.map(
                    |pair: (M::Fragment, IMap<M::Key, M::Value>)|
                        (M::Fragment::op(pair.0, other.fragment()), pair.1),
                ),
            ),
        ensures
            out.0.loc() == self.loc(),
            outputs.contains((out.0.fragment(), out.1)),
    {
        frame_exchange_nondeterministic_shared_sound::<M>(
            self.fragment(),
            other.fragment(),
            deposit,
            outputs,
        );
        let wrapped = ISet::new(
            |pair: (Carrier<M>, IMap<M::Key, M::Value>)|
                outputs.contains((pair.0.fragment, pair.1)),
        );
        let tracked (resource, base) = StorageResource::exchange_nondeterministic_with_shared(
            self.resource,
            other.resource,
            deposit,
            wrapped,
        );
        (Self { resource }, base)
    }
}

} // verus!
