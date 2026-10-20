//! Raw backend statement forms: several deposits, withdrawals and guards of one
//! `storage_map` field on one path, bindings after deposits at other keys, and
//! general-form deposits. Each path performs one storage exchange whose deposit
//! (withdrawal) is the union of its deposits (withdrawals).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

pub struct Tok {
    pub v: int,
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Slots {
        fields {
            #[sharding(variable)] pub auth: Map<nat, Tok>,
            #[sharding(storage_map)] pub stored: Map<nat, Tok>,
        }
        #[invariant] pub fn same(&self) -> bool { self.auth == self.stored }
        init! { initialize() { init auth = Map::empty(); init stored = Map::empty(); } }
        transition! { put_two(a: Tok, b: Tok) {
            require(!pre.auth.contains_key(1nat) && !pre.auth.contains_key(2nat));
            deposit stored += [1nat => a];
            deposit stored += [2nat => b] by { };
            update auth = pre.auth.insert(1nat, a).insert(2nat, b);
        } }
        transition! { take_two(a: Tok, b: Tok) {
            require(pre.auth.contains_key(1nat) && pre.auth[1nat] == a);
            require(pre.auth.contains_key(2nat) && pre.auth[2nat] == b);
            withdraw stored -= [1nat => a];
            withdraw stored -= [2nat => b];
            update auth = pre.auth.remove(1nat).remove(2nat);
        } }
        // Deposit, withdraw, deposit: one exchange at distinct keys.
        transition! { rotate(a: Tok, b: Tok) {
            require(pre.auth.contains_key(1nat) && pre.auth[1nat] == a);
            require(!pre.auth.contains_key(3nat) && !pre.auth.contains_key(4nat));
            deposit stored += [3nat => b];
            withdraw stored -= [1nat => a];
            deposit stored += [4nat => a];
            update auth = pre.auth.insert(3nat, b).remove(1nat).insert(4nat, a);
        } }
        // A withdrawal binding after a deposit at a different key.
        transition! { move_slot(a: Tok) {
            require(!pre.auth.contains_key(1nat) && pre.auth.contains_key(2nat));
            deposit stored += [1nat => a];
            withdraw stored -= [2nat => let _old];
            update auth = pre.auth.insert(1nat, a).remove(2nat);
        } }
        transition! { put_many(m1: Map<nat, Tok>, m2: Map<nat, Tok>) {
            require(m1.dom().disjoint(m2.dom()));
            require(pre.auth.dom().disjoint(m1.dom()) && pre.auth.dom().disjoint(m2.dom()));
            deposit stored += (m1);
            deposit stored += (m2);
            update auth = pre.auth.union_prefer_right(m1).union_prefer_right(m2);
        } }
        property! { two(a: Tok, b: Tok) {
            require(pre.auth.contains_key(1nat) && pre.auth[1nat] == a);
            require(pre.auth.contains_key(2nat) && pre.auth[2nat] == b);
            guard stored >= [1nat => a];
            guard stored >= [2nat => b];
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(put_two)] fn put_two_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
        #[inductive(take_two)] fn take_two_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
        #[inductive(rotate)] fn rotate_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
        #[inductive(move_slot)] fn move_slot_inductive(pre: Self, post: Self, a: Tok) {}
        #[inductive(put_many)] fn put_many_inductive(
            pre: Self, post: Self, m1: Map<nat, Tok>, m2: Map<nat, Tok>) {}
    }
}

pub open spec fn auth_of(f: Slots::Fragment) -> Map<nat, Tok> {
    f.auth->Some_0->Exclusive_0
}

/// The storage of `Slots`: one `IMap<__StorageKey, __StorageValue>`, with the
/// `stored` entry at `k` under `__StorageKey::stored(k)`.
pub type Storage = IMap<Slots::__StorageKey, Slots::__StorageValue>;

pub open spec fn at(k: nat) -> Slots::__StorageKey {
    Slots::__StorageKey::stored(k)
}

pub open spec fn val(t: Tok) -> Slots::__StorageValue {
    Slots::__StorageValue::stored(t)
}

/// A whole-state token determines the completion, so the deposits are known.
proof fn deposits_known(f: Slots::Fragment, d: Storage, a: Tok, b: Tok)
    requires
        f.auth is Some && f.auth->Some_0 is Exclusive,
        !auth_of(f).contains_key(1nat) && !auth_of(f).contains_key(2nat),
        d == IMap::empty().insert(at(1nat), val(a)).insert(at(2nat), val(b)),
    ensures
        Slots::Protocol::put_two_requires(f, Slots::Fragment::unit(), d, a, b),
{
    assert forall|z: Slots::Fragment, pre: Slots::State|
        pre.invariant() && Slots::Fragment::op(Slots::Fragment::op(f, Slots::Fragment::unit()), z)
            == Slots::Protocol::embed(pre) implies Slots::State::put_two_enabled(pre, a, b)
        && d == Slots::State::put_two_deposited(pre, a, b)
        && Slots::State::put_two_owners_enabled(pre, f, Slots::Fragment::unit(), a, b) by {
        assert(Slots::State::put_two_deposited(pre, a, b) =~= d);
    }
}

proof fn rotate_ready(f: Slots::Fragment, d: Storage, a: Tok, b: Tok)
    requires
        f.auth is Some && f.auth->Some_0 is Exclusive,
        auth_of(f).contains_key(1nat) && auth_of(f)[1nat] == a,
        !auth_of(f).contains_key(3nat) && !auth_of(f).contains_key(4nat),
        d == IMap::empty().insert(at(3nat), val(b)).insert(at(4nat), val(a)),
    ensures
        Slots::Protocol::rotate_requires(f, Slots::Fragment::unit(), d, a, b),
{
    assert forall|z: Slots::Fragment, pre: Slots::State|
        pre.invariant() && Slots::Fragment::op(Slots::Fragment::op(f, Slots::Fragment::unit()), z)
            == Slots::Protocol::embed(pre) implies Slots::State::rotate_enabled(pre, a, b)
        && d == Slots::State::rotate_deposited(pre, a, b)
        && Slots::State::rotate_owners_enabled(pre, f, Slots::Fragment::unit(), a, b) by {
        assert(Slots::State::rotate_deposited(pre, a, b) =~= d);
    }
}

proof fn history(tracked a: Tok, tracked b: Tok, tracked c: Tok, tracked e: Tok)
    requires
        c == b,
        e == a,
{
    assert(IMap::<nat, Tok>::empty() =~= Map::<nat, Tok>::empty().to_imap());
    assert(Slots::__tag_stored(IMap::empty()) =~= IMap::empty());
    let tracked token = Slots::Protocol::initialize(IMap::tracked_empty());
    let tracked mut d: Storage = IMap::tracked_empty();
    d.tracked_insert(at(1nat), Slots::__StorageValue::stored(a));
    d.tracked_insert(at(2nat), Slots::__StorageValue::stored(b));
    deposits_known(token.fragment(), d, a, b);
    let tracked token = Slots::Protocol::put_two(token, d, a, b);
    let tracked both = Slots::Protocol::two(&token, a, b);
    assert(both.contains_key(at(1nat)) && both[at(1nat)] == val(a));
    let tracked (token, mut w) = Slots::Protocol::take_two(token, a, b);
    let tracked a = Slots::__unwrap_stored(w.tracked_remove(at(1nat)));
    let tracked b = Slots::__unwrap_stored(w.tracked_remove(at(2nat)));
    let tracked mut d: Storage = IMap::tracked_empty();
    d.tracked_insert(at(1nat), Slots::__StorageValue::stored(a));
    d.tracked_insert(at(2nat), Slots::__StorageValue::stored(b));
    deposits_known(token.fragment(), d, a, b);
    let tracked token = Slots::Protocol::put_two(token, d, a, b);
    // Withdraw slot 1 while depositing slots 3 and 4 in the same exchange.
    let tracked mut d: Storage = IMap::tracked_empty();
    d.tracked_insert(at(3nat), Slots::__StorageValue::stored(c));
    d.tracked_insert(at(4nat), Slots::__StorageValue::stored(e));
    rotate_ready(token.fragment(), d, a, b);
    let tracked (token, mut w) = Slots::Protocol::rotate(token, d, a, b);
    let tracked a2 = Slots::__unwrap_stored(w.tracked_remove(at(1nat)));
    assert(a2 == a);
    assert(auth_of(token.fragment()) =~= Map::empty().insert(2nat, b).insert(3nat, b).insert(4nat, a));
}

fn main() {}

} // verus!
