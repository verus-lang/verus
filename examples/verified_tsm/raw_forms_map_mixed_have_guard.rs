// Regression (4e0ca49ec): guards after several haves of one map field, on the raw
// interface (see generic_tokens_map_mixed_have_guard.rs).
//! A property that borrows a general operand and a singleton of one `map`
//! field, and also guards storage.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::exclusive::ExclusiveRA;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Mixed {
        fields {
            #[sharding(map)] pub owners: Map<nat, u64>,
            #[sharding(storage_map)] pub store: Map<nat, u64>,
        }
        #[invariant] pub fn same(&self) -> bool { self.owners == self.store }
        init! { initialize(m: Map<nat, u64>) { init owners = m; init store = m; } }
        property! { peek(m: Map<nat, u64>, k: nat, v: u64) {
            have owners >= (m);
            have owners >= [k => v];
            guard store >= [k => v];
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, m: Map<nat, u64>) {}
    }
}

// Two singletons of one `map` field, and guards of both keys.
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    TwoSingletons {
        fields {
            #[sharding(map)] pub owners: Map<nat, u64>,
            #[sharding(storage_map)] pub store: Map<nat, u64>,
        }
        #[invariant] pub fn same(&self) -> bool { self.owners == self.store }
        init! { initialize(m: Map<nat, u64>) { init owners = m; init store = m; } }
        property! { peek(j: nat, w: u64, k: nat, v: u64) {
            have owners >= [j => w];
            have owners >= [k => v];
            guard store >= [j => w];
            guard store >= [k => v];
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, m: Map<nat, u64>) {}
    }
}

/// A fragment that embeds a whole state owns every entry of `owners`.
proof fn peek_ready(f: Mixed::Fragment, s: Mixed::State, m: Map<nat, u64>, k: nat, v: u64)
    requires
        f == Mixed::Protocol::embed(s),
        m.submap_of(s.owners),
        s.owners.contains_pair(k, v),
    ensures
        Mixed::Protocol::peek_requires(f, m, k, v),
{
    assert forall|z: Mixed::Fragment, pre: Mixed::State|
        pre.invariant() && Mixed::Fragment::op(f, z) == Mixed::Protocol::embed(pre) implies
        Mixed::State::peek_owners_enabled(pre, f, Mixed::Fragment::unit(), m, k, v)
        && Mixed::State::peek_enabled(pre, m, k, v) by {
        f.op_unit();
        assert forall|key: nat| s.owners.contains_key(key) implies
            pre.owners.contains_pair(key, s.owners[key]) by {
            vstd::resource::tsm_collections::map_owned_frame(
                f.owners, z.owners, pre.owners.to_imap(), key, s.owners[key]);
        }
        assert forall|key: nat| #[trigger] m.dom().contains(key) implies
            pre.owners.contains_pair(key, m[key]) by {
            assert(s.owners.contains_key(key));
        }
        assert(m.submap_of(pre.owners));
        assert forall|key: nat| #[trigger] m.to_imap().contains_key(key) implies
            f.owners.at(key) == Some(ExclusiveRA::Exclusive(m.to_imap()[key])) by {
            assert(m.dom().contains(key) && s.owners.contains_key(key));
        }
        assert(f.owners.at(k) == Some(ExclusiveRA::Exclusive(v)));
    }
}

proof fn client(tracked a: u64, tracked b: u64)
    requires
        a == 10,
        b == 20,
{
    let m = Map::<nat, u64>::empty().insert(1nat, 10u64).insert(2nat, 20u64);
    let tracked mut base = Map::tracked_empty();
    base.tracked_insert(1nat, a);
    base.tracked_insert(2nat, b);
    assert(base =~= m);
    // The storage is one `IMap<__StorageKey, __StorageValue>`; `__pack_store`
    // tags a finite map of the `store` field.
    let tracked token = Mixed::Protocol::initialize(Mixed::__pack_store(base), m);
    let s = choose|s: Mixed::State|
        Mixed::State::initialize(s, m) && s.invariant()
        && token.fragment() == Mixed::Protocol::embed(s);
    // The general operand and the singleton overlap at key 2.
    peek_ready(token.fragment(), s, m, 2nat, 20u64);
    let tracked g = Mixed::Protocol::peek(&token, m, 2nat, 20u64);
    assert(g.contains_key(Mixed::__StorageKey::store(2nat)) && g[Mixed::__StorageKey::store(2nat)] == Mixed::__StorageValue::store(20));
    let e = Map::<nat, u64>::empty();
    peek_ready(token.fragment(), s, e, 1nat, 10u64);
    let tracked g = Mixed::Protocol::peek(&token, e, 1nat, 10u64);
    assert(g[Mixed::__StorageKey::store(1nat)] == Mixed::__StorageValue::store(10));
}

fn main() {}

} // verus!
