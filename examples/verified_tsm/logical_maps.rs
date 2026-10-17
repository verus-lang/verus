//! Singleton map replacement keeps unrelated entry owners intact.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;

verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
Entries {
    fields {
        #[sharding(imap)] pub entries: IMap<int, bool>,
    }
    init! { initialize() {
        init entries = IMap::empty().insert(4int, true).insert(9int, false);
    } }
    transition! { replace(key: int, destination: int) {
        require key == destination;
        remove entries -= [key => let old];
        have entries >= [9int => false];
        add entries += [destination => !old];
    } }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(replace)] fn replace_inductive(pre: Self, post: Self, key: int, destination: int) {}
});

verified_tokenized_state_machine!(
    #[verified_raw_tokens]

    #[verifier::reject_recursive_types(K)]
    GenericEntries<K, V> {
        fields { #[sharding(imap)] pub entries: IMap<K, V>, }
        init! { initialize(entries: IMap<K, V>) { init entries = entries; } }
        transition! { remove(key: K) { remove entries -= [key => let value]; } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, entries: IMap<K, V>) {}
        #[inductive(remove)] fn remove_inductive(pre: Self, post: Self, key: K) {}
    }
);

pub proof fn allocate_entries() -> (tracked tokens: (Entries::Token, Entries::Token))
    ensures
        tokens.0.loc() == tokens.1.loc(),
        tokens.0.fragment().entries == map_frag(IMap::empty().insert(4int, true)),
        tokens.1.fragment().entries == map_frag(IMap::empty().insert(9int, false)),
{
    let tracked token = Entries::Protocol::initialize();
    let left = IMap::empty().insert(4int, true);
    let right = IMap::empty().insert(9int, false);
    map_join(left, right);
    assert(left.union_prefer_right(right) =~= IMap::empty().insert(4int, true).insert(9int, false));
    token.split(
        Entries::Fragment { entries: map_frag(left) },
        Entries::Fragment { entries: map_frag(right) },
    )
}

pub proof fn map_replacement_and_shared_observation() {
    let tracked (owner, observer) = allocate_entries();
    let old = owner.fragment();
    let h = observer.fragment();
    assert forall|z: Entries::Fragment, pre: Entries::State|
        pre.invariant() && Entries::Fragment::op(Entries::Fragment::op(old, h), z)
            == Entries::Protocol::embed(pre) implies Entries::State::replace_enabled(
        pre,
        4int,
        4int,
    ) && Entries::State::replace_owners_enabled(pre, old, h, 4int, 4int) by {
        let combined = Entries::Fragment::op(old, h);
        map_owned_frame(combined.entries, z.entries, pre.entries, 4int, true);
        map_owned_frame(combined.entries, z.entries, pre.entries, 9int, false);
    }
    let tracked owner = Entries::Protocol::replace_with_shared(owner, &observer, 4int, 4int);
    let (frame, pre, post) = choose|
        frame: Entries::Fragment,
        pre: Entries::State,
        post: Entries::State,
    |
        pre.invariant() && Entries::Fragment::op(Entries::Fragment::op(old, h), frame)
            == Entries::Protocol::embed(pre) && Entries::State::replace_strong(
            pre,
            post,
            4int,
            4int,
        ) && post.invariant() && owner.fragment() == Entries::Protocol::replace_owned_post(
            old,
            pre,
            post,
            4int,
            4int,
        ) && Entries::Fragment::op(Entries::Fragment::op(owner.fragment(), h), frame)
            == Entries::Protocol::embed(post);
    map_owned_frame(Entries::Fragment::op(old, h).entries, frame.entries, pre.entries, 4int, true);
    assert(owner.fragment().entries.at(4int) == Some(
        vstd::resource::exclusive::ExclusiveRA::Exclusive(false),
    ));
    assert(observer.fragment().entries == map_frag(IMap::empty().insert(9int, false)));
}

fn main() {
    proof {
        map_replacement_and_shared_observation();
    }
}

} // verus!
