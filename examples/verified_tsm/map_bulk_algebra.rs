//! Bulk map operations preserve arbitrary frames, including infinite maps.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::*;
use vstd::resource::tsm_collections::*;
verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas};

pub struct Maps;

impl Machine for Maps {
    type State = IMap<int, int>;

    type Fragment = MapFragment<int, int>;

    open spec fn invariant(s: Self::State) -> bool {
        true
    }

    open spec fn embed(s: Self::State) -> Self::Fragment {
        map_frag(s)
    }
}

proof fn remove_infinite_owned_map() {
    let whole = IMap::new(|key: int| true, |key: int| key);
    let local = IMap::new(|key: int| key >= 0, |key: int| key);
    let remainder = IMap::new(|key: int| key < 0, |key: int| key);
    map_join(local, remainder);
    assert(local.union_prefer_right(remainder) =~= whole);
    let tracked token = Token::<Maps>::alloc_state(whole);
    let tracked (owner, rest) = token.split(map_frag(local), map_frag(remainder));
    let owned = owner.fragment();
    let next = map_remove_many(owned, local.dom());
    assert(frame_update::<Maps>(owned, next)) by {
        assert forall|frame: MapFragment<int, int>, state: IMap<int, int>|
            Maps::invariant(state) && MapFragment::op(owned, frame) == Maps::embed(
                state,
            ) implies exists|post: IMap<int, int>|
            Maps::invariant(post) && MapFragment::op(next, frame) == Maps::embed(post) by {
            map_remove_many_frame(owned, frame, state, local);
            let post = state.remove_keys(local.dom());
            assert(Maps::invariant(post));
            assert(MapFragment::op(next, frame) == Maps::embed(post));
        };
    }
    let tracked owner = owner.update(next);
    let tracked token = owner.join(rest);
    token.validate();
}

proof fn explicit_disjoint_addition() {
    let local = IMap::empty().insert(0int, 10int);
    let rest = IMap::empty().insert(1int, 11int);
    let added = IMap::new(|key: int| key >= 2, |key: int| key);
    map_join(local, rest);
    map_add_many_frame(map_frag(local), map_frag(rest), local.union_prefer_right(rest), added);
    map_have_many_frame(map_frag(local), map_frag(rest), local.union_prefer_right(rest), local);
}

pub struct PersistentMaps;

impl Machine for PersistentMaps {
    type State = IMap<int, int>;

    type Fragment = PersistentMapFragment<int, int>;

    open spec fn invariant(s: Self::State) -> bool {
        forall|key: int| s.contains_key(key) ==> #[trigger] s[key] == key
    }

    open spec fn embed(s: Self::State) -> Self::Fragment {
        persistent_map_frag(s)
    }
}

proof fn union_preserves_infinite_persistent_observation() {
    let initial = IMap::new(|key: int| key >= 0, |key: int| key);
    let added = IMap::new(|key: int| key < 0, |key: int| key);
    let tracked owner = Token::<PersistentMaps>::alloc_state(initial);
    persistent_map_idempotent(initial);
    let tracked observation = owner.duplicate();
    let old = owner.fragment();
    let next = PersistentMapFragment::op(old, persistent_map_frag(added));
    assert(frame_update::<PersistentMaps>(old, next)) by {
        assert forall|frame: PersistentMapFragment<int, int>, state: IMap<int, int>|
            PersistentMaps::invariant(state) && PersistentMapFragment::op(old, frame)
                == PersistentMaps::embed(state) implies exists|post: IMap<int, int>|
            PersistentMaps::invariant(post) && PersistentMapFragment::op(next, frame)
                == PersistentMaps::embed(post) by {
            persistent_map_union_frame(old, frame, state, added);
            let post = state.union_prefer_right(added);
            assert(PersistentMaps::invariant(post)) by {
                assert forall|key: int| post.contains_key(key) implies post[key] == key by {};
            }
            assert(PersistentMapFragment::op(next, frame) == PersistentMaps::embed(post));
        };
    }
    let tracked owner = owner.update(next);
    assert(observation.fragment() == persistent_map_frag(initial));
    let tracked token = owner.join(observation);
    token.validate();
}

proof fn empty_and_infinite_observations() {
    let all = IMap::new(|key: int| key >= 0, |key: int| key);
    let observed = IMap::new(|key: int| key >= 5, |key: int| key);
    map_frag(all).op_unit();
    map_remove_many_frame(map_frag(all), MapFragment::unit(), all, IMap::<int, int>::empty());
    map_add_many_frame(map_frag(all), MapFragment::unit(), all, IMap::<int, int>::empty());
    persistent_map_frag(all).op_unit();
    persistent_map_have_many_frame(
        persistent_map_frag(all),
        PersistentMapFragment::unit(),
        all,
        observed,
    );
}

fn main() {
    proof {
        remove_infinite_owned_map();
        union_preserves_infinite_persistent_observation();
    }
}

} // verus!
