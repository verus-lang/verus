//! Mathematical tests for the pointwise collection algebra.
//! The map protocol combines local key ownership with an exclusive allocation
//! boundary, as in `state_machines/maps.rs`. Executable map clients use the macro.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::product::ProductRA;
use vstd::resource::tsm::*;
use vstd::resource::tsm_collections::*;

verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas};

pub ghost struct State {
    pub next: int,
    pub map: IMap<int, int>,
}

type Fragment = ProductRA<Option<ExclusiveRA<int>>, MapFragment<int, int>>;

pub struct Entries;

impl Machine for Entries {
    type State = State;

    type Fragment = Fragment;

    open spec fn invariant(state: State) -> bool {
        state.next >= 0 && (forall|key: int| #[trigger]
            state.map.dom().contains(key) ==> 0 <= key < state.next && state.map[key] >= 0)
    }

    open spec fn embed(state: State) -> Fragment {
        fragment(Some(state.next), state.map)
    }
}

pub open spec fn fragment(next: Option<int>, map: IMap<int, int>) -> Fragment {
    ProductRA {
        left: match next {
            None => None,
            Some(next) => Some(ExclusiveRA::Exclusive(next)),
        },
        right: map_frag(map),
    }
}

/// Updating and removing a key preserves another owner's key. Inserting a new
/// key uses the exclusive allocation boundary to prove absence in every frame.
proof fn exclusive_map_fragments() {
    let first_map = IMap::empty().insert(0, 4);
    let second_map = IMap::empty().insert(1, 6);
    let whole_map = first_map.union_prefer_right(second_map);
    let state = State { next: 2, map: whole_map };
    let tracked all = Token::<Entries>::alloc_state(state);
    map_join(first_map, second_map);
    let tracked (first, second) = all.split(
        fragment(Some(2), first_map),
        fragment(None, second_map),
    );
    let old_fragment = first.fragment();
    let new_fragment = ProductRA {
        left: old_fragment.left,
        right: replace_at(old_fragment.right, 0, Some(ExclusiveRA::Exclusive(5))),
    };
    assert(frame_update::<Entries>(old_fragment, new_fragment)) by {
        assert forall|frame: Fragment, state: State|
            Entries::invariant(state) && Fragment::op(old_fragment, frame) == Entries::embed(
                state,
            ) implies exists|next: State|
            Entries::invariant(next) && Fragment::op(new_fragment, frame) == Entries::embed(
                next,
            ) by {
            map_replace_frame(old_fragment.right, frame.right, state.map, 0, 4, 5);
            let next = State { next: state.next, map: state.map.insert(0, 5) };
            assert(Entries::invariant(next));
            assert(Fragment::op(new_fragment, frame) == Entries::embed(next));
        }
    };
    let tracked first = first.update(new_fragment);
    assert(first.fragment().right.at(0) == Some(ExclusiveRA::Exclusive(5)));
    assert(second.fragment().right.at(1) == Some(ExclusiveRA::Exclusive(6)));

    let old_fragment = first.fragment();
    let removed_fragment = ProductRA {
        left: old_fragment.left,
        right: replace_at(old_fragment.right, 0, None),
    };
    assert(frame_update::<Entries>(old_fragment, removed_fragment)) by {
        assert forall|frame: Fragment, state: State|
            Entries::invariant(state) && Fragment::op(old_fragment, frame) == Entries::embed(
                state,
            ) implies exists|next: State|
            Entries::invariant(next) && Fragment::op(removed_fragment, frame) == Entries::embed(
                next,
            ) by {
            map_remove_frame(old_fragment.right, frame.right, state.map, 0, 5);
            let next = State { next: state.next, map: state.map.remove(0) };
            assert(Entries::invariant(next));
            assert(Fragment::op(removed_fragment, frame) == Entries::embed(next));
        }
    };
    let tracked first = first.update(removed_fragment);
    assert(first.fragment().right.at(0) is None);

    let old_fragment = first.fragment();
    let inserted_fragment = ProductRA {
        left: Some(ExclusiveRA::Exclusive(3int)),
        right: replace_at(old_fragment.right, 2, Some(ExclusiveRA::Exclusive(8))),
    };
    assert(frame_update::<Entries>(old_fragment, inserted_fragment)) by {
        assert forall|frame: Fragment, state: State|
            Entries::invariant(state) && Fragment::op(old_fragment, frame) == Entries::embed(
                state,
            ) implies exists|next: State|
            Entries::invariant(next) && Fragment::op(inserted_fragment, frame) == Entries::embed(
                next,
            ) by {
            assert(state.next == 2);
            assert(frame.left is None);
            assert(!state.map.dom().contains(2));
            map_add_frame(old_fragment.right, frame.right, state.map, 2, 8);
            let next = State { next: 3, map: state.map.insert(2, 8) };
            assert(Entries::invariant(next));
            assert(Fragment::op(inserted_fragment, frame) == Entries::embed(next));
        }
    };
    let tracked first = first.update(inserted_fragment);
    let tracked combined = first.join(second);
    assert(combined.fragment().right.at(1) == Some(ExclusiveRA::Exclusive(6)));
    assert(combined.fragment().right.at(2) == Some(ExclusiveRA::Exclusive(8)));
    combined.validate();
}

pub struct PersistentEntries;

impl Machine for PersistentEntries {
    type State = IMap<int, int>;

    type Fragment = PersistentMapFragment<int, int>;

    open spec fn invariant(state: IMap<int, int>) -> bool {
        true
    }

    open spec fn embed(state: IMap<int, int>) -> Self::Fragment {
        persistent_map_frag(state)
    }
}

proof fn persistent_map_fragments() {
    let map = IMap::empty().insert(0int, 4int);
    let tracked token = Token::<PersistentEntries>::alloc_state(map);
    persistent_map_idempotent(map);
    let tracked copy = token.duplicate();
    assert(copy.loc() == token.loc());
    assert(copy.fragment().at(0) == Some(vstd::resource::agree::AgreementRA::Agree(4)));
    let tracked both = token.join(copy);
    assert(both.fragment() == persistent_map_frag(map));
}

fn main() {
}

} // verus!
