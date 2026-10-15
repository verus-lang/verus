//! Checked set ownership and monotone persistent observations.
//! These are algebra milestones for the generated collection strategies.
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::product::ProductRA;
use vstd::resource::tsm::*;
use vstd::resource::tsm_collections::*;

verus! {

broadcast use {vstd::iset::group_iset_lemmas, vstd::imap::group_imap_lemmas};

pub struct Sets;

type SetResources = ProductRA<SetFragment<int>, PersistentSetFragment<int>>;

impl Machine for Sets {
    type State = (ISet<int>, ISet<int>);

    type Fragment = SetResources;

    open spec fn invariant(state: Self::State) -> bool {
        true
    }

    open spec fn embed(state: Self::State) -> SetResources {
        ProductRA { left: set_frag(state.0), right: persistent_set_frag(state.1) }
    }
}

proof fn exclusive_and_persistent_sets() {
    let local_set = ISet::empty().insert(0int);
    let frame_set = ISet::empty().insert(2int);
    let observations = ISet::empty().insert(1int);
    let tracked all = Token::<Sets>::alloc_state((local_set.union(frame_set), observations));
    set_join(local_set, frame_set);
    persistent_set_idempotent(observations);
    let local = SetResources {
        left: set_frag(local_set),
        right: persistent_set_frag(observations),
    };
    let rest = SetResources { left: set_frag(frame_set), right: persistent_set_frag(observations) };
    let tracked (local, rest) = all.split(local, rest);
    let old = local.fragment();
    let next = SetResources {
        left: replace_at(old.left, 0int, None),
        right: PersistentSetFragment::op(old.right, persistent_set_frag(local_set)),
    };
    assert(frame_update::<Sets>(old, next)) by {
        assert forall|frame: SetResources, state: (ISet<int>, ISet<int>)|
            Sets::invariant(state) && SetResources::op(old, frame) == Sets::embed(
                state,
            ) implies exists|post: (ISet<int>, ISet<int>)|
            Sets::invariant(post) && SetResources::op(next, frame) == Sets::embed(post) by {
            set_remove_frame(old.left, frame.left, state.0, 0int);
            persistent_set_union_frame(old.right, frame.right, state.1, local_set);
            let post = (state.0.remove(0int), state.1.union(local_set));
            assert(SetResources::op(next, frame) == Sets::embed(post));
        };
    };
    let tracked local = local.update(next);
    assert(local.fragment().left.at(0) is None);
    assert(local.fragment().right.at(0) == Some(AgreementRA::Agree(())));
    assert(rest.fragment().left.at(2) == Some(ExclusiveRA::Exclusive(())));
    assert(rest.fragment().right.at(1) == Some(AgreementRA::Agree(())));
    let tracked both = local.join(rest);
    both.validate();
}

pub struct PersistentSets;

impl Machine for PersistentSets {
    type State = ISet<int>;

    type Fragment = PersistentSetFragment<int>;

    open spec fn invariant(state: ISet<int>) -> bool {
        true
    }

    open spec fn embed(state: ISet<int>) -> Self::Fragment {
        persistent_set_frag(state)
    }
}

proof fn infinite_persistent_set() {
    let set = ISet::new(|value: int| value >= 0);
    let tracked owner = Token::<PersistentSets>::alloc_state(set);
    persistent_set_idempotent(set);
    let tracked copy = owner.duplicate();
    let before = owner.fragment();
    let added = ISet::empty().insert(-1int);
    let after = PersistentSetFragment::op(before, persistent_set_frag(added));
    assert(frame_update::<PersistentSets>(before, after)) by {
        assert forall|frame: PersistentSetFragment<int>, state: ISet<int>|
            PersistentSets::invariant(state) && PersistentSetFragment::op(before, frame)
                == PersistentSets::embed(state) implies exists|post: ISet<int>|
            PersistentSets::invariant(post) && PersistentSetFragment::op(after, frame)
                == PersistentSets::embed(post) by {
            persistent_set_union_frame(before, frame, state, added);
            assert(PersistentSetFragment::op(after, frame) == PersistentSets::embed(
                state.union(added),
            ));
        };
    };
    let tracked owner = owner.update(after);
    assert(owner.fragment().at(-1) == Some(AgreementRA::Agree(())));
    assert(copy.fragment().at(10) == Some(AgreementRA::Agree(())));
    assert(copy.fragment().at(-1) is None);
    let tracked both = owner.join(copy);
    both.validate();
}

pub struct PersistentMaps;

impl Machine for PersistentMaps {
    type State = IMap<int, int>;

    type Fragment = PersistentMapFragment<int, int>;

    open spec fn invariant(state: IMap<int, int>) -> bool {
        true
    }

    open spec fn embed(state: IMap<int, int>) -> Self::Fragment {
        persistent_map_frag(state)
    }
}

proof fn persistent_map_observation() {
    let map = IMap::empty().insert(0int, 4int);
    let tracked token = Token::<PersistentMaps>::alloc_state(map);
    persistent_map_idempotent(map);
    let tracked copy = token.duplicate();
    let old = token.fragment();
    let new = replace_at(old, 0int, Some(AgreementRA::Agree(4int)));
    assert(frame_update::<PersistentMaps>(old, new)) by {
        assert forall|frame: PersistentMapFragment<int, int>, state: IMap<int, int>|
            PersistentMaps::invariant(state) && PersistentMapFragment::op(old, frame)
                == PersistentMaps::embed(state) implies exists|post: IMap<int, int>|
            PersistentMaps::invariant(post) && PersistentMapFragment::op(new, frame)
                == PersistentMaps::embed(post) by {
            persistent_map_owned_frame(old, frame, state, 0int, 4int);
            persistent_map_insert_frame(old, frame, state, 0int, 4int);
            assert(PersistentMapFragment::op(new, frame) == PersistentMaps::embed(
                state.insert(0int, 4int),
            ));
        };
    };
    let tracked token = token.update(new);
    assert(copy.fragment().at(0) == Some(AgreementRA::Agree(4)));
    let tracked combined = token.join(copy);
    combined.validate();
}

fn main() {
}

} // verus!
