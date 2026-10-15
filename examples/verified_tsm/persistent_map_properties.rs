//! Finite and infinite persistent maps support repeated, overlapping observations.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;
verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::map::group_map_lemmas};

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    PersistentMaps {
        fields {
            #[sharding(variable)] pub selected:nat,
            #[sharding(persistent_map)] pub finite:Map<nat,int>,
            #[sharding(persistent_imap)] pub infinite:IMap<nat,int>,
        }
        #[invariant] pub fn values_agree(&self)->bool {
            (forall|key:nat| self.finite.contains_key(key) ==> self.finite[key]==7int)
            &&(forall|key:nat| self.infinite.contains_key(key) ==> self.infinite[key]==7int)
        }
        init! { initialize() {
            init selected=0nat;
            init finite=Map::empty().insert(0nat,7int);
            init infinite=IMap::empty().insert(0nat,7int);
        } }
        transition! { record(key:nat) {
            add finite (union)= [key=>7int];
            add infinite (union)= [key=>7int];
        } }
        property! { compare(left:nat,left_value:int,right:nat,right_value:int) {
            have infinite >= [left=>left_value];
            have infinite >= [right=>right_value];
            assert left_value==right_value;
        } }
        property! { observe_selected() {
            have finite >= [pre.selected=>let value];
            assert value==7int;
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self) {}
        #[inductive(record)] fn record_inductive(pre:Self,post:Self,key:nat) {}
    }
}

pub proof fn persistent_observation_demo() {
    let tracked all = PersistentMaps::Protocol::initialize();
    let observations = PersistentMaps::Fragment {
        finite: persistent_map_frag(IMap::empty().insert(0nat, 7int)),
        infinite: persistent_map_frag(IMap::empty().insert(0nat, 7int)),
        ..PersistentMaps::Fragment::unit()
    };
    let selection = PersistentMaps::Fragment {
        selected: Some(ExclusiveRA::Exclusive(0nat)),
        ..PersistentMaps::Fragment::unit()
    };
    observations.finite.op_unit();
    observations.infinite.op_unit();
    assert(Map::<nat, int>::empty().insert(0nat, 7int).to_imap() =~= IMap::empty().insert(
        0nat,
        7int,
    ));
    Pointwise::extensionality(all.fragment().finite, observations.finite);
    let tracked (observations, selection) = all.split(observations, selection);
    persistent_map_idempotent(IMap::empty().insert(0nat, 7int));
    let tracked copy = observations.duplicate();
    assert(PersistentMaps::Protocol::compare_requires(
        copy.fragment(),
        observations.fragment(),
        0nat,
        7int,
        0nat,
        7int,
    )) by {
        assert forall|z: PersistentMaps::Fragment, pre: PersistentMaps::State|
            pre.invariant() && PersistentMaps::Fragment::op(
                PersistentMaps::Fragment::op(copy.fragment(), observations.fragment()),
                z,
            ) == PersistentMaps::Protocol::embed(
                pre,
            ) implies PersistentMaps::State::compare_enabled(pre, 0nat, 7int, 0nat, 7int)
            && PersistentMaps::State::compare_owners_enabled(
            pre,
            copy.fragment(),
            observations.fragment(),
            0nat,
            7int,
            0nat,
            7int,
        ) by {
            persistent_map_owned_frame(
                PersistentMaps::Fragment::op(copy.fragment(), observations.fragment()).infinite,
                z.infinite,
                pre.infinite,
                0nat,
                7int,
            );
        }
    }
    let tracked copy = PersistentMaps::Protocol::compare_with_shared(
        copy,
        &observations,
        0nat,
        7int,
        0nat,
        7int,
    );
    assert(PersistentMaps::Protocol::observe_selected_requires(
        copy.fragment(),
        selection.fragment(),
    )) by {
        assert forall|z: PersistentMaps::Fragment, pre: PersistentMaps::State|
            pre.invariant() && PersistentMaps::Fragment::op(
                PersistentMaps::Fragment::op(copy.fragment(), selection.fragment()),
                z,
            ) == PersistentMaps::Protocol::embed(
                pre,
            ) implies PersistentMaps::State::observe_selected_enabled(pre)
            && PersistentMaps::State::observe_selected_owners_enabled(
            pre,
            copy.fragment(),
            selection.fragment(),
        ) by {
            assert(pre.selected == 0nat);
            persistent_map_owned_frame(
                PersistentMaps::Fragment::op(copy.fragment(), selection.fragment()).finite,
                z.finite,
                pre.finite.to_imap(),
                0nat,
                7int,
            );
        }
    }
    let tracked copy = PersistentMaps::Protocol::observe_selected_with_shared(copy, &selection);
    assert(copy.fragment() == observations.fragment());
}

} // verus!
fn main() {}
