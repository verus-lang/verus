use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::prelude::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
ActualTransfers {
    fields {
        #[sharding(variable)] pub phase:nat,
        #[sharding(storage_option)] pub first:Option<PointsTo<u64>>,
        #[sharding(storage_map)] pub second:Map<nat,PointsTo<bool>>,
    }
    init!{initialize(){init phase=0;init first=None;init second=Map::empty();}}
    #[invariant] pub fn shape(&self)->bool {self.phase==0}
    #[inductive(initialize)] fn initialize_inductive(post:Self){}
}}
verus! {

fn main() {
    let (a, Tracked(pa)) = PCell::new(17u64);
    let (b, Tracked(pb)) = PCell::new(true);
    proof {
        broadcast use {
            vstd::map::group_map_lemmas,
            vstd::imap::group_imap_lemmas,
            vstd::set::group_set_lemmas,
            vstd::iset::group_iset_lemmas,
        };

    }
    let tracked mut native = Map::<nat, PointsTo<bool>>::tracked_empty();
    proof {
        native.tracked_insert(4nat, pb);
    }
    let tracked tagged_first = ActualTransfers::__pack_first(Some(pa));
    let tracked tagged_second = ActualTransfers::__pack_second(native);
    proof {
        assert(tagged_first.dom().disjoint(tagged_second.dom()));
        assert(tagged_first == ActualTransfers::__tag_first(
            ActualTransfers::__untag_first(tagged_first),
        ));
        assert(tagged_second == ActualTransfers::__tag_second(
            ActualTransfers::__untag_second(tagged_second),
        ));
        assert(tagged_second.dom().finite());
    }
    let tracked p_ref = ActualTransfers::__borrow_first(&tagged_first);
    let tracked q_ref = ActualTransfers::__borrow_second(&tagged_second, 4nat);
    let tracked p_ref = vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(p_ref);
    let av = a.borrow(Tracked(p_ref));
    let tracked q_ref = vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(q_ref);
    let bv = b.borrow(Tracked(q_ref));
    assert(*av == 17u64);
    assert(*bv);
    let tracked pa = ActualTransfers::__unpack_first(tagged_first);
    let tracked mut native = ActualTransfers::__unpack_second(tagged_second);
    let tracked pb = native.tracked_remove(4nat);
    let tracked pa = vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(pa);
    let av = a.into_inner(Tracked(pa));
    let bv = b.into_inner(Tracked(pb));
    assert(av == 17u64);
    assert(bv);
}

} // verus!
