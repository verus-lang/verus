use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(persistent_set)]
        pub b: Set<int>,
    }

    init!{
        initialize() {
            init b = Set::<int>::empty().insert(19);
        }
    }

    transition!{
        tr_add() {
            add b (union)= set { 5 };
        }
    }

    transition!{
        tr_have() {
            have b >= set { 5 };
        }
    }

    transition!{
        tr_add_gen(values:Set<int>) {
            add b (union)= (values);
        }
    }

    transition!{
        tr_have_gen(values:Set<int>) {
            have b >= (values);
        }
    }
}}

verus! {

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::initialize();
        let tracked token_set = Y::b_collection::empty(inst.id());
        inst.tr_have_gen(Set::<int>::empty(), &token_set);
        let tracked returned = inst.tr_add_gen(Set::<int>::empty());
        assert(returned.set() == Set::<int>::empty());
        inst.tr_have_gen(Set::<int>::empty(), &returned);
        let tracked token1 = inst.tr_add();
        let tracked again = inst.tr_add();
        inst.tr_have(&token1);
        inst.tr_have(&again);
    }
}

} // verus!
