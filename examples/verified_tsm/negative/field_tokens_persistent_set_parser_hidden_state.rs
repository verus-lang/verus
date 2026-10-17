// EXPECTED-ERROR: set facade requires explicit native operands and assertions
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
            require pre.b.contains(19);
            add b (union)= set { 5 };
        }
    }

    transition!{
        tr_have() {
            have b >= set { 5 };
        }
    }

    transition!{
        tr_add_gen() {
            add b (union)= (Set::<int>::empty().insert(6));
        }
    }

    transition!{
        tr_have_gen() {
            have b >= (Set::<int>::empty().insert(6));
        }
    }
}}

fn main() {}
