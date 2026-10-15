// EXPECTED-ERROR: Type test_type_recursion_fail_negative::X::State recursively uses type test_type_recursion_fail_negative::X::Instance in a non-positive position
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, pervasive::*, set::*};
verified_tokenized_state_machine! {  X {
    fields {
        // this should fail because IMap has a reject_recursive_types first param

        #[sharding(variable)]
        pub t: IMap<X::Instance, int>
    }
}}

fn main() {}
