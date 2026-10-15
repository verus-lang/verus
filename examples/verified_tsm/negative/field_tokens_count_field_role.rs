// EXPECTED-ERROR: mismatched types
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {

    X {
        fields {
            #[sharding(count)]
            pub c: nat,
            #[sharding(count)]
            pub d: nat,
        }
        init! {
            initialize() {
                init c = 9;
                init d = 9;
            }
        }
    }
}

proof fn fields_with_identical_native_types_are_still_distinct(tracked token: X::d) {
    let tracked _c: X::c = token;
}

fn main() {
}

} // verus!
