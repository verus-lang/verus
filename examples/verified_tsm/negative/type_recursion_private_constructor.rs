// EXPECTED-ERROR: cannot construct `X::Instance` with struct literal syntax due to private fields
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, pervasive::*, set::*};
verified_tokenized_state_machine! {  X {
    fields {
        #[sharding(variable)]
        pub t: X::Instance,
    }
}}

verus! {

proof fn cannot_forge(location: vstd::resource::Loc) {
    let tracked context = vstd::resource::tsm_context::Descriptor::alloc(location);
    let tracked forged = X::Instance { context };
}

} // verus!
fn main() {}
