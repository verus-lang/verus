#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, pervasive::*, set::*};
verified_tokenized_state_machine! {  X {
    fields {
        #[sharding(variable)]
        pub r#context: X::Instance,
    }
}}

fn main() {}
