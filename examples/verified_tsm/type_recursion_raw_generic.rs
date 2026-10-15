#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, pervasive::*, set::*};
verified_tokenized_state_machine! {  X<r#marker> {
    fields {
        #[sharding(variable)]
        pub t: X::Instance<r#marker>,
    }
}}

fn main() {}
