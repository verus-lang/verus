use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;

verified_state_machine_model! { Example {
    fields {
        pub x: nat,
    }

    pub enum InitLabel
    {
        B { b: nat }
    }

    init!{
        g(l: InitLabel) {
            init x = l->b;
        }
    }
}}

fn main() {}
