use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;

verified_state_machine_model! { Example {
    fields {}

    pub enum Label
    {
        B { b: nat }
    }

    pub open spec fn test(t: Label) -> bool
        recommends t is B
    {
        t->b > 10
    }

    transition!{
        f(l: Label) {
            require l->b > 10;
        }
    }
}}

fn main() {}
