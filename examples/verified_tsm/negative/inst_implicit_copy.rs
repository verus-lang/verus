// EXPECTED-ERROR: use of moved value: `t`
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, pervasive::*, set::*};
verus! {

pub struct Y {}

} // verus!
verified_tokenized_state_machine! {  A {
    fields {
        #[sharding(variable)]
        pub x: IMap<int, Y>,
    }

    init!{
        initialize() {
            init x = IMap::<int, Y>::empty();
        }
    }
}}
verus! {

proof fn test(tracked t: A::Instance) -> (tracked r: (A::Instance, A::Instance)) {
    (t, t)
}

} // verus!
fn main() {}
