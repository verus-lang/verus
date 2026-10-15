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
        #[sharding(map)]
        pub x: Map<int, Y>,
    }

    init!{
        initialize() {
            init x = Map::<int, Y>::empty();
        }
    }
}}
verus! {

proof fn test(tracked t: A::x) -> (tracked r: (A::x, A::x)) {
    (t, t)
}

} // verus!
fn main() {}
