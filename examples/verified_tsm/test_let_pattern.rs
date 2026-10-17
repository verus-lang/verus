#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, multiset::*, pervasive::*, set::*};

verified_tokenized_state_machine! {  X {
    fields { #[sharding(variable)] pub t: (int, int) }

    init!{
        initialize() {
            init t = (2, 2);
        }
    }

    transition!{
        tr() {
            let (a, b) = pre.t;
            update t = (a + 1, b + 1);
        }
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        self.t.0 == self.t.1
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(tr)]
    fn tr_inductive(pre: Self, post: Self) { }
}}
fn main() {}
