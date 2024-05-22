#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::{pervasive::*, *};

// ANCHOR: main
state_machine! {
    X {
        fields {
            pub num_threads: nat,
            pub counter: int,
            pub unstamped_tickets: nat,
            pub stamped_tickets: nat,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == self.stamped_tickets
            && self.stamped_tickets + self.unstamped_tickets == self.num_threads
        }

        init!{
            initialize(num_threads: nat) {
                init num_threads = num_threads;
                init counter = 0;
                init unstamped_tickets = num_threads;
                init stamped_tickets = 0;
            }
        }

        transition!{
            tr_inc() {
                // Replace a single unstamped ticket with a stamped ticket
                require(pre.unstamped_tickets >= 1);
                update unstamped_tickets = (pre.unstamped_tickets - 1) as nat;
                update stamped_tickets = pre.stamped_tickets + 1;

                assert(pre.counter < pre.num_threads);
                update counter = pre.counter + 1;
            }
        }

        property!{
            finalize() {
                require(pre.stamped_tickets >= pre.num_threads);
                assert(pre.counter == pre.num_threads);
            }
        }
// ANCHOR_END: main

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, num_threads: nat) { }

        #[inductive(tr_inc)]
        fn tr_inc_preserves(pre: Self, post: Self) {
        }
    }
}

fn main() {}
