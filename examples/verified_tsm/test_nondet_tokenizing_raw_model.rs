use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 Z {
    fields {
        #[sharding(variable)]
        pub v1: int,

        #[sharding(variable)]
        pub v2: int,

        #[sharding(not_tokenized)]
        pub nt: int,

        #[sharding(constant)]
        pub c: int,
    }

    init!{
        initialize() {
            init v1 = 0;
            init v2 = 1;
            init nt = 2;
            init c = 3;
        }
    }

    transition!{
        tr1() {
            update nt = pre.nt + 1; // this is ok because the exchange fn ignores this line
            update v1 = pre.v1 + 2;
        }
    }

    transition!{
        tr2() {
            // v1 should be passed in as tokens, v2 read nondeterministically
            birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
            update v1 = x;
        }
    }

    transition!{
        tr3() {
            // v1, v2 both passed in as tokens
            birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
            update v1 = x + 4 * pre.v2;
        }
    }
}}

fn main() {}
