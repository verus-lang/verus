// rust_verify/tests/example.rs ignore --- checked macro: Z3 warns "'=>' cannot be used in patterns" for a generated trigger (verifies otherwise)
//! Complete original X declarations and both checked transition APIs; initialized native history.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!(

    X {
        fields {
            #[sharding(imap)]
            pub bool_map: IMap<int, bool>,

        }

        init!{
            initialize(cond: bool) {
                init bool_map = IMap::empty().insert(5, true);
            }
        }

        transition!{
            add(n: int) {
                remove bool_map -= [n => true];
                add bool_map += [n => true];
            }
        }

        transition!{
            add_have(n: int) {
                remove bool_map -= [n => false];
                have bool_map >= [19 => false];
                add bool_map += [n => true];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, cond: bool) { }

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, n: int) { }

        #[inductive(add_have)]
        fn add_have_inductive(pre: Self, post: Self, n: int) { }
    }
);
verus! {

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut bool_map)) = X::Instance::initialize(false);
        let tracked token = bool_map.remove(5);
        let tracked token = inst.add(5, token);
        assert(token.key() == 5 && token.value());
    }
}

} // verus!
