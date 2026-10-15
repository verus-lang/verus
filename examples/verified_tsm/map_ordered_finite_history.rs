//! Synthetic actual initialized coverage for originalX replacement+Have, unreachable from its fixed original initializer.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!(

    X {
        fields {
            #[sharding(map)]
            pub bool_map: Map<int, bool>,

        }

        init!{
            initialize(cond: bool) {
                init bool_map = Map::empty().insert(5, false).insert(19,false);
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
        let tracked observer = bool_map.remove(19);
        let tracked token = inst.add_have(5, token, &observer);
        assert(token.key() == 5 && token.value());
        assert(observer.key() == 19 && !observer.value());
    }
}

} // verus!
