//! Complete RequireLetExample and its equivalent operation from the guide.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  RequireLetExample {
    fields {
        #[sharding(variable)]
        pub x_opt: Option<int>,
    }

    init!{
        initialize(value: Option<int>) {
            init x_opt = value;
        }
    }

    transition!{
        add_1() {
            require let Some(x) = pre.x_opt;
            update x_opt = Some(x + 1);
        }
    }

    transition!{
        add_1_alternative() {
            require pre.x_opt is Some;
            let x = pre.x_opt->Some_0;
            update x_opt = Some(x + 1);
        }
    }
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut x_opt)) =
            RequireLetExample::Instance::initialize(Some(5));
        instance.add_1(&mut x_opt);
        assert(x_opt.value() == Some(6));
        instance.add_1_alternative(&mut x_opt);
        assert(x_opt.value() == Some(7));
    }
}

} // verus!
