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
verus! {

fn main() {
    proof {
        let label = Example::InitLabel::B { b: 11nat };
        let post = Example::take_step::g(label);
        assert(post.x == 11);
        assert(post.invariant());
        Example::show::g(post, label);
        assert(Example::State::init(post, label));
    }
}

} // verus!
