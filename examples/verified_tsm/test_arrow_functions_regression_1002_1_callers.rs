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
verus! {

fn main() {
    proof {
        let pre = Example::State {  };
        let label = Example::Label::B { b: 11nat };
        assert(Example::State::test(label));
        let post = Example::take_step::f(pre, label);
        assert(Example::State::f_strong(pre, post, label));
        Example::show::f(pre, post, label);
        assert(Example::State::next(pre, post, label));
    }
}

} // verus!
