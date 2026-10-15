use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;

verus! {

verified_state_machine_model!{ X {
    fields {
        pub number: int,
    }
    init!{
        initialize() {
            init number = 0;
        }
    }
    transition!{
        add(n: int) {
            update number = pre.number + 2*n;
        }
    }
    transition!{
        sub(n: int) {
            update number = pre.number - 2*n;
        }
    }
}}

proof fn test(s: X::Step)
    requires
        s.is_add(),
{
    match s {
        X::Step::add(_) => assert(true),
        X::Step::sub(_) => assert(false),
        _ => {},
    }
}

proof fn classify_invalid() {
    let pre = X::State { number: 0int };
    let post = X::State { number: 5int };
    X::show::initialize(pre);
    X::show::add(pre, post, 2int);

}

fn main() {
}

} // verus!
