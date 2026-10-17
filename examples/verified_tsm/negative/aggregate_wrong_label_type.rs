use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;

verus! {

verified_state_machine_model!{ X<T, U> {
    fields {
        pub x: T,
        pub y: U,
    }
    pub type InitLabel<U> = Option<U>;
    pub type Label<T> = Option<T>;

    init!{
        g(l: InitLabel<U>, t: T, u: U) {
            init x = t;
            init y = u;
        }
    }
    transition!{
        f(l: Label<U>) {
        }
    }
}}

proof fn classify<T, U>(pre: X::State<T, U>, l: X::Label<T>, initial: X::InitLabel<U>) {
    X::show::g(pre, initial, pre.x, pre.y);
    X::show::f(pre, pre, l);
    assert(X::State::init(pre, initial));
    assert(X::State::next(pre, pre, l));
}

fn main() {
}

} // verus!
