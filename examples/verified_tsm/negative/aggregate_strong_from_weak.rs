use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model! { X {
    fields { pub number: int, }
    init! { initialize(n: int) { init number = n; } }
    transition! { positive() { assert(pre.number > 0); update number = pre.number + 1; } }
    readonly! { observe(n: int) { require(pre.number == n); } }
}}

proof fn weak_is_not_strong() {
    let pre = X::State { number: 0int };
    let post = X::State { number: 91int };
    assert(X::State::positive(pre, post));
    X::show::positive(pre, post);
    assert(X::State::next(pre, post));
    reveal(X::State::next_strong_by);
    assert(!X::State::next_strong_by(pre, post, X::Step::positive()));
    assert(!X::State::next_strong_by(pre, post, X::Step::observe(0int)));
    assert(!X::State::next_strong_by(pre, post, X::Step::dummy_to_use_type_params(pre)));
    reveal(X::State::next_strong);
    assert(X::State::next_strong(pre, post));
}

proof fn readonly_and_dummy() {
    let pre = X::State { number: 3int };
    X::show::observe(pre, pre, 3int);
    reveal(X::State::next_by);
    reveal(X::State::next_strong_by);
    reveal(X::State::init_by);
    assert(X::State::next_by(pre, pre, X::Step::observe(3int)));
    assert(X::State::next_strong_by(pre, pre, X::Step::observe(3int)));
    assert(!X::State::next_by(pre, pre, X::Step::dummy_to_use_type_params(pre)));
    assert(!X::State::init_by(pre, X::Config::dummy_to_use_type_params(pre)));
    assert(X::State::init_by(pre, X::Config::initialize(3int)));
}

fn main() {
}

} // verus!
