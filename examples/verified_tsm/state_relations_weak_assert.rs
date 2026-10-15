use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 X {
    fields {
        #[sharding(variable)] pub x: int,
        #[sharding(persistent_bool)] pub flag: bool,
    }
    init! { initialize() { init x = 0; init flag = false; } }
    transition! { advance() { assert pre.x >= 0; update x = pre.x + 1; } }
    #[invariant] pub fn nonnegative(&self) -> bool { self.x >= 0 }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(advance)] fn advance_inductive(pre: Self, post: Self) {}
}}
verus! {

proof fn original_relations(pre: X::State, post: X::State) {
    assert(X::State::advance(pre, post) == (pre.x >= 0 ==> post.x == pre.x + 1 && post.flag
        == pre.flag));
    assert(X::State::advance_strong(pre, post) == (pre.x >= 0 && post.x == pre.x + 1 && post.flag
        == pre.flag));
    assert(X::State::advance_enabled_weak(pre) == X::State::advance_enabled(pre));
}

fn main() {
    proof {
        let pre = X::State { x: -1, flag: false };
        let post = X::State { x: -1, flag: true };
        original_relations(pre, post);
        assert(X::State::advance(pre, post));
        assert(!X::State::advance_strong(pre, post));
    }
}

} // verus!
