//! Raw backend statement forms: repeated additions to persistent fields, each
//! sequence composed by the idempotent join of the field's algebra.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Persist {
        fields {
            #[sharding(persistent_count)] pub hi: nat,
            #[sharding(persistent_bool)] pub done: bool,
            #[sharding(persistent_set)] pub seen: Set<int>,
            #[sharding(persistent_map)] pub log: Map<int, int>,
            #[sharding(persistent_option)] pub first: Option<int>,
        }
        init! { initialize() { init hi = 0; init done = false; init seen = Set::empty();
            init log = Map::empty(); init first = None; } }
        transition! { raise_twice(a: nat, b: nat) {
            add hi (union)= (a);
            add hi (union)= (b);
            have hi >= (a);
        } }
        transition! { finish_twice() {
            add done (union)= true;
            add done (union)= true;
        } }
        transition! { see_two(a: int, b: int) {
            have seen >= set {a};
            add seen (union)= set {a};
            add seen (union)= set {b};
        } }
        transition! { log_two(k: int, v: int, k2: int) {
            require(k != k2);
            have log >= [k => v];
            have log >= [k2 => v];
            add log (union)= [k => v];
            add log (union)= [k2 => v];
        } }
        transition! { set_first_twice(v: int) {
            have first >= Some(v);
            add first (union)= Some(v);
            add first (union)= Some(v);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(raise_twice)] fn raise_twice_inductive(pre: Self, post: Self, a: nat, b: nat) {}
        #[inductive(finish_twice)] fn finish_twice_inductive(pre: Self, post: Self) {}
        #[inductive(see_two)] fn see_two_inductive(pre: Self, post: Self, a: int, b: int) {}
        #[inductive(log_two)] fn log_two_inductive(pre: Self, post: Self, k: int, v: int, k2: int) {}
        #[inductive(set_first_twice)] fn set_first_twice_inductive(pre: Self, post: Self, v: int) {}
    }
}
proof fn persistent_history() {
    let tracked token = Persist::Protocol::initialize();
    let tracked token = Persist::Protocol::raise_twice(token, 0, 0);
    let tracked token = Persist::Protocol::finish_twice(token);
    assert(token.fragment().done.count >= 1);
}

fn main() {}

} // verus!
