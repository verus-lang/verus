//! A raw-token machine none of whose transitions `local_ready` supports (a closure in an
//! operand), so the macro takes its fallback emitter (`verified_tokens::output_raw`):
//! its operations prove the (opaque) `frame_update` of their token updates directly.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Clo {
        fields {
            #[sharding(variable)] pub v: int,
            #[sharding(count)] pub c: nat,
        }
        init! { initialize() { init v = 0; init c = 0; } }
        transition! { bump(n: nat) {
            add c += ((|x: nat| x)(n));
            update v = pre.v + 1;
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(bump)] fn bump_inductive(pre: Self, post: Self, n: nat) {}
    }
}

fn main() {}

} // verus!
