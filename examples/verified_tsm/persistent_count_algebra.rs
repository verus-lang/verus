//! Persistent count fragments duplicate lower bounds and compose by maximum.
//! Mathematical backend demonstration, not generated-strategy coverage.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_persistent::*;

verus! {

pub struct Bounded;

impl Machine for Bounded {
    type Fragment = PersistentCountRA;

    type State = nat;

    open spec fn invariant(state: nat) -> bool {
        state <= 10
    }

    open spec fn embed(state: nat) -> PersistentCountRA {
        PersistentCountRA { count: state }
    }
}

proof fn persistent_lower_bounds() {
    let tracked token = Token::<Bounded>::alloc_state(3);
    persistent_count_idempotent(token.fragment());
    let tracked copy = token.duplicate();
    let old_fragment = token.fragment();
    let next_fragment = PersistentCountRA { count: 7 };
    assert(frame_update::<Bounded>(old_fragment, next_fragment)) by {
        assert forall|frame: PersistentCountRA, state: nat|
            Bounded::invariant(state) && PersistentCountRA::op(old_fragment, frame)
                == Bounded::embed(state) implies exists|next: nat|
            Bounded::invariant(next) && PersistentCountRA::op(next_fragment, frame)
                == Bounded::embed(next) by {
            persistent_count_raise_frame(old_fragment, frame, state, 7);
            let next = count_max(state, 7);
            assert(Bounded::invariant(next));
            assert(PersistentCountRA::op(next_fragment, frame) == Bounded::embed(next));
        }
    };
    let tracked token = token.update(next_fragment);
    assert(copy.fragment().count == 3);
    assert(token.fragment().count == 7);
    let tracked combined = token.join(copy);
    assert(combined.fragment().count == 7);
}

fn main() {
}

} // verus!
