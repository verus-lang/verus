//! Persistent true observations survive union with false and remain duplicable.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_persistent::*;

verus! {

pub struct BooleanKnowledge;

impl Machine for BooleanKnowledge {
    type State = bool;

    type Fragment = PersistentCountRA;

    open spec fn invariant(state: bool) -> bool {
        true
    }

    open spec fn embed(state: bool) -> PersistentCountRA {
        persistent_bool_frag(state)
    }
}

proof fn raise_and_retain_boolean() {
    let tracked owner = Token::<BooleanKnowledge>::alloc_state(false);
    persistent_count_idempotent(owner.fragment());
    let tracked initial_copy = owner.duplicate();
    let before = owner.fragment();
    let after = PersistentCountRA::op(before, persistent_bool_frag(true));
    assert(frame_update::<BooleanKnowledge>(before, after)) by {
        assert forall|frame: PersistentCountRA, state: bool|
            BooleanKnowledge::invariant(state) && PersistentCountRA::op(before, frame)
                == BooleanKnowledge::embed(state) implies exists|post: bool|
            BooleanKnowledge::invariant(post) && PersistentCountRA::op(after, frame)
                == BooleanKnowledge::embed(post) by {
            persistent_bool_raise_frame(before, frame, state, true);
            assert(PersistentCountRA::op(after, frame) == BooleanKnowledge::embed(true));
        };
    };
    let tracked owner = owner.update(after);
    assert(owner.fragment() == persistent_bool_frag(true));
    // The initial zero fragment conveys no claim that the full state is false.
    assert(initial_copy.fragment().count == 0);
    persistent_count_idempotent(owner.fragment());
    let tracked observed = owner.duplicate();
    let before = owner.fragment();
    let after = PersistentCountRA::op(before, persistent_bool_frag(false));
    assert(frame_update::<BooleanKnowledge>(before, after)) by {
        assert forall|frame: PersistentCountRA, state: bool|
            BooleanKnowledge::invariant(state) && PersistentCountRA::op(before, frame)
                == BooleanKnowledge::embed(state) implies exists|post: bool|
            BooleanKnowledge::invariant(post) && PersistentCountRA::op(after, frame)
                == BooleanKnowledge::embed(post) by {
            persistent_bool_raise_frame(before, frame, state, false);
            assert(PersistentCountRA::op(after, frame) == BooleanKnowledge::embed(state));
        };
    };
    let tracked owner = owner.update(after);
    assert(observed.fragment() == persistent_bool_frag(true));
    assert(owner.fragment() == observed.fragment());
    let tracked all = owner.join(observed).join(initial_copy);
    all.validate();
}

fn main() {
}

} // verus!
