//! Optional ownership can be removed and reinserted in the same protocol step.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_collections::*;

verus! {

pub struct OptionalCounter;

impl Machine for OptionalCounter {
    type State = Option<nat>;

    type Fragment = OptionFragment<nat>;

    open spec fn invariant(state: Self::State) -> bool {
        true
    }

    open spec fn embed(state: Self::State) -> Self::Fragment {
        option_frag(state)
    }
}

proof fn increment_owned_optional() {
    let tracked token = Token::<OptionalCounter>::alloc_state(Some(3nat));
    let owned = token.fragment();
    let replacement = option_frag(Some(4nat));
    assert(frame_update::<OptionalCounter>(owned, replacement)) by {
        assert forall|frame: OptionFragment<nat>, state: Option<nat>|
            OptionalCounter::invariant(state) && OptionFragment::op(owned, frame)
                == OptionalCounter::embed(state) implies exists|post: Option<nat>|
            OptionalCounter::invariant(post) && OptionFragment::op(replacement, frame)
                == OptionalCounter::embed(post) by {
            option_replace_frame(owned, frame, state, 3nat, 4nat);
            assert(OptionFragment::op(replacement, frame) == OptionalCounter::embed(Some(4nat)));
        };
    };
    let tracked token = token.update(replacement);
    assert(token.fragment() == option_frag(Some(4nat)));
    token.validate();
}

proof fn generic_replacement<V>(previous: V, replacement: V) {
    option_replace_frame(option_frag(Some(previous)), None, Some(previous), previous, replacement);
}

fn main() {
    proof {
        increment_owned_optional();
    }
}

} // verus!
