//! Boolean ownership is exclusive and can only be removed by its owner.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_bool::*;

verus! {

pub struct Boolean;

impl Machine for Boolean {
    type Fragment = CountRA;

    type State = bool;

    open spec fn invariant(state: bool) -> bool {
        true
    }

    open spec fn embed(state: bool) -> CountRA {
        bool_frag(state)
    }
}

proof fn boolean_add_and_remove() {
    bool_owned_frame(bool_frag(true), bool_frag(false), true);
    bool_add_frame(bool_frag(false), bool_frag(false), false);
    bool_remove_frame(bool_frag(true), bool_frag(false), true);
    assert(CountRA::op(bool_frag(true), bool_frag(true)).count == 2);
    assert(CountRA::op(bool_frag(true), bool_frag(true)) != bool_frag(false));
    assert(CountRA::op(bool_frag(true), bool_frag(true)) != bool_frag(true));
}

proof fn consume_owned_boolean_with_borrowed_empty_frame() {
    let tracked all = Token::<Boolean>::alloc_state(true);
    let tracked (owner, shared) = all.split(bool_frag(true), bool_frag(false));
    assert(frame_update::<Boolean>(
        CountRA::op(owner.fragment(), shared.fragment()),
        CountRA::op(bool_frag(false), shared.fragment()),
    )) by {
        assert forall|frame: CountRA, state: bool|
            Boolean::invariant(state) && CountRA::op(
                CountRA::op(owner.fragment(), shared.fragment()),
                frame,
            ) == Boolean::embed(state) implies exists|next: bool|
            Boolean::invariant(next) && CountRA::op(
                CountRA::op(bool_frag(false), shared.fragment()),
                frame,
            ) == Boolean::embed(next) by {
            bool_remove_frame(CountRA::op(owner.fragment(), shared.fragment()), frame, state);
            assert(CountRA::op(CountRA::op(bool_frag(false), shared.fragment()), frame)
                == Boolean::embed(false));
        }
    };
    let tracked owner = owner.update_with_shared(&shared, bool_frag(false));
    assert(owner.fragment() == bool_frag(false));
    assert(shared.fragment() == bool_frag(false));
    let tracked all = owner.join(shared);
    assert(all.fragment() == bool_frag(false));
}

fn main() {
}

} // verus!
