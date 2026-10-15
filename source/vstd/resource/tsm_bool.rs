//! Checked exclusive boolean fragments for proof-producing state machines.
//!
//! An additive count represents absent (zero) or present (one) ownership.
//! Completing a fragment to a boolean state excludes overlapping owners.
use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::tsm::CountRA;

verus! {

pub open spec fn bool_frag(value: bool) -> CountRA {
    CountRA { count: if value { 1 } else { 0 } }
}

pub proof fn bool_owned_frame(owned: CountRA, frame: CountRA, whole: bool)
    requires
        CountRA::op(owned, frame) == bool_frag(whole),
    ensures
        owned.count <= 1,
        frame.count <= 1,
        owned.count == 1 ==> whole && frame.count == 0,
        !whole ==> owned.count == 0 && frame.count == 0,
{
}

/// Addition requires absence in the complete state, including its frame.
pub proof fn bool_add_frame(owned: CountRA, frame: CountRA, whole: bool)
    requires
        CountRA::op(owned, frame) == bool_frag(whole),
        !whole,
    ensures
        owned.count == 0,
        frame.count == 0,
        CountRA::op(CountRA { count: owned.count + 1 }, frame) == bool_frag(true),
{
    bool_owned_frame(owned, frame, whole);
}

/// Removal requires ownership of the present boolean in the consumed fragment.
pub proof fn bool_remove_frame(owned: CountRA, frame: CountRA, whole: bool)
    requires
        CountRA::op(owned, frame) == bool_frag(whole),
        owned.count >= 1,
    ensures
        whole,
        owned.count == 1,
        frame.count == 0,
        CountRA::op(CountRA { count: (owned.count - 1) as nat }, frame) == bool_frag(false),
{
    bool_owned_frame(owned, frame, whole);
}

}
