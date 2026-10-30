//! Checked maximum-count PCM for persistent lower-bound knowledge.
//! This is the `MaxN` component used by the Lean VerusSync construction.
use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;

verus! {
pub open spec fn count_max(left: nat, right: nat) -> nat {
    if left >= right { left } else { right }
}

pub struct PersistentCountRA { pub count: nat }

impl ResourceAlgebra for PersistentCountRA {
    open spec fn valid(self) -> bool { true }
    open spec fn op(left: Self, right: Self) -> Self {
        Self { count: count_max(left.count, right.count) }
    }
    proof fn associative(a: Self, b: Self, c: Self) {}
    proof fn commutative(a: Self, b: Self) {}
    proof fn valid_op(a: Self, b: Self) {}
}

impl PCM for PersistentCountRA {
    open spec fn unit() -> Self { Self { count: 0 } }
    proof fn op_unit(self) {}
    proof fn unit_valid() {}
}

pub proof fn persistent_count_idempotent(fragment: PersistentCountRA)
    ensures
        PersistentCountRA::op(fragment, fragment) == fragment,
{
}

pub proof fn persistent_count_owned_frame(
    owned: PersistentCountRA, frame: PersistentCountRA, whole: nat,
)
    requires
        PersistentCountRA::op(owned, frame).count == whole,
    ensures
        owned.count <= whole,
        frame.count <= whole,
{
}

pub proof fn persistent_count_raise_frame(
    owned: PersistentCountRA, frame: PersistentCountRA, whole: nat, lower_bound: nat,
)
    requires
        PersistentCountRA::op(owned, frame).count == whole,
    ensures
        PersistentCountRA::op(
            PersistentCountRA { count: count_max(owned.count, lower_bound) }, frame,
        ).count == count_max(whole, lower_bound),
{
    let knowledge = PersistentCountRA { count: lower_bound };
    PersistentCountRA::associative(owned, knowledge, frame);
    PersistentCountRA::commutative(knowledge, frame);
    PersistentCountRA::associative(owned, frame, knowledge);
}

/// False carries no knowledge; true carries a duplicable observation.
pub open spec fn persistent_bool_frag(value: bool) -> PersistentCountRA {
    PersistentCountRA { count: if value { 1 } else { 0 } }
}

pub proof fn persistent_bool_owned_frame(
    owned: PersistentCountRA, frame: PersistentCountRA, whole: bool,
)
    requires
        PersistentCountRA::op(owned, frame) == persistent_bool_frag(whole),
    ensures
        owned.count <= 1,
        frame.count <= 1,
        owned.count == 1 ==> whole,
        !whole ==> owned.count == 0 && frame.count == 0,
{
    persistent_count_owned_frame(owned, frame, if whole { 1 } else { 0 });
}

pub proof fn persistent_bool_raise_frame(
    owned: PersistentCountRA, frame: PersistentCountRA, whole: bool, added: bool,
)
    requires
        PersistentCountRA::op(owned, frame) == persistent_bool_frag(whole),
    ensures
        PersistentCountRA::op(
            PersistentCountRA::op(owned, persistent_bool_frag(added)), frame,
        ) == persistent_bool_frag(whole || added),
{
    persistent_count_raise_frame(owned, frame, if whole { 1 } else { 0 },
        if added { 1 } else { 0 });
}
}
