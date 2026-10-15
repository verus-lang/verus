//! Cloning immutable metadata neither clones nor updates the actual permission.
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::tsm_context::Descriptor;

verus! {

pub fn metadata_and_permission() -> (value: u64)
    ensures
        value == 9,
{
    let (cell, Tracked(mut permission)) = PCell::new(7u64);
    let ghost original = permission;
    let tracked descriptor = Descriptor::<PointsTo<u64>>::alloc(original);
    let tracked first = descriptor.clone();
    let tracked second = first.clone();
    assert(second.id() == descriptor.id());
    proof {
        descriptor.agrees(&second);
    }
    assert(second.value() == original);

    let old = cell.replace(Tracked(&mut permission), 9u64);
    assert(old == 7);
    assert(*second.value().value() == 7);
    assert(*permission.value() == 9);
    cell.into_inner(Tracked(permission))
}

fn main() {
    proof {
        let tracked left = Descriptor::alloc(7int);
        let tracked right = Descriptor::alloc(9int);
        if left.id() == right.id() {
            left.agrees(&right);
            assert(false);
        }
    }
    let value = metadata_and_permission();
    assert(value == 9);
}

} // verus!
