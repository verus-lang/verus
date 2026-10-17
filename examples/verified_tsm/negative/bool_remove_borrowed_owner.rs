// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm::*;
use vstd::resource::tsm_bool::*;
#[path = "../bool_algebra.rs"]
mod model;

verus! {

proof fn cannot_consume_the_borrowed_owner(
    tracked owned: Token<model::Boolean>,
    tracked borrowed: &Token<model::Boolean>,
)
    requires
        owned.loc() == borrowed.loc(),
        owned.fragment() == bool_frag(false),
        borrowed.fragment() == bool_frag(true),
{
    // The complete boolean is present, but its owner is the borrowed fragment.
    bool_remove_frame(owned.fragment(), borrowed.fragment(), true);
}

fn main() {
}

} // verus!
