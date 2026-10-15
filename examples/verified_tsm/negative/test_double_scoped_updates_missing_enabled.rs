// EXPECTED-ERROR: precondition not satisfied
#[path = "../test_double_scoped_updates_match.rs"]
mod model;
use vstd::prelude::*;
verus! {

proof fn test_take_step2(
    pre: model::X::State,
    x: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) {
    let post = model::checked_take_step(pre, x, y, z, w, v);
}

} // verus!
fn main() {}
