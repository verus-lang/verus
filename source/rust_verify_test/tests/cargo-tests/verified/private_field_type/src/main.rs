use private_field_type::{Exposed, make_exposed};
use vstd::prelude::*;

verus! {

fn main() {
    let _exposed: Exposed = make_exposed();
}

} // verus!
