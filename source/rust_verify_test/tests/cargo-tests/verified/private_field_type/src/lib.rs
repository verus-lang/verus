#![allow(private_interfaces)]

use vstd::prelude::*;

verus! {

pub(crate) struct Hidden;

pub struct Exposed {
    pub hidden: Hidden,
}

pub fn make_exposed() -> Exposed {
    Exposed { hidden: Hidden }
}

} // verus!
