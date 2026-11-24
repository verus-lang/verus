use vstd::prelude::*;

verus! {

// Used as `dyn N` by the dyn_trait_use crate
pub trait N {
    fn s(&self) -> (r: u8)
        ensures
            r < 10,
    ;
}

pub trait M {
    fn map(&self) -> Option<Box<dyn N>>;
}

// Not Verus dyn-compatible: the self parameter of a proof fn must be tracked.
// The cargo-tests/failing/dyn_trait_not_dyn_compatible crate uses it as `dyn NotDyn`.
pub trait NotDyn {
    proof fn bogus(&self)
        ensures
            false,
    ;
}

} // verus!
