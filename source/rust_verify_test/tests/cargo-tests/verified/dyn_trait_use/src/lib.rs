use dyn_trait_def::{M, N};
use vstd::prelude::*;

verus! {

// Use dyn of a trait declared in another crate
pub struct C;

impl N for C {
    fn s(&self) -> (r: u8) {
        1
    }
}

pub struct E;

impl M for E {
    fn map(&self) -> Option<Box<dyn N>> {
        Some(Box::new(C))
    }
}

pub fn param(x: &dyn N) -> (r: u8)
    ensures
        r < 10,
{
    x.s()
}

pub fn local() -> (r: u8)
    ensures
        r < 10,
{
    let c = C;
    let d: &dyn N = &c;
    param(d)
}

} // verus!
