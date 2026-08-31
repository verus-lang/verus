use vstd::prelude::*;

#[verus_verify(dual_spec)]
pub fn identity(value: u64) -> u64 {
    value
}

fn main() {}
