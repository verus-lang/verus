use vstd::prelude::*;

#[verus_verify]
pub fn identity(value: u64) -> u64 {
    value
}

fn main() {}
