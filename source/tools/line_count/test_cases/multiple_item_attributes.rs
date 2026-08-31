use vstd::prelude::*;

#[verus_verify]
#[verus::trusted]
#[verus_spec(ret => ensures ret == x)]
fn trusted_identity(x: u64) -> u64 {
    x
}

fn main() {}
