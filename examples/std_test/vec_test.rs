use std::vec::Vec;

use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

verus! {

fn vec_extend_slice_test() {
    let mut a: Vec<u32> = vec![1, 2];
    let b: Vec<u32> = vec![3, 4];
    a.extend_from_slice(b.as_slice());
    runtime_assert(a.len() == 4);
    runtime_assert(a[0] == 1);
    runtime_assert(a[1] == 2);
    runtime_assert(a[2] == 3);
    runtime_assert(a[3] == 4);
    runtime_assert(b.len() == 2);
}

} // verus!
