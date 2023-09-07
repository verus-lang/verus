use std::vec::{from_elem};

use vstd::prelude::*;
use vstd::pervasive::runtime_assert;

verus! {

fn from_elem_test() {
    let a: Vec<i32> = vec![3; 7];
    runtime_assert(a.len() == 7);
    runtime_assert(a[5] == 3);
}

} // verus!
