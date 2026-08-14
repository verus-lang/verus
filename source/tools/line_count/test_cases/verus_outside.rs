use vstd::prelude::*;

fn exec_min(a: u32, b: u32) -> u32 {
    if a < b { a } else { b }
}

verus! {

spec fn spec_min(a: u32, b: u32) -> u32 {
    if a < b { a } else { b }
}

assume_specification[exec_min](a: u32, b: u32) -> (r: u32)
    ensures
        r == spec_min(a, b)
;

}
