use vstd::prelude::*;
use vstd::pervasive::runtime_assert;

verus! {
    
fn is_ok_test() {
    let r1: Result<i32, i32> = Ok(7);
    runtime_assert(r1.is_Ok() == true);
    let r2: Result<i32, i32> = Err(7);
    runtime_assert(r2.is_Ok() == false);
    let r3: Result<i32, bool> = Err(true);
    runtime_assert(r3.is_Ok() == false);
}

fn map_test_helper(x: i32) -> (y: i32)
    requires
        x < 100000
    ensures
        y > x
{
    x + 1
}

fn map_test() {
    let r1: Result<i32, i32> = Ok(7);
    let r2; Result<i32, i32> = r1.map(|i| i+1);
    runtime_assert(r2.is_ok());
    runtime_assert(r2.get_Ok_0() == 8);
    let r3 = r1.map(map_test_helper);
    runtime_assert(r3.is_ok());
    runtime_assert(r3.get_Ok_0() > 7);
    let r4: Result<i32, i32> = Err(9);
    runtime_assert(r4.map(map_test_helper) == Err(9));
    runtime_assert(r4.map(|i| i+1) == Err(9));
}
    
} // verus!
