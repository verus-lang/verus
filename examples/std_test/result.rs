use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

verus! {

fn is_ok_test() {
    let r1: Result<i32, i32> = Ok(7);
    runtime_assert(r1.is_ok() == true);
    let r2: Result<i32, i32> = Err(7);
    runtime_assert(r2.is_ok() == false);
    let r3: Result<i32, bool> = Err(true);
    runtime_assert(r3.is_ok() == false);
}

fn map_test() {
    let r1: Result<i32, i32> = Ok(7);
    let op = |x: i32| -> (y: i32)
        requires
            x < 100000,
        ensures
            y > x,
        { x + 1 };
    let r2 = r1.map(op);
    runtime_assert(r2.unwrap() > 7);
    let r3: Result<i32, i32> = Err(9);
    let r4: Result<i32, i32> = r3.map(op);
    runtime_assert(r4.unwrap_err() == 9);
}

fn ok_test() {
    let r1: Result<i32, i32> = Ok(7);
    runtime_assert(r1.ok().is_some());
    runtime_assert(r1.ok().unwrap() == 7);
    let r2: Result<i32, i32> = Err(7);
    runtime_assert(r2.ok().is_none());
    let r3: Result<i32, bool> = Err(true);
    runtime_assert(r3.ok().is_none());
    let r4: Result<bool, i32> = Ok(false);
    runtime_assert(r4.ok().is_some());
    runtime_assert(r4.ok().unwrap() == false);
}

fn err_test() {
    let r1: Result<i32, i32> = Ok(7);
    runtime_assert(r1.err().is_none());
    let r2: Result<i32, i32> = Err(7);
    runtime_assert(r2.err().is_some());
    runtime_assert(r2.err().unwrap() == 7);
    let r3: Result<i32, bool> = Err(true);
    runtime_assert(r3.err().is_some());
    runtime_assert(r3.err().unwrap() == true);
    let r4: Result<bool, i32> = Ok(true);
    runtime_assert(r4.err().is_none());
}

} // verus!
