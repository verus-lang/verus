#[allow(unused_imports)]
use super::prelude::*;

verus! {

/// This function computes the minimum of two given integers.
pub open spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

/// This function computes the maximum of two given integers.
pub open spec fn max(x: int, y: int) -> int {
    if x >= y {
        x
    } else {
        y
    }
}

/// This function computes the maximum of three given integers.
pub open spec fn max3(x: int, y: int, z: int) -> int {
    if x < y {
        max(y, z)
    } else {
        max(x, z)
    }
}

/// This function converts the given integer `x` to a natural number
/// by returning 0 when `x` is negative and `x` otherwise.
pub open spec fn clip(x: int) -> nat {
    if x < 0 {
        0
    } else {
        x as nat
    }
}

/// This function computes the absolute value of a given integer.
pub open spec fn abs(x: int) -> nat {
    if x < 0 {
        -x as nat
    } else {
        x as nat
    }
}

/// This function adds two integers together. It's sometimes
/// useful as a substitute for `+` in triggers that feature
/// function invocations, since mathematical operators can't be
/// mixed with function invocations in triggers.
pub open spec fn add(x: int, y: int) -> int {
    x + y
}

/// This function subtracts two integers. It's sometimes useful as
/// a substitute for `-` in triggers that feature function
/// invocations, since mathematical operators can't be mixed with
/// function invocations in triggers.
pub open spec fn sub(x: int, y: int) -> int {
    x - y
}

/// This function divides two integers. It's sometimes useful as a
/// substitute for `/` in triggers that feature function
/// invocations, since mathematical operators can't be mixed with
/// function invocations in triggers.
pub open spec fn div(x: int, y: int) -> int {
    x / y
}

} // verus!
