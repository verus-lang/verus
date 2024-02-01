//! This file contains functions describing mathematical operations.
//! These are part of the math standard library.

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
verus! {

    /// This function computes the minimum of two given integers
    pub open spec fn min(a: int, b: int) -> int
    {
      if a < b
      { a }
      else
      { b }
    }

    /// This function computes the maximum of two given integers
    pub open spec fn max(a: int, b: int) -> int
    {
      if a < b { b } else { a }
    }

    /// This function computes the maximum of three given integers
    pub open spec fn max3(a: int, b: int, c: int) -> int
    {
      if a < b { max(b, c) } else { max(a, c) }
    }

    /// This function computes the absolute value of a given integer
    pub open spec fn abs(a: int) -> (b: int)
    {
      if a >= 0 { a } else { -a }
    }

    /// This function adds two integers together. It's sometimes
    /// useful as a substitute for `+` in triggers that feature
    /// function invocations, since mathematical operators can't be
    /// mixed with function invocations in triggers.
    pub open spec fn add (a: int, b: int) -> int
    {
        a + b
    }

    /// This function subtracts two integers. It's sometimes useful as
    /// a substitute for `-` in triggers that feature function
    /// invocations, since mathematical operators can't be mixed with
    /// function invocations in triggers.
    pub open spec fn sub (a: int, b: int) -> int
    {
        a - b
    }

    /// This function divides two integers. It's sometimes useful as a
    /// substitute for `/` in triggers that feature function
    /// invocations, since mathematical operators can't be mixed with
    /// function invocations in triggers.
    pub open spec fn div (a: int, b: int) -> int
    {
        a / b
    }

}
