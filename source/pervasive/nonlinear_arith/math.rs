#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
verus! {

    pub open spec fn min(a: int, b: int) -> int
    {
      if a < b
      { a }
      else
      { b }
    }

    pub open spec fn max(a: int, b: int) -> int
    {
      if a < b { b } else { a }
    }

    pub open spec fn max3(a: int, b: int, c: int) -> int
    {
      if a < b { max(b, c) } else { max(a, c) }
    }

    pub open spec fn abs(a: int) -> (b: int)
    {
      if a >= 0 { a } else { -a }
    }

    pub open spec fn add (a: int, b: int) -> int
    {
        a + b
    }

    pub open spec fn sub (a: int, b: int) -> int
    {
        a - b
    }

    pub open spec fn div (a: int, b: int) -> int
    {
        a / b
    }

}
