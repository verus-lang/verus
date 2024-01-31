#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

pub open spec fn min(x: int, y: int) -> int {
    if x <= y {x}
    else {y}
}

pub open spec fn max(x: int, y: int) -> int {
    if x >= y {x}
    else {y}
}

pub open spec fn clip(x: int) -> nat {
    if x < 0 {0}
    else {x as nat}
}

pub open spec fn abs(x: int) -> nat {
    if x < 0 {-x as nat}
    else {x as nat}
}

}
