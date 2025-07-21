// rust_verify/tests/example.rs expect-warnings
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: spec_const
spec const SPEC_ONE: int = 1;

spec fn spec_add_one(x: int) -> int {
    x + SPEC_ONE
}
// ANCHOR_END: spec_const

// ANCHOR: exec_const_syntax
exec const C: u64 
    ensures C == 7 
{
    7 
}
// ANCHOR_END: exec_const_syntax

// ANCHOR: exec_const_complicated
spec fn f() -> int { 1 }
const fn e() -> (u: u64) ensures u == f() { 1 }
exec const E: u64 ensures E == 2 {
    assert(f() == 1);
    1 + e()
}

exec const C: int ensures C == 7 { 7 }
// ANCHOR_END: exec_const_complicated

// ANCHOR: spec_exec_const
const ONE: u8 = 1;

fn add_one(x: u8) -> (ret: u8)
    requires
        x < 0xff,
    ensures
        ret == x + ONE,  // use "ONE" in spec code
{
    x + ONE  // use "ONE" in exec code
}
// ANCHOR_END: spec_exec_const

// ANCHOR: when_used_as_spec
use vstd::layout;

global layout usize is size == 8;

spec const SPEC_USIZE_BYTES: usize = layout::size_of_as_usize::<usize>();

#[verifier::when_used_as_spec(SPEC_USIZE_BYTES)]
exec const USIZE_BYTES: usize 
    ensures USIZE_BYTES as nat == layout::size_of::<usize>() 
{
    8
}
// ANCHOR_END: when_used_as_spec

// ANCHOR: nonlinear
pub const FOO: u8 = 4;
pub const BAR: u8 = FOO; //4
pub const BAR_PLUS_ONE: u8 = BAR + 1; 
#[verifier::nonlinear]
pub const C: u8 = BAR_PLUS_ONE * BAR;
// ANCHOR_END: nonlinear

fn main() {
}

}