use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

pub fn foo(a: u64) -> u64
    requires
        a < 100,
{
    a + 1
}

fn test_foo() {
    assert(foo(0) == 1);
    assert(foo(99) == 100);
}

fn main() {
    let c = 1;
    let mut b = 3;
    b = 4;
    b = foo(c);
}

} // verus!
