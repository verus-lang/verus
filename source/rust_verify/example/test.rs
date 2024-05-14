use builtin::*;
use builtin_macros::*;

verus! {

pub fn foo(a: u64) -> u64
    requires
        a < 100,
{
    a + 1
}

fn main() {
    let c = 1;
    let mut b = 3;
    b = 4;
    b = foo(c);
}

} // verus!
