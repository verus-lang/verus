#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

#[verifier::external_body]
fn print_two_digit_number(i: i8)
    requires
        -99 <= i < 100,
{
    println!("The answer is {}", i);
}

fn octuple(x1: i8) -> (x8: i8)
    requires
        -16 <= x1 < 16,
    ensures
        x8 == 8 * x1,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}

fn main() {
    let n = octuple(10);
    assert(n == 80);
    print_two_digit_number(n);
}

} // verus!
