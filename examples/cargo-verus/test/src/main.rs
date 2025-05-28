use vstd::{prelude::*, string::*};

verus! {

#[verifier::external_body]
fn print_result(value: u32) {
    println!("{value}");
}

fn main() {
    let x = library::f();
    assert(x == 4);
    print_result(x as u32);
}

} // verus!
