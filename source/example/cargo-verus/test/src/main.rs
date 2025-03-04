use vstd::{prelude::*, string::*};

verus! {

#[verifier::external_body]
fn print_result(msg: StrSlice<'static>, value: u32) {
    println!("{}: {value}", msg.into_rust_str());
}

fn main() {
    let x = library::f();
    assert(x == 4);
    print_result(new_strlit("value"), x as u32);
}

} // verus!
