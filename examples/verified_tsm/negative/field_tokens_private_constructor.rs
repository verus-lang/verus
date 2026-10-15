// EXPECTED-ERROR: disallowed: constructor for an opaque datatype
use vstd::prelude::*;
#[path="../counting_to_2.rs"] mod demo;
verus! {
proof fn misuse(tracked token:demo::X::Token)->(tracked out:demo::X::counter){
    demo::X::counter {raw:token}
}
fn main(){}
}
