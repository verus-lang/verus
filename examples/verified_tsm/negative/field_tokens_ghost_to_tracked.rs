// EXPECTED-ERROR: expression has mode spec, expected mode proof
use vstd::prelude::*;
#[path="../counting_to_2.rs"] mod demo;
verus! {
proof fn misuse(ghost:demo::X::counter)->(tracked out:demo::X::counter){ghost}
fn main(){}
}
