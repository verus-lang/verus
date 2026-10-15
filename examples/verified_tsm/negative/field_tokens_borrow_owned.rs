// EXPECTED-ERROR: cannot move out of
#[path = "../counting_to_2.rs"]
mod counting_protocol;
use counting_protocol::X;
use vstd::prelude::*;
verus! {
proof fn misuse(tracked counter:&X::counter)->(tracked out:X::Token) { *counter.borrow_token() }
}
fn main(){}
