// EXPECTED-ERROR: cannot move out of
#[path = "../counting_to_2.rs"]
mod counting_protocol;
use counting_protocol::X;
use vstd::prelude::*;
verus! {
proof fn misuse(tracked counter:&X::counter) { let tracked raw=counter.borrow_token(); let tracked invalid=X::Protocol::tr_inc_a(*raw); }
}
fn main(){}
