// rust_verify/tests/example.rs expect-failures

use builtin_macros::*;
use builtin::*;
#[cfg(not(vstd_todo))]
mod pervasive;
#[cfg(not(vstd_todo))]
use pervasive::*;
#[cfg(vstd_todo)]
use vstd::*;

verus! {

fn main() {}

fn test(b: bool) {
    assert(b);
}

fn has_expectations(b:bool) {
    requires(b);
}

fn fails_expectations() {
    has_expectations(false);
}

fn fails_post()
    ensures
        false,
{

    let x = 5;
    let y = 7;
}

} // verus!
