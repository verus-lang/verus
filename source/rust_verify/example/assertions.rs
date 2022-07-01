// rust_verify/tests/example.rs expect-failures

use builtin::*;
mod pervasive;
use pervasive::*;

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

fn fails_post() {
    ensures(false);

    let x = 5;
    let y = 7;
}

#[verifier(custom_req_err("failed first arg", 0))]
#[verifier(custom_req_err("failed second arg", 1))]
fn detailed(b: bool, c: bool)
{
    requires([
        b,
        c,
    ]);
}

fn fails1() {
    detailed(false, true);
}

fn fails2() {
    detailed(true, false);
}
