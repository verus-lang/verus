extern crate builtin;
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
