extern crate builtin;
use builtin::*;

#[proof]
pub fn assume(b: bool) {
    ensures(b);

    admit();
}

#[proof]
#[verifier(custom_req_err, "assertion failure")]
pub fn assert(b: bool) {
    requires(b);
    ensures(b);
}

#[proof]
pub fn affirm(b: bool) {
    requires(b);
}

/// In spec, all types are inhabited
#[spec]
#[verifier(external)]
#[allow(dead_code)]
pub fn arbitrary<A>() -> A {
    unimplemented!()
}
