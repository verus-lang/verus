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
pub fn arbitrary_external<A>() -> A {
    unimplemented!()
}

#[spec]
#[verifier(no_verify)]
#[allow(dead_code)]
pub fn arbitrary<A>() -> A {
    arbitrary_external()
}

#[verifier(external)]
pub fn print_u64_external(i: u64) {
    println!("{}", i);
}

#[verifier(no_verify)]
pub fn print_u64(i: u64) {
    print_u64_external(i);
}
