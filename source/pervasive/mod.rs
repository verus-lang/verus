pub mod map;
pub mod option;
pub mod vec;
pub mod seq;
pub mod seq_lib;
pub mod set;
pub mod set_lib;

#[allow(unused_imports)]
use builtin::*;

#[proof]
pub fn assume(b: bool) {
    ensures(b);

    admit();
}

#[proof]
#[verifier(custom_req_err("assertion failure"))]
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
fn arbitrary_external<A>() -> A {
    unimplemented!()
}

#[spec]
#[verifier(external_body)]
#[allow(dead_code)]
pub fn arbitrary<A>() -> A {
    arbitrary_external()
}

#[proof]
#[verifier(returns(proof))]
#[verifier(external)]
#[allow(dead_code)]
fn proof_from_false_external<A>() -> A {
    unimplemented!()
}

#[proof]
#[verifier(returns(proof))]
#[verifier(external_body)]
#[allow(dead_code)]
pub fn proof_from_false<A>() -> A {
    requires(false);

    proof_from_false_external()
}

#[verifier(external)]
#[allow(dead_code)]
pub fn unreached_external<A>() -> A {
    panic!("unreached_external")
}

#[verifier(external_body)]
#[allow(dead_code)]
pub fn unreached<A>() -> A {
    requires(false);

    unreached_external()
}

#[verifier(external)]
pub fn print_u64_external(i: u64) {
    println!("{}", i);
}

#[verifier(external_body)]
pub fn print_u64(i: u64) {
    print_u64_external(i);
}
