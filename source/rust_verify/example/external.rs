extern crate builtin;
use builtin::*;
mod pervasive;

#[verifier(external)]
fn test_impl(n: u64) {
    println!("hello {}", n);
}

#[verifier(no_verify)]
fn test(n: u64, #[spec] s: int) {
    requires(n > 10 && s >= n);
    test_impl(n);
}

fn main() {
    test(15, 200);
}
