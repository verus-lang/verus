// rust_verify/tests/example.rs
use builtin::*;
use builtin_macros::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
struct Thing {}

#[derive(PartialEq, Eq, Structural)]
struct Car<T> {
    passengers: T,
    four_doors: bool,
}

fn one() {
    let c1 = Car { passengers: Thing {  }, four_doors: true };
    let c2 = Car { passengers: Thing {  }, four_doors: true };
    assert(c1 == c2);
}

fn two(c1: Car<u64>, c2: Car<u64>) {
  if c1 == c2 {
    assert(c1 == c2);
  }
}

fn main() {
}

} // verus!
