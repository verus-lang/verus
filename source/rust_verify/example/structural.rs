// rust_verify/tests/example.rs
use builtin::*;
use builtin_macros::*;

verus! {

#[derive(Eq)]
struct Thing {}

impl std::cmp::PartialEq for Thing {
    fn eq(&self, _: &Self) -> bool {
        todo!()
    }
}

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

fn main() {
}

} // verus!
