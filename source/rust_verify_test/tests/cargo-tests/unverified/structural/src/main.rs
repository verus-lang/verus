use vstd::prelude::*;

#[derive(Structural, Debug, Copy, Clone, PartialEq)]
struct A(u8);

verus! {

fn main() {
    let _a = A(5);
    assert(1 == 0 + 1);
}

}
