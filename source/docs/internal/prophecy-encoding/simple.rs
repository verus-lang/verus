use builtin::*;
use builtin_macros::verus;

verus! {

fn main() {
    let mut a = 0;
    let mut b = &mut a;
    *b = 5;
    resolve(b);
    assert(a == 5);
}

} // verus!
