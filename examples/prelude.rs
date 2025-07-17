#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
use vstd::prelude::*;

verus! {

proof fn lemma() {
    let a: Seq<nat> = seq![1, 2, 3];
    assert(a[1] == 2);
}

fn main() {
}

} // verus!
