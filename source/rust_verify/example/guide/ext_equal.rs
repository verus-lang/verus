#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use vstd::{seq::*, set::*, map::*, prelude::*};

verus! {

// ANCHOR: ext_eq_struct
#[verifier(ext_equal)] // necessary for invoking =~= on the struct
struct Foo{
    a: Seq<int>,
    b: Set<int>
}

proof fn ext_equal1() {
    let f1 = Foo{a: seq![1, 2, 3], b: set!{4, 5, 6} };
    let f2 = Foo{a: seq![1, 2].push(3), b: set!{5, 6}.insert(4) };

    assert(f1.a =~= f2.a);  // succeeds
    // assert(f1 == f2);    // FAILS
    assert(f1 =~= f2);      // succeeds
}
// ANCHOR_END: ext_eq_struct

// ANCHOR: ext_eq_nested
proof fn ext_equal2() {
    let inner : Set<int> = set!{1, 2, 3};
    let s1 : Seq<Set<int>> = seq![inner];

    let s2 = s1.update(0, s1[0].insert(1));
    let s3 = s1.update(0, s1[0].insert(2).insert(3));

    // assert(s2 == s3);  // FAILS
    // assert(s2 =~= s3); // FAILS
    assert(s2 =~~= s3);   // succeeds

    let s4 : Seq<Seq<Set<int>>> = seq![s1];
    let s5 : Seq<Seq<Set<int>>> = seq![s2];
    assert(s4 =~~= s5);   // succeeds
}
// ANCHOR_END: ext_eq_nested

fn main() {
}

} // verus!
