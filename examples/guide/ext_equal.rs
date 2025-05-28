#[allow(unused_imports)]
use vstd::{map::*, prelude::*, seq::*, set::*};

verus! {

mod m1 {
    #[allow(unused_imports)]


    use vstd::{seq::*, set::*, map::*, prelude::*};

    // ANCHOR: ext_eq_struct_fields
    struct Foo {
        a: Seq<int>,
        b: Set<int>,
    }

    proof fn ext_equal_struct() {
        let f1 = Foo { a: seq![1, 2, 3], b: set!{4, 5, 6} };
        let f2 = Foo { a: seq![1, 2].push(3), b: set!{5, 6}.insert(4) };
        // assert(f1 == f2);    // FAILS -- need to use =~= first
        assert(f1.a =~= f2.a);  // succeeds
        assert(f1.b =~= f2.b);  // succeeds
        assert(f1 == f2);  // succeeds, now that we've used =~= on .a and .b
    }
    // ANCHOR_END: ext_eq_struct_fields

}

// ANCHOR: ext_eq_struct
#[verifier::ext_equal]  // necessary for invoking =~= on the struct
struct Foo {
    a: Seq<int>,
    b: Set<int>,
}

proof fn ext_equal_struct() {
    let f1 = Foo { a: seq![1, 2, 3], b: set!{4, 5, 6} };
    let f2 = Foo { a: seq![1, 2].push(3), b: set!{5, 6}.insert(4) };
    assert(f1.a =~= f2.a);  // succeeds
    // assert(f1 == f2);    // FAILS
    assert(f1 =~= f2);  // succeeds
}
// ANCHOR_END: ext_eq_struct

// ANCHOR: ext_eq_nested
proof fn ext_equal_nested() {
    let inner: Set<int> = set!{1, 2, 3};
    let s1: Seq<Set<int>> = seq![inner];
    let s2 = s1.update(0, s1[0].insert(1));
    let s3 = s1.update(0, s1[0].insert(2).insert(3));
    // assert(s2 == s3);  // FAILS
    // assert(s2 =~= s3); // FAILS
    assert(s2 =~~= s3);  // succeeds
    let s4: Seq<Seq<Set<int>>> = seq![s1];
    let s5: Seq<Seq<Set<int>>> = seq![s2];
    assert(s4 =~~= s5);  // succeeds
}
// ANCHOR_END: ext_eq_nested

// ANCHOR: ext_eq_fnspec
#[verifier::ext_equal]  // necessary for invoking =~= on the struct
struct Bar {
    a: spec_fn(int) -> int,
}

proof fn ext_equal_fnspec(n: int) {
    // basic case
    let f1 = (|i: int| i + 1);
    let f2 = (|i: int| 1 + i);
    // assert(f1 == f2); // FAILS
    assert(f1 =~= f2);  // succeeds
    // struct case
    let b1 = Bar { a: |i: int| if i == 1 { i } else { 1 } };
    let b2 = Bar { a: |i: int| 1int };
    // assert(b1 == b2); // FAILS
    assert(b1 =~= b2);  // succeeds
    // nested case
    let i1 = (|i: int| i + 2);
    let i2 = (|i: int| 2 + i);
    let n1: Seq<spec_fn(int) -> int> = seq![i1];
    let n2: Seq<spec_fn(int) -> int> = seq![i2];
    // assert(n1 =~= n2); // FAILS
    assert(n1 =~~= n2);  // succeeds
}
// ANCHOR_END: ext_eq_fnspec

fn main() {
}

} // verus!
