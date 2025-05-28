#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use vstd::{calc_macro::*, prelude, seq::*, seq_lib::*};

verus! {

fn main() {
}

proof fn calc_example_usage() {
    let a: Seq<u8> = seq![1u8, 2u8];
    let b: Seq<u8> = seq![1u8];
    let c: Seq<u8> = seq![2u8];
    let d: Seq<u8> = seq![1u8, 2u8];
    calc! {
        (==)
        a; (==) {
            assert_seqs_equal!(a == b + c);
        }
        b + c; {
            assert_seqs_equal!(b + c == d);
        }
        d;
    };
    calc! {
        (<=)
        (2 as int); (==) {}
        3 - 1; {}
        5;
    };
    calc! {
        (==>)
        (5 > 4); (==) {}
        (4 >= 4); (<==>) {}
        (2 > 1); (==>) {}
        (1 > 0); {}
        true;
    };
    calc! {
        (==>)
        false; {}
        true;
    };
}

} // verus!
