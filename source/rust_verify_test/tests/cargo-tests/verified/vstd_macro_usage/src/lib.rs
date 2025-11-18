use vstd::prelude::*;
use vstd::*;

verus! {

proof fn contradiction_test() {
    assert_by_contradiction!(1 == 0 + 1, {
        assert(false);
    });
}

proof fn map_test() {
    let m1 = map![1nat => true, 2 => false];
    let m2 = map![1nat => true, 2 => false];
    assert_maps_equal!(m1, m2);
}

proof fn seq_test() {
    let s1 = seq![true, false];
    let s2 = Seq::empty().push(true).push(false);
    assert_seqs_equal!(s1, s2);
}

proof fn calc_test(x: int, y: int, z: int) 
    requires x + y == z,
{
    calc! {
        (==)
        x + y; 
            {}
        z;
    }
}

pub fn do_something(x: u64, y: u64, z: u64) -> (w: u64)
    requires x + y == z,
{
    proof {
        calc_test(x as int, y as int, z as int);
    }
    if x < y {
        x
    } else {
        z
    }
}


} // verus!
