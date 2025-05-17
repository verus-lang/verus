#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)]
use vstd::{pervasive::*, seq::*, seq_lib::*};

verus! {

spec fn max_int(x: int, y: int) -> int {
    if x > y {
        x
    } else {
        y
    }
}

// To enable recommends checking, use: spec(checked) instead of spec
spec fn seq_max_int(s: Seq<int>) -> int
    recommends
        s.len()
            > 0,  // without this, spec(checked) generates a recommends warning below

    decreases s.len(),
{
    let m = s[s.len() - 1];
    if s.len() <= 1 {
        m
    } else {
        max_int(m, seq_max_int(s.drop_last()))
    }
}

proof fn test(s: Seq<int>)
    requires
        seq_max_int(s)
            >= 0,  // without this, the assertion fails and there's a recommends note
{
    assert(seq_max_int(s) >= 0);
}

fn main() {
    proof {
        let s = seq![10, 20, 30, 25];
        reveal_with_fuel(seq_max_int, 4);
        assert(seq_max_int(s) == 30);
    }
}

// Usage of `spec_affirm`
spec fn some_predicate(a: nat) -> bool
    recommends
        a < 100,
{
    if (a >= 50) {
        let _ = spec_affirm(50 <= a && a < 100);
        a >= 75
    } else {
        let _ = spec_affirm(a < 40);  // spec(checked) would raise a recommends note here
        a < 25
    }
}

} // verus!
