#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: fun_modes
spec fn f1(x: int) -> int {
    x / 2
}

proof fn f2(x: int) -> int {
    x / 2
}

// "exec" is optional, and is usually omitted
exec fn f3(x: u64) -> u64 {
    x / 2
}
// ANCHOR_END: fun_modes

/*
// ANCHOR: fun_modes2
fn f3(x: u64) -> u64 { x / 2 } // exec function
// ANCHOR_END: fun_modes2
*/

/*
// ANCHOR: spec_fun1
spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

fn test() {
    assert(min(10, 20) == 10); // succeeds
    assert(min(100, 200) == 100); // succeeds
}
// ANCHOR_END: spec_fun1
*/

// ANCHOR: spec_fun3
spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

spec fn min3(x: int, y: int, z: int) -> int {
    min(x, min(y, z))
}

fn compute_min3(x: u64, y: u64, z: u64) -> (m: u64)
    ensures
        m == min3(x as int, y as int, z as int),
{
    let mut m = x;
    if y < m {
        m = y;
    }
    if z < m {
        m = z;
    }
    m
}

fn test() {
    let m = compute_min3(10, 20, 30);
    assert(m == 10);
}

// ANCHOR_END: spec_fun3
/*
// ANCHOR: spec_fun_mod1
mod M1 {
    use builtin::*;

    pub open spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }
}

mod M2 {
    use builtin::*;
    use crate::M1::*;

    fn test() {
        assert(min(10, 20) == 10); // succeeds
    }
}
// ANCHOR_END: spec_fun_mod1

// ANCHOR: spec_fun_mod2
mod M1 {
    use builtin::*;

    pub closed spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }

    pub proof fn lemma_min(x: int, y: int)
        ensures
            min(x,y) <= x && min(x,y) <= y,
    {}
}

mod M2 {
    use builtin::*;
    use crate::M1::*;

    fn test() {
        assert(min(10, 20) == min(10, 20)); // succeeds
        assert(min(10, 20) == 10); // FAILS
        proof {
            lemma_min(10,20);
        }
        assert(min(10, 20) <= 10); // succeeds
    }
}
// ANCHOR_END: spec_fun_mod2
*/

/*
// ANCHOR: spec_fun_proof
mod M1 {
    use builtin::*;

    pub closed spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }

    pub proof fn lemma_min(x: int, y: int)
        ensures
            min(x, y) <= x,
            min(x, y) <= y,
            min(x, y) == x || min(x, y) == y,
    {
    }
}

mod M2 {
    use builtin::*;
    use crate::M1::*;

    proof fn test() {
        lemma_min(10, 20);
        assert(min(10, 20) == 10); // succeeds
        assert(min(100, 200) == 100); // FAILS
    }
}
// ANCHOR_END: spec_fun_proof
*/

// ANCHOR: spec_fun_proof_block1
fn test_consts_infer() {
    let u: u8 = 1;
    proof {
        let i: int = 2;
        let n: nat = 3;
        assert(0 <= u < i < n < 4);
    }
}
// ANCHOR_END: spec_fun_proof_block1

// ANCHOR: spec_fun_proof_block2
mod M1 {
    use builtin::*;

    pub closed spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }

    pub proof fn lemma_min(x: int, y: int)
        ensures
            min(x, y) <= x,
            min(x, y) <= y,
            min(x, y) == x || min(x, y) == y,
    {
    }
}

mod M2 {
    use builtin::*;
    use crate::M1::*;

    fn test() {
        proof {
            lemma_min(10, 20);
            lemma_min(100, 200);
        }
        assert(min(10, 20) == 10);  // succeeds
        assert(min(100, 200) == 100);  // succeeds
    }
}
// ANCHOR_END: spec_fun_proof_block2

/*
// ANCHOR: assert_by
mod M1 {
    use builtin::*;

    pub closed spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }

    pub proof fn lemma_min(x: int, y: int)
        ensures
            min(x, y) <= x,
            min(x, y) <= y,
            min(x, y) == x || min(x, y) == y,
    {
    }
}

mod M2 {
    use builtin::*;
    use crate::M1::*;

    fn test() {
        assert(min(10, 20) == 10) by {
            lemma_min(10, 20);
            lemma_min(100, 200);
        }
        assert(min(10, 20) == 10); // succeeds
        assert(min(100, 200) == 100); // FAILS
    }
}
// ANCHOR_END: assert_by
*/

/*
// ANCHOR: determinism
mod M1 {
    use builtin::*;

    pub closed spec fn s(i: int) -> int {
        i + 1
    }

    pub proof fn p(i: int) -> int {
        i + 1
    }
}

mod M2 {
    use builtin::*;
    use crate::M1::*;

    proof fn test_determinism() {
        let s1 = s(10);
        let s2 = s(10);
        assert(s1 == s2); // succeeds

        let p1 = p(10);
        let p2 = p(10);
        assert(p1 == p2); // FAILS
    }
}
// ANCHOR_END: determinism
*/

// ANCHOR: recommends1
spec fn f(i: nat) -> nat
    recommends
        i > 0,
{
    (i - 1) as nat
}

proof fn test1() {
    assert(f(0) == f(0));  // succeeds
}
// ANCHOR_END: recommends1

/*
// ANCHOR: recommends2
proof fn test2() {
    assert(f(0) <= f(1)); // FAILS
}
// ANCHOR_END: recommends2
*/

// ANCHOR: recommends3
spec fn caller1() -> nat {
    f(0)  // no note, warning, or error generated

}
// ANCHOR_END: recommends3

// ANCHOR: recommends4
spec(checked) fn caller2() -> nat {
    f(0)  // generates a warning because of "(checked)"

}
// ANCHOR_END: recommends4

/*
// ANCHOR: ghost_abilities0
fn divide_by_zero() {
    let x: u8 = 1;
    assert(x / 0 == x / 0); // succeeds in ghost code
    let y = x / 0; // FAILS in exec code
}
// ANCHOR_END: ghost_abilities0
*/

// ANCHOR: ghost_abilities1
mod MA {
    // does not implement Copy
    // does not allow construction by other modules
    pub struct S {
        private_field: u8,
    }

}

mod MB {
    use builtin::*;
    use crate::MA::*;

    // construct a ghost S
    spec fn make_S() -> S;

    // duplicate an S
    spec fn duplicate_S(s: S) -> (S, S) {
        (s, s)
    }
}
// ANCHOR_END: ghost_abilities1

/*
// ANCHOR: ghost_abilities2
fn test(s: S) {
    let pair = duplicate_S(s); // FAILS
}
// ANCHOR_END: ghost_abilities2
*/

// ANCHOR: const1
spec const SPEC_ONE: int = 1;

spec fn spec_add_one(x: int) -> int {
    x + SPEC_ONE
}

const ONE: u8 = 1;

fn add_one(x: u8) -> (ret: u8)
    requires
        x < 0xff,
    ensures
        ret == x + ONE,  // use "ONE" in spec code
{
    x + ONE  // use "ONE" in exec code
}
// ANCHOR_END: const1

fn main() {
}

} // verus!
