#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
use builtin::int;
use builtin::SpecAdd;

fn main() {}

verus! {
    spec fn f(i: int) -> int {
        i + 1
    }

    spec fn g(i: int) -> int {
        f(i) + 1
    }

    proof fn test_f_behavior() {
        assert(f(0) == 1);
        assert(f(1) == 2);
        assert(f(-3) == -2);
    }

    proof fn test_g_behavior() {
        assert(g(0) == 2); // g(0) = f(0) + 1 = 1 + 1 = 2
        assert(g(1) == 3); // g(1) = f(1) + 1 = 2 + 1 = 3
        assert(g(-4) == -2); // g(-4) = f(-4) + 1 = -3 + 1 = -2
    }
}