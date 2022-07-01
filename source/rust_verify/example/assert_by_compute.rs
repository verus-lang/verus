use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

fn compute_arith(x:u64) {
    assert_by_compute((7 + 7 * 2 > 20) && (22 - 5 <= 10*10)); // true
    assert_by_compute(x * 0 == 0);  // 0 == 0
    // TODO: This currently produces: uClip(64, x) == x,
    // due to the same issue mentioned below
    assert_by_compute(x * 1 == x);  // x == x
}

fn compute_ite() {
    assert_by_compute(9 == if 7 > 3 { 9 } else { 5 });  // 9 == 9
    // TODO: The example below fails the expr_to_pure_exp check,
    // due to the overflow checks that are inserted.
    // They are inserted because the mode checker treats constants as Exec,
    // which leads to the arith being marked as Exec, and the mode checker
    // confirms that an Exec expression can be passed as a Spec arg,
    // but it doesn't "upgrade" the expression to Spec
    //assert_by_compute(9 == if (7 + 7 * 2 > 20) { 7 + 2 } else { 22 - 5 + 10*10 });
}
