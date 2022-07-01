use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

fn compute_arith() {
    assert_by_compute((7 + 7 * 2 > 20) && (22 - 5 <= 10*10));
}

fn compute_ite() {
    assert_by_compute(9 == if true { 9 } else { 5 });
    // TODO: This fails the expr_to_pure_exp check, due to the overflow checks that are inserted
    // 1. Why doesn't this apply to compute_arith?
    // 2. Why isn't the mode inferred to be spec?
    // 3. Should we set the view_as_spec field in State to be true before calling expr_to_pure_exp?
    //assert_by_compute(9 == if (7 + 7 * 2 > 20) { 7 + 2 } else { 22 - 5 + 10*10 });
}
