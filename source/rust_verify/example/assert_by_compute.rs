use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

fn compute_simple() {
    assert_by_compute((7 + 7 * 2 > 20) && (22 - 5 <= 10*10));
}
