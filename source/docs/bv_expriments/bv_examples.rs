use builtin::*;
mod pervasive;
use pervasive::*;

#[spec]
fn arith_sum_int(i: int) -> int {
    decreases(i);

    if i <= 0 { 0 } else { i + arith_sum_int(i - 1) }
}

#[proof]
fn arith_sum_test2() {
    // Instead of writing out intermediate assertions, 
    // we can instead boost the fuel setting
    reveal_with_fuel(arith_sum_int, 4);
    assert(arith_sum_int(3) == 6);
}

#[verifier(external)]
fn main() {
   //  let args = std::env::args();
   //  for arg in args {
   //      if let Ok(n) = arg.parse::<u64>() {
   //          println!("{}", run_arith_sum(n));
   //      }
   //  }
}
