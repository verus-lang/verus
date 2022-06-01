#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use pervasive::*;
mod pervasive;

fndecl!(fn f(x: nat, y: nat) -> bool);
fndecl!(fn g(x: nat) -> bool);
fndecl!(fn j(x: nat) -> bool);

//#[proof]
//fn quantifier_example() {
//    requires(forall(|x| g(x)));
//    ensures(exists(|y| g(y)));
//    let w = choose(|z| g(z));
//    assert(g(w));
//}
//
//#[proof] 
//fn choose_example() {
//    requires(exists(|x| g(x)));
//
//    let z = choose(|y| g(y));
//    assert(g(z));
//}
//
//#[proof]
//fn cost_example() {
//    requires([f(1,2),
//              forall(|x, y| #[trigger] f(x, y) == (g(x) && g(y))),
//              forall(|z| #[trigger] g(z) == j(z + 2))]);
//    assert(j(3) && j(4));
//}
//
//
//#[proof] 
//fn trigger_forever() {
//   requires(forall(|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) >>= (#[trigger] f(x, y))));
//   ensures(forall(|x: nat, y: nat| x > 2318 && y < 100 >>= f(x, y)));
//}
//
//fndecl!(fn h(x:nat, y: nat) -> bool);
//
//// Split the triggering over two different quantifiers
//#[proof] 
//fn trigger_forever2() {
//   requires([forall(|x: nat| g(x)),
//             forall(|x: nat, y: nat| h(x, y) == f(x, y)),
//             forall(|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) >>= (#[trigger] f(x, y)))]);
//   ensures(forall(|x: nat, y: nat| x > 2318 && y < 100 >>= h(x, y)));
//   assert(g(4));
//}
//
#[exec]
fn simple_loop() {
    ensures(forall(|x| 0 <= x && x < 10 >>= g(x)));
    let mut x:u32 = 0;
    while (x < 10) {
        invariant([0 <= x && x <= 10,
                  forall(|i:u32| 0 <= i && i < x >>= g(i))]);
        decreases(x);

        assume(g(x));
        x = x + 1;
    }
}

//#[exec]
//fn bad_loop() {
//    requires(forall(|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) >>= (#[trigger] f(x, y))));
//    let mut x = 10;
//    while (x > 10) {
//        invariant(forall(|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) >>= (#[trigger] f(x, y))));
//        decreases(x);
//
//        x = x - 1;
//        assert(forall(|x: nat, y: nat| x > 2318 && y < 100 >>= f(x, y)));
//    }
//}

fn main() {}
