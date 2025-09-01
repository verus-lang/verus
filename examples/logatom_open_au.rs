// rust_verify/tests/example.rs ignore --- incomplete feature
use vstd::*;
use vstd::prelude::*;
use vstd::atomic::*;

verus! {

struct MyPredicate;

impl UpdatePredicate<i32, i32> for MyPredicate {
    open spec fn req(self, x: i32) -> bool {
        x == 2
    }

    open spec fn ens(self, x: i32, y: i32) -> bool {
        y == 3
    }
}

fn trivial(au: AtomicUpdate<i32, i32, MyPredicate>) {
    open_atomic_update!(au, x => {
        x + 1
    });
}

}
