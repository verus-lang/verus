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
        y == 5
    }
}

fn silly(au: AtomicUpdate<i32, i32, MyPredicate>) {
    open_atomic_update!(au, mut n => {
        n + 3
    });
}

}
