// rust_verify/tests/example.rs ignore --- incomplete feature
use vstd::prelude::*;

verus! {

pub fn atomic_function<'a, T>(x: i32, _s: &'a str, _t: T) -> (y: i32)
    atomically (atom_upd) {
        type FunctionPred,
        (z: i32) -> (w: i32),
        requires z == 5,
        ensures w == 7,
    },
    requires x == 2,
    ensures y == 3,
{
    let tracked _: vstd::atomic::AtomicUpdate<i32, i32, _> = atom_upd;

    return x + 1;
}

pub fn atomic_call() {
    let x = 2;
    let y = atomic_function(x, "hi", ()) atomically |update| {
        let z = 5;
        let w = update(z);
    };
}

} // verus!
