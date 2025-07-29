use vstd::prelude::*;

verus! {

fn atomic_function(x: i32) -> (y: i32)
    atomically (atom_upd) {
        (z: i32) -> (w: i32),
        requires z == 5,
        ensures w == 7,
    },
    requires x == 2,
    ensures y == 3,
{
    let tracked _: vstd::atomic::AtomicUpdate<i32, i32, ()> = atom_upd;

    return x + 1;
}

fn atomic_call() {
    let x = 2;
    let y = atomic_function(x) atomically |update| {
        let z: i32 = 5;
        let w: i32 = update(z);
    };
}

} // verus!
