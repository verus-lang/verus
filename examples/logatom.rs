use vstd::prelude::*;
use vstd::*;

verus! {

pub fn atomic_function<T>(x: i32, _s: &str, _t: T) -> (y: i32)
    atomically (au) {
        type FunPred,
        (z: i32) -> (w: i32),
        requires z == 5,
        ensures w == 7,
        outer_mask [ 2_int, 3_int ],
        inner_mask [ 2_int ],
    },
    requires x == 2,
    ensures y == 3,
{
    let tracked _: vstd::atomic::AtomicUpdate<i32, i32, FunPred<T>> = au;
    assume(au.resolves());
    return x + 1;
}

pub fn middle(x: i32) -> (y: i32)
    atomically (atom_upd) {
        type MiddlePred,
        (z: i32) -> (w: i32),
        requires z == 5,
        ensures w == 7,
        outer_mask any,
        inner_mask [ 2_int, 3_int ],
    },
    requires x == 2,
{
    atomic_function(x, "hi", ()) atomically |upd| {
        let res: Result<(), _> = try_open_atomic_update!(atom_upd, a => {
            assert(a == 5);
            let b = upd(a);
            assert(b == 7);
            Ok(b)
        });

        assert(res is Ok);
        assert(atom_upd.resolves());
    }
}

pub fn atomic_call() {
    let x = 2;
    let y = middle(x) atomically |update| {
        let tracked z = 5;
        assert(z == 5);
        let w = update(z);
        assert(w == 7);
    };
}

} // verus!
