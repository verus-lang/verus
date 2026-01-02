// rust_verify/tests/example.rs ignore --- broken

#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

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
    let tracked mut au = atom_upd;

    loop invariant au == atom_upd { break }

    atomic_function(x, "hi", ()) atomically |upd|
        invariant au == atom_upd,
    {
        let tracked Tracked(res) = try_open_atomic_update!(au, a => {
            assert(a == 5);
            let tracked res = upd(a);
            Tracked(res)
        });

        match res {
            Ok(_) => {
                assert(atom_upd.resolves());
                break;
            }

            Err(new_au) => {
                au = new_au;
                //continue;
            }
        }
    }
}

pub fn atomic_call() {
    let x = 2;
    let y = middle(x) atomically |update| {
        let tracked z = 5;
        assert(z == 5);
        let w = update(z);
        //assert(w == 7);
        if w is Ok { break }
    };
}

} // verus!
