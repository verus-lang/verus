#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

// TODO: remove this example, it's complete non-sense

use vstd::prelude::*;
use vstd::*;

verus! {

pub enum UpdateResult<C, A> {
    Commit(C),
    Abort(A),
}

use UpdateResult::*;

impl<C, A> vstd::atomic::UpdateTry for UpdateResult<C, A> {
    open spec fn branch(self) -> vstd::atomic::UpdateControlFlow {
        match self {
            Commit(_) => vstd::atomic::UpdateControlFlow::Commit,
            Abort(_) => vstd::atomic::UpdateControlFlow::Abort,
        }
    }
}

pub fn atomic_function<T>(x: i32, _s: &str, _t: T) -> (y: i32)
    atomically (au) {
        type FunPred,
        (z: i32) -> (w: UpdateResult<i32, i32>),
        requires z == 5,
        ensures match w {
            Commit(t) => t == 7,
            Abort(t) => t == z,
        },
        outer_mask [ 2_int, 3_int ],
        inner_mask [ 2_int ],
    },
    requires x == 2,
    ensures y == 3,
{
    let tracked _: vstd::atomic::AtomicUpdate<i32, UpdateResult<i32, i32>, FunPred<T>> = au;
    assume(au.resolves());
    return x + 1;
}

pub fn middle(x: i32) -> (y: i32)
    atomically (atom_upd) {
        type MiddlePred,
        (z: i32) -> (w: Result<i32, i32>),
        requires z == 5,
        ensures match w {
            Ok(t) => t == 7,
            Err(t) => t == z,
        },
        outer_mask any,
        inner_mask [ 2_int, 3_int ],
    },
    requires x == 2,
{
    let tracked mut au = atom_upd;

    loop invariant au == atom_upd { break }

    atomic_function(x, "hi", ()) 'label: atomically |upd| -> (final_au)
        invariant au == atom_upd,
    {
        let tracked Tracked(res) = try_open_atomic_update!(au, a => {
            assert(a == 5);
            let tracked upd_res = upd(a);
            Tracked(match upd_res {
                Commit(x) => Ok(x),
                Abort(x) => Err(x),
            })
        });

        match res {
            Ok(_) => {
                assert(atom_upd.resolves());
                assert(final_au.resolves());
                break 'label;
            }

            Err(new_au) => {
                au = new_au;
                continue 'label;
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
