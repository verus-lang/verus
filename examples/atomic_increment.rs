#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

pub fn increment_bad(var: &PAtomicU64, Tracked(perm): Tracked<&mut PermissionU64>)
    requires
        old(perm)@.patomic == var.id(),
    ensures
        perm@.patomic == old(perm)@.patomic,
        perm@.value == old(perm)@.value.wrapping_add(1),
{
    let val = var.load(Tracked(&*perm));
    var.store(Tracked(perm), val.wrapping_add(1));
}

pub fn increment_good(var: &PAtomicU64)
    atomically (atomic_update) {
        (old_perm: PermissionU64) -> (new_perm: PermissionU64),
        requires
            old_perm@.patomic == var.id(),
        ensures
            new_perm@.patomic == old_perm@.patomic,
            new_perm@.value == old_perm@.value.wrapping_add(1),
        outer_mask any,
    },
{
    let tracked mut au = atomic_update;

    let mut curr;
    let wrapped_au = peek_atomic_update!(au, perm => {
        curr = var.load(Tracked(&perm));
        Tracked(perm)
    });

    proof { au = wrapped_au.get() };

    loop invariant au == atomic_update {
        let next = curr.wrapping_add(1);

        let res;
        let maybe_au = try_open_atomic_update!(au, mut perm => {
            let ghost prev = perm;

            res = var.compare_exchange_weak(Tracked(&mut perm), curr, next);

            Tracked(match res {
                Ok(_) => Ok(perm),
                Err(_) => Err(perm),
            })
        });

        match res {
            Ok(_) => {
                assert(atomic_update.resolves());
                break;
            }

            Err(new) => {
                proof { au = maybe_au.get().tracked_unwrap_err() };
                curr = new;
            },
        }
    }
}

} // verus!
