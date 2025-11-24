#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

proof fn tracked_unwrap_err<T, E>(tracked this: Result<T, E>) -> (tracked out: E)
    requires
        this is Err,
    ensures
        Err::<T, E>(out) == this,
{
    match this {
        Err(out) => out,
        _ => proof_from_false(),
    }
}

// pub fn increment_bad(patomic: &PAtomicU64, Tracked(perm): Tracked<&mut PermissionU64>)
//     requires
//         perm.view().patomic == patomic.id(),
//     ensures
//         patomic.view().value == old(patomic).view().value + 1,
// {
//     let val = patomic.load(Tracked(&*perm));
//     patomic.store(Tracked(perm), val + 1);
// }

pub fn increment_good(patomic: &PAtomicU64)
    atomically (atomic_update) {
        type IncrementPred,
        (old_perm: PermissionU64) -> (new_perm: PermissionU64),
        requires
            old_perm@.patomic == patomic.id(),
        ensures
            new_perm@.patomic == old_perm@.patomic,
            new_perm@.value == old_perm@.value.wrapping_add(1),
        outer_mask any,
        inner_mask any,
    },
{
    let tracked mut au = atomic_update;

    let mut val;
    let maybe_au = try_open_atomic_update!(au, perm => {
        val = patomic.load(Tracked(&perm));
        Tracked(Err(perm))
    });

    proof { au = tracked_unwrap_err(maybe_au.get()) };

    loop invariant
        au == atomic_update,
    {
        let res;
        let maybe_au = try_open_atomic_update!(au, mut perm => {
            let ghost old_perm = perm;

            res = patomic.compare_exchange_weak(Tracked(&mut perm), val, val.wrapping_add(1));

            Tracked(match &res {
                Ok(_) => Ok(perm),
                Err(_) => {
                    assert(perm@ == old_perm@);
                    assume(perm == old_perm);

                    Err(perm)
                },
            })
        });

        match res {
            Ok(_) => {
                assert(atomic_update.resolves());
                break
            }

            Err(new) => {
                proof { au = tracked_unwrap_err(maybe_au.get()) };

                val = new;
            },
        }
    }
}

} // verus!
