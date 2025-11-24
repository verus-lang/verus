#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

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
        Err::<Tracked<PermissionU64>, Tracked<PermissionU64>>(Tracked(perm))
    });

    let tmp = maybe_au.unwrap_err();
    proof { au = tmp.get() };

    loop invariant au == atomic_update {
        let res;
        let maybe_au = try_open_atomic_update!(au, mut perm => {
            let ghost old_perm = perm;

            res = patomic.compare_exchange_weak(Tracked(&mut perm), val, val.wrapping_add(1));

            match &res {
                Ok(_) => Ok(Tracked(perm)),
                Err(_) => {
                    assert(perm@ == old_perm@);
                    assume(perm == old_perm);

                    Err(Tracked(perm))
                },
            }
        });

        match res {
            Ok(_) => {
                assert(atomic_update.resolves());
                break
            }

            Err(new) => {
                let tmp = maybe_au.unwrap_err();
                proof { au = tmp.get() };

                val = new;
            },
        }
    }
}

} // verus!
