#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

pub fn increment_bad(patomic: &PAtomicU64, Tracked(perm): Tracked<&mut PermissionU64>)
    requires
        old(perm)@.patomic == patomic.id(),
    ensures
        perm@.patomic == old(perm)@.patomic,
        perm@.value == old(perm)@.value.wrapping_add(1),
{
    let val = patomic.load(Tracked(&*perm));
    patomic.store(Tracked(perm), val.wrapping_add(1));
}

pub fn increment_good(patomic: &PAtomicU64)
    atomically (atomic_update) {
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

    let mut curr;
    let wrapped_au = peek_atomic_update!(au, perm => {
        curr = patomic.load(Tracked(&perm));
        Tracked(perm)
    });

    proof { au = wrapped_au.get() };

    loop invariant au == atomic_update {
        let next = curr.wrapping_add(1);

        let res;
        let maybe_au = try_open_atomic_update!(au, mut perm => {
            let ghost prev = perm;

            res = patomic.compare_exchange_weak(Tracked(&mut perm), curr, next);

            Tracked(match res is Ok {
                true => Ok(perm),
                false => {
                    assert(perm@ == prev@);
                    assert(perm == prev) by {
                        perm.view_bijective();
                        prev.view_bijective();
                    }

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
                proof { au = maybe_au.get().tracked_unwrap_err() };
                curr = new;
            },
        }
    }
}

} // verus!
