use vstd::prelude::*;
use vstd::atomic::*;
use vstd::simple_pptr::*;
use vstd::invariant::*;

verus! {

// ################################################################
// ################################################################
// ################################################################

pub fn increment_bad(patomic: &PAtomicU64, Tracked(perm): Tracked<&mut PermissionU64>)
    requires
        perm.view().patomic == patomic.id(),
    ensures
        patomic.view().value == old(patomic).view().value + 1,
{
    let val = patomic.load(Tracked(&*perm));
    patomic.store(Tracked(perm), val + 1);
}

// ################################################################
// ################################################################
// ################################################################

pub fn increment_good(patomic: &PAtomicU64)
    atomic_spec au {
        (tracked old_perm: PermissionU64) -> (tracked new_perm: PermissionU64)
        requires
            old_perm.view().patomic == patomic.id(),
        ensures
            new_perm.view().id == old_perm.id(),
            new_perm.view().value == old_perm.view().value + 1,
    },
{
    let mut val = patomic.load();

    loop {
        let res = patomic.compare_exchange_weak(val, val + 1) atomically |update| {
            open_atomic_update!(au, |perm| {
                let ghost old_perm = perm.view();
                let (v, Tracked(new_perm)) = update(perm);
            });
        };

        match res {
            Ok(_) => break,
            Err(new) => val = new,
        }
    }
}

// ################################################################
// ################################################################
// ################################################################

} // verus!
