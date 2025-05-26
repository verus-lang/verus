use vstd::prelude::*;
use vstd::atomic::{APermissionU64, APAtomicU64, wrapping_add_u64};
use vstd::logatom::AtomicUpdate;

verus! {

// fn add_1(p: PAtomicU64, Tracked(perm): Tracked<PermissionU64>) -> ()
//     /// requires perm.view().patomic == p.id()
//     // atomic_update: {
//     //   (perm: PermissionU64) -> ()
//     //   requires perm.view().patomic == p.id()
//     //   ensures <expr>
//     // }
// {
//     #[cfg(verus_keep_ghost_body)]
//     /* will be syntax */ ::builtin::atomic_requires([
//     /* will be syntax */    ::builtin::spec_eq(perm.view().patomic, p.id())
//     /* will be syntax */ ]);
// 
// }

fn fetch_add_plus_1(
    patomic: APAtomicU64,
    v: u64,

    /* (internal) */ Tracked(atomic_update): Tracked<AtomicUpdate<APermissionU64, APermissionU64>>,
    /* (internal) */ Tracked(perm): Tracked<APermissionU64>,
    ) -> (/* r: */ u64, /* new_perm: */ Tracked<APermissionU64>)

    // atomic_update: atomic_spec {
    //     (tracked perm: APermissionU64) -> (tracked new_perm: APermissionU64)
    //     requires // ATOMIC PRE
    //         perm.view().patomic == patomic.id(),
    //     ensures // ATOMIC POST
    //         new_perm.view().patomic == perm.id(),
    //         new_perm.view().value == wrapping_add_u64(
    //             perm.view().value,
    //             wrapping_add_u64(v, 1))
    // }   
    // ensures r == perm.view().value
{
    #[cfg(verus_keep_ghost_body)]
    /* will be syntax */ ::builtin::atomic_requires([
    /* will be syntax */    ::builtin::spec_eq(perm.view().patomic, patomic.id())
    /* will be syntax */ ]);

    #[cfg(verus_keep_ghost_body)]
    /* will be syntax */ ::builtin::ensures(|r: u64, new_perm: APermissionU64| [
    /* will be syntax */    ::builtin::spec_eq(new_perm.view().patomic, perm.view().patomic),
    /* will be syntax */    ::builtin::spec_eq(new_perm.view().value, wrapping_add_u64(
    /* will be syntax */        perm.view().value, wrapping_add_u64(v,spec_literal_integer("1"))))
    /* will be syntax */ ]);

    assume(false);
    unreached()
}

} // verus!
