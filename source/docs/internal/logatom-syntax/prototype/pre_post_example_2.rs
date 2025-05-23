use vstd::prelude::*;
use vstd::atomic::{PermissionU64, PAtomicU64};

verus! {

fn add_1(p: PAtomicU64, Tracked(perm): Tracked<PermissionU64>) -> ()
    // atomic_update: {
    //   (perm: PermissionU64) -> ()
    //   requires perm.view().patomic == p.id()
    //   ensures <expr>
    // }
{
    #[cfg(verus_keep_ghost)]
    /* will be syntax */ ::builtin::atomic_requires([
    /* will be syntax */    perm.view().patomic == p.id()
    /* will be syntax */ ]);

}

// fn main() {
//     let x = 4;
// 
//     let y = add_1(4);
//     
//     assert(y == 5);
// }

}