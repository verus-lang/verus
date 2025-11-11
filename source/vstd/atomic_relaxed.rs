#![allow(unused_imports)]

use core::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI8, AtomicIsize, AtomicPtr, AtomicU16, AtomicU32,
    AtomicU8, AtomicUsize, Ordering,
};

#[cfg(target_has_atomic = "64")]
use core::sync::atomic::{AtomicI64, AtomicU64};

use super::atomic::*;
use super::modes::*;
use super::pervasive::*;
use super::prelude::*;

verus! {

#[verifier::external_body]
struct PAtomicRelaxedU32 {
    ato: core::sync::atomic::AtomicU32,
}

#[verifier::external_body]
tracked struct PermissionRelaxedU32 {
    no_copy: NoCopy,
    unused: u32,
}

ghost struct PermissionRelaxedDataU32 {
    patomic: int,
    value: u32,
}

impl PermissionRelaxedU32 {
    #[verifier::external_body]  /* vattr */
    uninterp spec fn view(self) -> PermissionRelaxedDataU32;

    closed spec fn is_for(&self, patomic: PAtomicRelaxedU32) -> bool {
        self.view().patomic == patomic.id()
    }

    closed spec fn points_to(&self, v: u32) -> bool {
        self.view().value == v
    }

    #[verifier::inline]
    closed spec fn value(&self) -> u32 {
        self.view().value
    }

    #[verifier::inline]
    closed spec fn id(&self) -> AtomicCellId {
        self.view().patomic
    }
}

// DANGER: UNSOUND
impl PAtomicRelaxedU32 {
    uninterp spec fn id(&self) -> int;

    #[inline(always)]
    #[verifier::external_body]
    const fn new(i: u32) -> (res: (PAtomicRelaxedU32, Tracked<PermissionRelaxedU32>))
        ensures
            equal(res.1@.view(), PermissionRelaxedDataU32 { patomic: res.0.id(), value: i }),
    {
        let p = PAtomicRelaxedU32 { ato: <core::sync::atomic::AtomicU32>::new(i) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier::external_body]  /* vattr */
    #[verifier::atomic]  /* vattr */
    fn fetch_add_wrapping(&self, Tracked(perm): Tracked<&mut PermissionRelaxedU32>, n: u32) -> (ret:
        u32)
        requires
            equal(self.id(), old(perm).view().patomic),
        ensures
            equal(old(perm).view().value, ret),
            perm.view().patomic == old(perm).view().patomic,
            perm.view().value as int == wrapping_add_u32(old(perm).view().value as int, n as int),
        opens_invariants none
        no_unwind
    {
        return self.ato.fetch_add(n, Ordering::Relaxed);
    }
}

} // verus!
