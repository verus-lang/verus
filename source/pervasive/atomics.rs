use std::sync::atomic::{AtomicU32, Ordering};

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

// TODO support all the different integer types

#[verifier(external_body)]
pub struct PAtomicU32 {
    ato: AtomicU32,
}

#[proof]
#[verifier(unforgeable)]
pub struct PermissionU32 {
    #[spec] pub patomic: int,
    #[spec] pub value: u32,
}

#[inline(always)]
#[verifier(external_body)]
fn new_atomic_u32_external(i: u32) -> PAtomicU32 {
    ensures(|p: PAtomicU32| false);
    return PAtomicU32 { ato: AtomicU32::new(i) };
}

#[inline(always)]
pub fn new_atomic_u32(i: u32) -> (PAtomicU32, Proof<PermissionU32>) {
    ensures(|res : (PAtomicU32, Proof<PermissionU32>)|
        equal(res.1, proof(PermissionU32{ patomic: res.0.view(), value: i }))
    );

    let p = new_atomic_u32_external(i);
    #[proof] let t = proof_from_false();
    (p, proof(t))
}

#[spec]
pub fn wrapping_add_u32(a: int, b: int) -> int {
    if a + b >= 0x100000000 {
        a + b - 0x100000000
    } else {
        a + b
    }
}

impl PermissionU32 {
    #[spec]
    fn is_for(&self, patomic: PAtomicU32) -> bool {
        self.patomic == patomic.view()
    }

    #[spec]
    fn points_to(&self, v: u32) -> bool {
        self.value == v
    }
}

impl PAtomicU32 {
  #[verifier(pub_abstract)]
  #[spec]
  pub fn view(&self) -> int {
    arbitrary()
  }

  #[inline(always)]
  #[verifier(external_body)]
  #[verifier(atomic)]
  pub fn load(&self, #[proof] perm: &PermissionU32) -> u32 {
    requires([
        equal(self.view(), perm.patomic),
    ]);
    ensures(|ret: u32| equal(perm.value, ret));
    opens_invariants_none();

    return self.ato.load(Ordering::SeqCst);
  }

  #[inline(always)]
  #[verifier(external_body)]
  #[verifier(atomic)]
  pub fn fetch_add(&self, #[proof] perm: &mut PermissionU32, n: u32) -> u32 {
    requires([
        equal(self.view(), old(perm).patomic),
    ]);
    ensures(|ret: u32| equal(old(perm).value, ret)
        && perm.patomic == old(perm).patomic
        && perm.value == wrapping_add_u32(old(perm).value, n)
    );
    opens_invariants_none();

    return self.ato.fetch_add(n, Ordering::SeqCst);
  }
}
