use std::ptr::NonNull;
use std::mem::MaybeUninit;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

// TODO Identifier should be some opaque type, not necessarily an int

// TODO implement: borrow, borrow_mut, take, swap, read_copy

// TODO figure out how Drop should work

//type Identifier = int;

#[verifier(external_body)]
pub struct PPtr<#[verifier(strictly_positive)] V> {
  uptr: NonNull<MaybeUninit<V>>,
}

#[proof]
#[verifier(unforgeable)]
pub struct Permission<V> {
  #[spec] pub pptr: int,
  #[spec] pub value: option::Option<V>,
}

impl<V> PPtr<V> {
  #[inline(always)]
  #[verifier(external_body)]
  pub fn empty() -> (PPtr<V>, Proof<Permission<V>>) {
    ensures(|pt : (PPtr<V>, Proof<Permission<V>>)|
      equal(pt.1, Proof(Permission{ pptr: pt.0.view(), value: option::Option::None }))
    );
    opens_invariants_none();

    let p = PPtr {
      uptr: Box::leak(box MaybeUninit::uninit()).into(),
    };
    let Proof(t) = exec_proof_from_false();
    (p, Proof(t))
  }

  fndecl!(pub fn view(&self) -> int);

  #[inline(always)]
  #[verifier(external_body)]
  pub fn clone(&self) -> PPtr<V> {
      ensures(|pt: PPtr<V>| equal(pt.view(), self.view()));
      opens_invariants_none();

      PPtr { uptr: self.uptr }
  }

  #[inline(always)]
  #[verifier(external_body)]
  pub fn put(&self, v: V, #[proof] perm: &mut Permission<V>) {
    requires([
        equal(self.view(), old(perm).pptr),
        equal(old(perm).value, option::Option::None),
    ]);
    ensures([
        equal(perm.pptr, old(perm).pptr),
        equal(perm.value, option::Option::Some(v)),
    ]);
    opens_invariants_none();

    unsafe {
      *(self.uptr.as_ptr()) = MaybeUninit::new(v);
    }
  }

  #[inline(always)]
  #[verifier(external_body)]
  pub fn take(&self, #[proof] perm: &mut Permission<V>) -> V {
    requires([
        equal(self.view(), old(perm).pptr),
        old(perm).value.is_Some(),
    ]);
    ensures(|v: V| [
        equal(perm.pptr, old(perm).pptr),
        equal(perm.value, option::Option::None),
        equal(v, old(perm).value.get_Some_0()),
    ]);
    opens_invariants_none();

    unsafe {
        let mut m = MaybeUninit::uninit();
        std::mem::swap(&mut m, &mut *self.uptr.as_ptr());
        m.assume_init()
    }
  }

  #[inline(always)]
  #[verifier(external_body)]
  pub fn as_ref<'a>(&self, #[proof] perm: &'a Permission<V>) -> &'a V {
    requires([
        equal(self.view(), perm.pptr),
        perm.value.is_Some(),
    ]);
    ensures(|v: V|
        equal(v, perm.value.get_Some_0())
    );
    opens_invariants_none();
    
    unimplemented!();
    /*
    unsafe {
        (self.uptr.as_ref()).assume_init_ref()
    }
    */
  }

  #[inline(always)]
  #[verifier(external_body)]
  pub fn dispose(&self, #[proof] perm: Permission<V>) {
    requires([
        equal(self.view(), perm.pptr),
        equal(perm.value, option::Option::None),
    ]);
    opens_invariants_none();

    // TODO how to deallocate?
  }
}
