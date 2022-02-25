use std::cell::UnsafeCell;
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
pub struct PCell<#[verifier(strictly_positive)] V> {
  ucell: UnsafeCell<MaybeUninit<V>>,
}

#[proof]
#[verifier(unforgeable)]
pub struct Permission<V> {
  #[spec] pub pcell: int,
  #[spec] pub value: option::Option<V>,
}

impl<V> PCell<V> {
  #[inline(always)]
  #[verifier(external_body)]
  pub fn empty() -> (PCell<V>, Proof<Permission<V>>) {
    ensures(|pt : (PCell<V>, Proof<Permission<V>>)|
      equal(pt.1, Proof(Permission{ pcell: pt.0.view(), value: option::Option::None }))
    );

    let p = PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
    let Proof(t) = exec_proof_from_false();
    (p, Proof(t))
  }

  fndecl!(pub fn view(&self) -> int);

  //// Put

  #[inline(always)]
  #[verifier(external_body)]
  fn put_external(&self, v: V) {
    ensures(false);
    opens_invariants_none();
    unsafe {
      *(self.ucell.get()) = MaybeUninit::new(v);
    }
  }

  #[inline(always)]
  pub fn put(&self, v: V, #[proof] perm: &mut Permission<V>) {
    requires([
        equal(self.view(), old(perm).pcell),
        equal(old(perm).value, option::Option::None),
    ]);
    ensures(
        equal(perm.pcell, old(perm).pcell) &&
        equal(perm.value, option::Option::Some(v))
    );
    opens_invariants_none();

    self.put_external(v);
  }

  #[inline(always)]
  #[verifier(external_body)]
  pub fn take(&self, #[proof] perm: &mut Permission<V>) -> V {
    requires([
        equal(self.view(), old(perm).pcell),
        old(perm).value.is_Some(),
    ]);
    ensures(|v: V| [
        equal(perm.pcell, old(perm).pcell),
        equal(perm.value, option::Option::None),
        equal(v, old(perm).value.get_Some_0()),
    ]);
    opens_invariants_none();

    unimplemented!();
  }


  /*
  #[inline(always)]
  #[verifier(no_verify)]
  pub fn borrow(&self, perm: &'a Permission<V>) -> &'a V {
    requires([
        equal(self.view(), perm.view().pcell),
        !equal(perm.view().value, None),
    ]);
    ensures(|p: Permission<V>|
        equal(p.view().value, Some(v))
    );
    
    self.write_external(v);

    perm
  }
  */
}
