use std::cell::UnsafeCell;
use std::mem::MaybeUninit;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use crate::pervasive::*;

// TODO Identifier should be some opaque type, not necessarily an int

// TODO implement: borrow, borrow_mut, take, swap, read_copy

// TODO figure out how Drop should work

//type Identifier = int;

#[verifier(external_body)]
pub struct PCell<V> {
  ucell: UnsafeCell<MaybeUninit<V>>,
}

#[proof]
#[verifier(unforgeable)]
pub struct Permission<V> {
  #[spec] pub pcell: int,
  #[spec] pub value: option::Option<V>,
}

pub struct PCellWithToken<V> {
  pub pcell: PCell<V>,
  #[proof] pub token: Permission<V>,
}

// TODO put these in impl once methods without 'self' are supported

//// new_empty
#[inline(always)]
#[verifier(external_body)]
fn new_empty_external<V>() -> PCell<V> {
  ensures(|p: PCell<V>| false);
  return PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
}

#[inline(always)]
pub fn new_empty<V>() -> PCellWithToken<V> {
  ensures(|pt : PCellWithToken<V>|
    equal(pt.token, Permission{ pcell: pt.pcell.view(), value: option::Option::None })
  );

  let p = new_empty_external();
  #[proof] let t = proof_from_false();
  PCellWithToken {pcell: p, token: t}
}

impl<V> PCell<V> {
  #[verifier(pub_abstract)]
  #[spec]
  pub fn view(&self) -> int {
    arbitrary()
  }

  //// Put

  #[inline(always)]
  #[verifier(external_body)]
  fn put_external(&self, v: V) {
    ensures(false);
    unsafe {
      *(self.ucell.get()) = MaybeUninit::new(v);
    }
  }

  #[inline(always)]
  #[verifier(returns(proof))]
  pub fn put(&self, v: V, #[proof] perm: Permission<V>) -> Permission<V> {
    requires([
        equal(self.view(), perm.pcell),
        equal(perm.value, option::Option::None),
    ]);
    ensures(|p: Permission<V>|
        equal(p.value, option::Option::Some(v))
    );

    self.put_external(v);

    perm
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

    return perm;
  }
  */
}
