use std::cell::UnsafeCell;
use std::mem::MaybeUninit;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use crate::pervasive::*;

//type Identifier = int;

#[verifier(external_body)]
pub struct PCell<V> {
  ucell: UnsafeCell<MaybeUninit<V>>,
}

// TODO find a way to consolidate Permission and PermissionToken

#[spec]
pub struct Permission<V> {
  pub pcell: int,
  pub value: option::Option<V>,
}

#[verifier(external_body)]
#[proof]
pub struct PermissionToken<V> {
  dummy: std::marker::PhantomData<V>,
}

pub struct PCellWithToken<V> {
  pub pcell: PCell<V>,
  #[proof] pub token: PermissionToken<V>,
}

impl<V> PermissionToken<V> {
  #[verifier(pub_abstract)]
  #[spec]
  pub fn view(&self) -> Permission<V> {
    arbitrary()
  }
}

// TODO put these in impl:

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
    equal(pt.token.view(), Permission{ pcell: pt.pcell.view(), value: option::Option::None })
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
  pub fn put(&self, v: V, #[proof] perm: PermissionToken<V>) -> PermissionToken<V> {
    requires([
        equal(self.view(), perm.view().pcell),
        equal(perm.view().value, option::Option::None),
    ]);
    ensures(|p: PermissionToken<V>|
        equal(p.view().value, option::Option::Some(v))
    );

    self.put_external(v);

    perm
  }

  /*
  #[inline(always)]
  #[verifier(no_verify)]
  pub fn borrow(&self, perm: &'a PermissionToken<V>) -> &'a V {
    requires([
        equal(self.view(), perm.view().pcell),
        !equal(perm.view().value, None),
    ]);
    ensures(|p: PermissionToken<V>|
        equal(p.view().value, Some(v))
    );
    
    self.write_external(v);

    return perm;
  }
  */
}
