// rust_verify/tests/example.rs expect-failures

#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};

pub fn main() {
  #[proof] let u: u32 = 5;

  #[proof] let i = invariant_new(u, |u: u32| u % 2 == 1, 0);

  open_invariant!(&i => inner => {
    assert(i.inv(inner));
    assert(inner % 2 == 1); // TODO this fails
  });
}

/*
pub fn main() {
  #[proof] let u: u32 = 5;

  #[proof] let i = invariant_new(u, |u: u32| u % 2 == 1, 0);

  open_invariant!(&i => inner => {
    if inner == 1 {
      inner = 3;
    }
  });

  #[proof] let j = invariant_new(7, |u: u32| u % 2 == 1, 1);

  open_invariant!(&i => inner_i => {
    assert(i.inv(inner_i));
    assert(inner_i % 2 == 1);
    open_invariant!(&j => inner_j => {
      assert(inner_i % 2 == 1);
      #[proof] let tmp = inner_i;
      assert(tmp % 2 == 1);
      inner_i = inner_j;
      inner_j = tmp;
      assert(inner_j % 2 == 1);
    });
  });

  #[proof] let j = i.destruct();
  assert(j % 2 == 1);
}
*/
