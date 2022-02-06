#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};

pub fn main() {
  #[proof] let u: u32 = 5;

  #[proof] let i = Invariant::new(u, |u: u32| u % 2 == 1, 0);

  open_invariant!(&i => inner => {
    if inner == 1 {
      inner = 3;
    }
  });

  #[proof] let j = Invariant::new(7, |u: u32| u % 2 == 1, 1);

  open_invariant!(&i => inner_i => {
    open_invariant!(&j => inner_j => {
      #[proof] let tmp = inner_i;
      inner_i = inner_j;
      inner_j = tmp;
    });
  });

  #[proof] let j = i.into_inner();
  assert(j % 2 == 1);
}
