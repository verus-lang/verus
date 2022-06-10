#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariant::*};

pub fn main() {
  #[proof] let u: u32 = 5;

  #[proof] let i = AtomicInvariant::new(u, |u: u32| u % 2 == 1, 0);

  open_atomic_invariant!(&i => inner => {
    if inner == 1 {
      inner = 3;
    }
  });

  #[proof] let j = AtomicInvariant::new(7, |u: u32| u % 2 == 1, 1);

  open_atomic_invariant!(&i => inner_i => {
    open_atomic_invariant!(&j => inner_j => {
      #[proof] let tmp = inner_i;
      inner_i = inner_j;
      inner_j = tmp;
    });
  });

  #[proof] let j = i.into_inner();
  assert(j % 2 == 1);
}
