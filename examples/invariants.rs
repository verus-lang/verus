#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::invariant::*;

verus! {

struct ModPredicate {}

impl InvariantPredicate<int, u32> for ModPredicate {
    closed spec fn inv(k: int, v: u32) -> bool {
        v as int % 2 == k
    }
}

pub fn main() {
    let tracked u: u32 = 5u32;
    let tracked i: AtomicInvariant<int, u32, ModPredicate> = AtomicInvariant::new(1, u, 0);
    open_atomic_invariant!(&i => inner => {
      proof {
          if inner == 1u32 {
              inner = 3u32;
          }
      }
  });
    let tracked j: AtomicInvariant<int, u32, ModPredicate> = AtomicInvariant::new(1, 7u32, 1);
    open_atomic_invariant!(&i => inner_i => {
      open_atomic_invariant!(&j => inner_j => {
          proof {
              let tracked tmp = inner_i;
              inner_i = inner_j;
              inner_j = tmp;
          }
      });
  });
    let tracked j = i.into_inner();
    assert(j % 2 == 1);
}

} // verus!
