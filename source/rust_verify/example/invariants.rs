#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariant::*};

verus!{
struct ModPredicate { }
impl InvariantPredicate<int, u32> for ModPredicate {
    spec fn inv(k: int, v: u32) -> bool {
        v as int % 2 == k
    }
}
}

pub fn main() {
  #[proof] let u: u32 = 5;

  #[proof] let i: AtomicInvariant<int, u32, ModPredicate> = AtomicInvariant::new(
      verus_proof_expr!(1),
      u,
      verus_proof_expr!(0));

  open_atomic_invariant!(&i => inner => {
    if inner == 1 {
      inner = 3;
    }
  });

  #[proof] let j: AtomicInvariant<int, u32, ModPredicate> = AtomicInvariant::new(
      verus_proof_expr!(1),
      7,
      verus_proof_expr!(1));

  open_atomic_invariant!(&i => inner_i => {
    open_atomic_invariant!(&j => inner_j => {
      #[proof] let tmp = inner_i;
      inner_i = inner_j;
      inner_j = tmp;
    });
  });

  #[proof] let j = i.into_inner();

  assert(verus_proof_expr!(j % 2 == 1));
}
