// rust_verify/tests/example.rs

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariant::*};

pub fn main() {
  #[proof] let u: u32 = 5;

  #[proof] let i = AtomicInvariant::new(u,
      verus_proof_expr!(|u: u32| u % 2 == 1),
      verus_proof_expr!(0));

  open_atomic_invariant!(&i => inner => {
    if inner == 1 {
      inner = 3;
    }
  });

  #[proof] let j = AtomicInvariant::new(7,
      verus_proof_expr!(|u: u32| u % 2 == 1),
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
