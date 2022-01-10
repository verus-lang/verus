#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};
use crate::pervasive::{atomics::*};

#[verifier(atomic)]
#[verifier(external_body)]
fn atomic_op() {
  opens_invariants_none();
}

#[verifier(external_body)]
fn non_atomic_op() {
  opens_invariants_none();
}

pub fn do_nothing(#[proof] i: Invariant<u8>) {
  open_invariant!(&i => inner => {
    atomic_op();
    //atomic_op();
  });
}

pub fn main() { }
