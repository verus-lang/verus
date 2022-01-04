// rust_verify/tests/example.rs expect-failures

#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};

/*
#[proof]
fn throw_away(#[proof] i: Invariant<u8>) {
}

pub fn do_nothing(#[proof] i: Invariant<u8>) {
  requires([
    i.inv(0)
  ]);
  open_invariant!(&i => inner => {
    throw_away(i);
  });
}
*/

pub fn X(#[proof] i: Invariant<u8>) {
  requires([
    i.inv(0)
  ]);
  open_invariant!(&i => inner => {
    #[proof] let x = 5;
    #[proof] let x = 6;
    inner = 0;
  });
}

pub fn nested(#[proof] i: Invariant<u8>) {
  requires([
    i.inv(0)
  ]);
  open_invariant!(&i => inner => {
    open_invariant!(&i => inner2 => {
      inner2 = 0;
    });
    inner = 0;
  });
}

pub fn do_nothing(#[proof] i: Invariant<u8>) {
  requires([
    i.inv(0)
  ]);
  open_invariant!(&i => inner => {
  });
}

pub fn inv_doesnt_hold(#[proof] i: Invariant<u8>) {
  requires([
    i.inv(0)
  ]);
  open_invariant!(&i => inner => {
    inner = 1;
  });
}

pub fn nested_good(#[proof] i: Invariant<u8>, #[proof] j: Invariant<u8>) {
  requires([
    i.inv(0),
    j.inv(1),
    i.namespace() == 0,
    j.namespace() == 1,
  ]);
  open_invariant!(&i => inner => {
    inner = 0;
    open_invariant!(&j => inner => {
      inner = 1;
    });
  });
}

#[proof]
pub fn callee_mask_empty() {
  opens_invariants_none(); // will not open any invariant
}

#[proof]
pub fn callee_mask_full() {
  opens_invariants_any(); // can open any invariant
}

pub fn t1(#[proof] i: Invariant<u8>) {
  open_invariant!(&i => inner => {
    callee_mask_empty();
  });
}

pub fn t2(#[proof] i: Invariant<u8>) {
  open_invariant!(&i => inner => {
    callee_mask_full(); // ERROR
  });
}
pub fn t3(#[proof] i: Invariant<u8>) {
  opens_invariants_none();
  open_invariant!(&i => inner => { // ERROR
  });
}

/*
#[spec]
pub fn open_inv_in_spec(i: Invariant<u8>) {
  open_invariant!(&i => inner => {
  });
}
*/

/*
#[spec]
pub fn inv_header_in_spec(i: Invariant<u8>) {
    opens_invariants_any();
}
*/

/*
pub fn blah(#[exec] i: Invariant<u8>) {
    open_invariant!(&i => inner => {
    });
}
*/

/*
pub fn exec_fn() { }

pub fn blah(#[proof] i: Invariant<u8>) {
    let mut exec_var = 0; 
    open_invariant!(&i => inner => {
        exec_fn();
    });
}
*/

pub fn main() {
}
