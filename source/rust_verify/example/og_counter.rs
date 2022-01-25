#![allow(unused_mut)] // TODO remove this once Verus allows removing 'mut'

#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};
use crate::pervasive::{atomics::*};
use crate::pervasive::{modes::*};

// LTS tokens (currently trusted)
// TODO, once we have state machine infrastructure, we can auto-generate these

#[proof]
#[verifier(unforgeable)]
pub struct Counter {
  #[spec] counter: int,
}

#[proof]
#[verifier(unforgeable)]
pub struct IncA {
  #[spec] done: bool,
}

#[proof]
#[verifier(unforgeable)]
pub struct IncB {
  #[spec] done: bool,
}

#[proof]
pub struct Init {
  #[proof] pub counter: Counter,
  #[proof] pub incA: IncA,
  #[proof] pub incB: IncB,
}

impl Init {
  #[spec]
  #[verifier(pub_abstract)]
  pub fn valid(self) -> bool {
      equal(self.counter.counter, 0)
      && !self.incA.done
      && !self.incB.done
  }
}

#[proof]
#[verifier(external_body)]
#[verifier(returns(proof))]
pub fn init_protocol() -> Init {
  ensures(|init: Init| init.valid());

  unimplemented!();
}

#[proof]
#[verifier(external_body)]
#[verifier(returns(proof))]
pub fn do_inc_a(#[proof] counter: &mut Counter, #[proof] inc_a: &mut IncA) {
  requires([
    !old(inc_a).done,
  ]);
  ensures([
    inc_a.done,
    equal(counter.counter, old(counter).counter + 1),
    counter.counter <= 2,
  ]);

  unimplemented!();
}

#[proof]
#[verifier(external_body)]
#[verifier(returns(proof))]
pub fn do_inc_b(#[proof] counter: &mut Counter, #[proof] inc_b: &mut IncB) {
  requires([
    !old(inc_b).done,
  ]);
  ensures([
    inc_b.done,
    equal(counter.counter, old(counter).counter + 1),
  ]);

  unimplemented!();
}

#[proof]
#[verifier(external_body)]
#[verifier(returns(proof))]
pub fn finish(#[proof] counter: &Counter, #[proof] inc_a: &IncA, #[proof] inc_b: &IncB) {
  requires([
    inc_a.done,
    inc_b.done,
  ]);
  ensures([
    equal(counter.counter, 2)
  ]);

  unimplemented!();
}

// Untrusted stuff starts here

#[proof]
pub struct G {
  #[proof] pub counter: Counter,
  #[proof] pub perm: PermissionU32,
}

impl G {
  #[spec]
  #[verifier(pub_abstract)]
  pub fn wf(self, patomic: PAtomicU32) -> bool {
    equal(self.perm.patomic, patomic.view()) && equal(self.perm.value as int, self.counter.counter)
  }
}

fn main() {
  // Initialize protocol 

  #[proof] let Init{
       counter: mut counter_token,
       incA: mut inc_a_token,
       incB: mut inc_b_token} = init_protocol();

  // Initialize the counter

  let mut at;
  #[proof] let mut perm_token;
  match new_atomic_u32(0) {
    (patomic, proof(token)) => {
      at = patomic;
      perm_token = token;
    }
  }

  #[proof] let at_inv: Invariant<G> = invariant_new(
      G { counter: counter_token, perm: perm_token },
      |g: G| g.wf(at),
      0);

  // TODO actually run these on separate threads

  // Thread 1 (gets access to inc_a_token)

  open_invariant!(&at_inv => g => {
    #[proof] let G { counter: mut c, perm: mut p } = g;

    at.fetch_add(&mut p, 1);
    do_inc_a(&mut c, &mut inc_a_token); // atomic increment

    g = G { counter: c, perm: p };
  });

  // Thread 2 (gets access to inc_b_token)

  open_invariant!(&at_inv => g => {
    #[proof] let G { counter: mut c, perm: mut p } = g;

    at.fetch_add(&mut p, 1);
    do_inc_b(&mut c, &mut inc_b_token); // atomic increment

    g = G { counter: c, perm: p };
  });

  // Join threads, load the atomic again

  // Since we recovered exclusive control of the invariant, we could destruct it
  // if we want to. Or we can just open the invariant block like normal.

  let mut x;
  open_invariant!(&at_inv => g => {
    #[proof] let G { counter: mut c, perm: mut p } = g;

    x = at.load(&p);
    finish(&c, &inc_a_token, &inc_b_token);

    g = G { counter: c, perm: p };
  });

  assert(equal(x, 2));
}
