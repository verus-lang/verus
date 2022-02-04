#![allow(unused_mut)] // TODO remove this once Verus allows removing 'mut'

#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};
use crate::pervasive::{atomics::*};
use crate::pervasive::{modes::*};
use state_machines_macros::concurrent_state_machine;

concurrent_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            counter: int,

            #[sharding(variable)]
            inc_a: bool,

            #[sharding(variable)]
            inc_b: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 } else { 0 }) + (if self.inc_b { 1 } else { 0 })
        }

        #[init]
        fn initialize(&self) {
            update(counter, 0);
            update(inc_a, false);
            update(inc_b, false);
        }

        #[transition]
        fn tr_inc_a(&self) {
            require(!self.inc_a);
            update(counter, self.counter + 1);
            update(inc_a, true);
        }

        #[transition]
        fn tr_inc_b(&self) {
            require(!self.inc_b);
            update(counter, self.counter + 1);
            update(inc_b, true);
        }

        #[readonly]
        fn finalize(&self) {
            require(self.inc_a);
            require(self.inc_b);
            assert(self.counter == 2);
        }

        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(self: X, post: X) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(self: X, post: X) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: X) {
        }

        #[safety(finalize_safety_1)]
        fn finalize_correct(pre: X) {
            // XXX TODO verus currently doesn't generate the right conditions here
        }
    }
);

#[proof]
pub struct G {
  #[proof] pub counter: X_counter,
  #[proof] pub perm: PermissionU32,
}

impl G {
  #[spec]
  pub fn wf(self, inst: X_Instance, patomic: PAtomicU32) -> bool {
    equal(self.perm.patomic, patomic.view()) && equal(self.perm.value as int, self.counter.counter)
    && equal(self.counter.instance, inst)
  }
}

fn main() {
  // Initialize protocol 

  #[proof] let (spec(inst),
      mut counter_token,
      mut inc_a_token,
      mut inc_b_token) = X_initialize();

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
      |g: G| g.wf(inst, at),
      0);

  // TODO actually run these on separate threads

  // Thread 1 (gets access to inc_a_token)

  open_invariant!(&at_inv => g => {
    assume(g.perm.value as int <= 2 as int);

    #[proof] let G { counter: mut c, perm: mut pho } = g;

    at.fetch_add(&mut pho, 1);
    X_tr_inc_a(inst, &mut c, &mut inc_a_token); // atomic increment

    g = G { counter: c, perm: pho };
  });

  // Thread 2 (gets access to inc_b_token)

  open_invariant!(&at_inv => gxxxx => {
    //assert(gxxxx.perm.value as int <= 1234 as int);
    #[proof] let G { counter: mut c, perm: mut pho } = gxxxx;

    at.fetch_add(&mut pho, 1);
    X_tr_inc_b(inst, &mut c, &mut inc_b_token); // atomic increment

    gxxxx = G { counter: c, perm: pho };
  });

  // Join threads, load the atomic again

  // Since we recovered exclusive control of the invariant, we could destruct it
  // if we want to. Or we can just open the invariant block like normal.

  let mut x;
  open_invariant!(&at_inv => g => {
    #[proof] let G { counter: mut c, perm: mut p } = g;

    x = at.load(&p);
    X_finalize(inst, &c, &inc_a_token, &inc_b_token);

    g = G { counter: c, perm: p };
  });

  assert(equal(x, 2));
}

fn X() {
  assert(false);
}
