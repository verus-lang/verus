#![allow(unused_mut)] // TODO remove this once Verus allows removing 'mut'

#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};
use crate::pervasive::{atomic::*};
use crate::pervasive::{modes::*};
use state_machines_macros::concurrent_state_machine;

concurrent_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 } else { 0 }) + (if self.inc_b { 1 } else { 0 })
        }

        #[init]
        fn initialize(&self) {
            init(counter, 0);
            init(inc_a, false);
            init(inc_b, false);
        }

        #[transition]
        fn tr_inc_a(&self) {
            require(!self.inc_a);
            assert(self.counter <= 2);
            update(counter, self.counter + 1);
            update(inc_a, true);
        }

        #[transition]
        fn tr_inc_b(&self) {
            require(!self.inc_b);
            assert(self.counter <= 2);
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

  #[proof] let (inst,
      mut counter_token,
      mut inc_a_token,
      mut inc_b_token) = X_Instance::initialize();

  // Initialize the counter

  let (at, Proof(perm_token)) = PAtomicU32::new(0);

  #[proof] let at_inv: Invariant<G> = Invariant::new(
      G { counter: counter_token, perm: perm_token },
      |g: G| g.wf(inst, at),
      0);

  // TODO actually run these on separate threads

  // Thread 1 (gets access to inc_a_token)

  open_invariant!(&at_inv => g => {
    #[proof] let G { counter: mut c, perm: mut p } = g;

    inst.tr_inc_a(&mut c, &mut inc_a_token); // atomic increment
    at.fetch_add(&mut p, 1);

    g = G { counter: c, perm: p };
  });

  // Thread 2 (gets access to inc_b_token)

  open_invariant!(&at_inv => g => {
    #[proof] let G { counter: mut c2, perm: mut p2 } = g;

    inst.tr_inc_b(&mut c2, &mut inc_b_token); // atomic increment
    at.fetch_add(&mut p2, 1);

    g = G { counter: c2, perm: p2 };
  });

  // Join threads, load the atomic again

  // Since we recovered exclusive control of the invariant, we could destruct it
  // if we want to. Or we can just open the invariant block like normal.

  let mut x;
  open_invariant!(&at_inv => g => {
    #[proof] let G { counter: mut c3, perm: mut p3 } = g;

    x = at.load(&p3);
    inst.finalize(&c3, &inc_a_token, &inc_b_token);

    g = G { counter: c3, perm: p3 };
  });

  assert(equal(x, 2));
}
