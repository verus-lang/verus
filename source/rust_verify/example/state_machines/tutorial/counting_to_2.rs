#![allow(unused_imports)]

// ANCHOR: full
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{atomic_ghost::*};
use crate::pervasive::{modes::*};
use crate::pervasive::{thread::*};
use state_machines_macros::tokenized_state_machine;
use crate::pervasive::result::*;
use std::sync::Arc;

tokenized_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,
        }

        // ANCHOR: inv 
        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 as int } else { 0 }) + (if self.inc_b { 1 as int } else { 0 })
        }
        // ANCHOR_END: inv 

        init!{
            initialize() {
                init counter = 0;
                init inc_a = false;
                init inc_b = false;
            }
        }

        transition!{
            tr_inc_a() {
                require(!pre.inc_a);
                assert(pre.counter <= 2);
                update counter = pre.counter + 1;
                update inc_a = true;
            }
        }

        transition!{
            tr_inc_b() {
                require(!pre.inc_b);
                assert(pre.counter <= 2);
                update counter = pre.counter + 1;
                update inc_b = true;
            }
        }

        property!{
            finalize() {
                require(pre.inc_a);
                require(pre.inc_b);
                assert pre.counter == 2;
            }
        }

        // ANCHOR: inv_proof
        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(pre: Self, post: Self) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(pre: Self, post: Self) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: Self) {
        }
        // ANCHOR_END: inv_proof
    }
);

// ANCHOR: global_struct
pub struct Global {
    // An AtomicU32 that matches with the `counter` field of the ghost protocol.
    pub atomic: AtomicU32<X::counter>,

    // The instance of the protocol that the `counter` is part of.
    #[proof] pub instance: X::Instance,
}

impl Global {
    // Specify the invariant that should hold on the AtomicU32<X::counter>.
    // Specifically the ghost token (`g`) should have
    // the same value as the atomic (`v`).
    // Furthermore, the ghost token should have the appropriate `instance`.

    #[spec]
    pub fn wf(self) -> bool {
        self.atomic.has_inv(|v, g|
            equal(g, X![self.instance => counter => v as int])
        )
    }
}
// ANCHOR_END: global_struct

//// thread 1

pub struct Thread1Data {
    pub globals: Arc<Global>,

    #[proof] pub token: X::inc_a,
}

impl Spawnable<Proof<X::inc_a>> for Thread1Data {
    #[spec]
    fn pre(self) -> bool {
        (*self.globals).wf()
        && equal(self.token,
            X![(*self.globals).instance => inc_a => false]
        )
    }

    #[spec]
    fn post(self, new_token: Proof<X::inc_a>) -> bool {
        equal(new_token.0,
            X![(*self.globals).instance => inc_a => true]
        )
    }

    fn run(self) -> Proof<X::inc_a> {
        let Thread1Data { globals: globals, mut token } = self;
        let globals = &*globals;

        let _ = atomic_with_ghost!(&globals.atomic => fetch_add(1);
            ghost c => {
                globals.instance.tr_inc_a(&mut c, &mut token); // atomic increment
            }
        );

        Proof(token)
    }
}

//// thread 2

pub struct Thread2Data {
    pub globals: Arc<Global>,

    #[proof] pub token: X::inc_b,
}

impl Spawnable<Proof<X::inc_b>> for Thread2Data {
    #[spec]
    fn pre(self) -> bool {
        (*self.globals).wf()
        && equal(self.token,
            X![(*self.globals).instance => inc_b => false]
        )
    }

    #[spec]
    fn post(self, new_token: Proof<X::inc_b>) -> bool {
        equal(new_token.0,
            X![(*self.globals).instance => inc_b => true]
        )
    }

    fn run(self) -> Proof<X::inc_b> {
        let Thread2Data { globals: globals, mut token } = self;
        let globals = &*globals;

        let _ = atomic_with_ghost!(&globals.atomic => fetch_add(1);
            ghost c => {
                globals.instance.tr_inc_b(&mut c, &mut token); // atomic increment
            }
        );

        Proof(token)
    }
}

fn main() {
  // Initialize protocol 

  #[proof] let (instance,
      counter_token,
      inc_a_token,
      inc_b_token) = X::Instance::initialize();

  // Initialize the counter

  let atomic = AtomicU32::new(0, counter_token, |v, g| {
      equal(g.instance, instance) && equal(g.value, v as int)
  });

  let global = Global { atomic, instance: instance.clone() };
  let global_arc = Arc::new(global);

  // Spawn threads

  let thread1_data = Thread1Data { globals: global_arc.clone(), token: inc_a_token };
  let join_handle1 = spawn(thread1_data);

  let thread2_data = Thread2Data { globals: global_arc.clone(), token: inc_b_token };
  let join_handle2 = spawn(thread2_data);

  // Join threads

  #[proof] let inc_a_token;
  match join_handle1.join() {
      Result::Ok(Proof(token)) => { inc_a_token = token; }
      _ => { return; }
  };

  #[proof] let inc_b_token;
  match join_handle2.join() {
      Result::Ok(Proof(token)) => { inc_b_token = token; }
      _ => { return; }
  };

  // Join threads, load the atomic again

  let global = &*global_arc;
  
  let x = atomic_with_ghost!(&global.atomic => load();
      ghost c => {
          instance.finalize(&c, &inc_a_token, &inc_b_token);
      }
  );

  assert(equal(x, 2));
}
// ANCHOR_END: full
