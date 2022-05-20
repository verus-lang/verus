#![allow(unused_imports)]

// ANCHOR: full
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariant::*};
use crate::pervasive::{atomic::*};
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
            self.counter == (if self.inc_a { 1 } else { 0 }) + (if self.inc_b { 1 } else { 0 })
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

        readonly!{
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

#[proof]
pub struct G {
    #[proof] pub counter: X::counter,
    #[proof] pub perm: PermissionU32,
}

impl G {
    #[spec]
    pub fn wf(self, instance: X::Instance, patomic: PAtomicU32) -> bool {
        equal(self.perm.patomic, patomic.id())
        && equal(self.perm.value as int, self.counter.value)
        && equal(self.counter.instance, instance)
    }
}

pub struct Global {
    pub atomic: PAtomicU32,
    #[proof] pub instance: X::Instance,
    #[proof] pub inv: Invariant<G>,
}

impl Global {
    #[spec]
    pub fn wf(self) -> bool {
        forall(|g: G| self.inv.inv(g) == g.wf(self.instance, self.atomic))
    }
}

//// thread 1

pub struct Thread1Data {
    pub globals: Arc<Global>,

    #[proof] pub token: X::inc_a,
}

impl Spawnable<Proof<X::inc_a>> for Thread1Data {
    #[spec]
    fn pre(self) -> bool {
        (*self.globals).wf()
        && equal(self.token.instance, (*self.globals).instance)
        && !self.token.value
    }

    #[spec]
    fn post(self, new_token: Proof<X::inc_a>) -> bool {
        equal(new_token.0.instance, (*self.globals).instance)
        && new_token.0.value
    }

    fn run(self) -> Proof<X::inc_a> {
        let Thread1Data { globals: globals, mut token } = self;
        let globals = &*globals;

        open_invariant!(&globals.inv => g => {
            #[proof] let G { counter: mut c, perm: mut p } = g;

            #[spec] let now_c = c;

            globals.instance.tr_inc_a(&mut c, &mut token); // atomic increment
            globals.atomic.fetch_add(&mut p, 1);

            g = G { counter: c, perm: p };
        });

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
        && equal(self.token.instance, (*self.globals).instance)
        && !self.token.value
    }

    #[spec]
    fn post(self, new_token: Proof<X::inc_b>) -> bool {
        equal(new_token.0.instance, (*self.globals).instance)
        && new_token.0.value
    }

    fn run(self) -> Proof<X::inc_b> {
        let Thread2Data { globals: globals, mut token } = self;
        let globals = &*globals;

        open_invariant!(&globals.inv => g => {
            #[proof] let G { counter: mut c, perm: mut p } = g;

            #[spec] let now_c = c;

            globals.instance.tr_inc_b(&mut c, &mut token); // atomic increment
            globals.atomic.fetch_add(&mut p, 1);

        
            g = G { counter: c, perm: p };
        });

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

  let (atomic, Proof(perm_token)) = PAtomicU32::new(0);

  #[proof] let at_inv: Invariant<G> = Invariant::new(
      G { counter: counter_token, perm: perm_token },
      |g: G| g.wf(instance, atomic),
      0);

  let global = Global { atomic, instance: instance.clone(), inv: at_inv };
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
  let x;
  open_invariant!(&global.inv => g => {
    #[proof] let G { counter: c3, perm: p3 } = g;

    x = global.atomic.load(&p3);
    instance.finalize(&c3, &inc_a_token, &inc_b_token);

    g = G { counter: c3, perm: p3 };
  });

  assert(equal(x, 2));
}
// ANCHOR_END: full
