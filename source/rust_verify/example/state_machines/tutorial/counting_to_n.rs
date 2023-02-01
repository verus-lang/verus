#![allow(unused_imports)]

// ANCHOR: full
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{atomic_ghost::*};
use crate::pervasive::{modes::*};
use crate::pervasive::{thread::*};
use crate::pervasive::{vec::*};
use state_machines_macros::tokenized_state_machine;
use crate::pervasive::result::*;
use std::sync::Arc;

verus_old_todo_no_ghost_blocks!{

// ANCHOR: fields
tokenized_state_machine!{
    X {
        fields {
            #[sharding(constant)]
            pub num_threads: nat,

            #[sharding(variable)]
            pub counter: int,

            #[sharding(count)]
            pub unstamped_tickets: nat,

            #[sharding(count)]
            pub stamped_tickets: nat,
        }
// ANCHOR_END: fields

// ANCHOR: inv
        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == self.stamped_tickets
            && self.stamped_tickets + self.unstamped_tickets == self.num_threads
        }
// ANCHOR_END: inv

// ANCHOR: init
        init!{
            initialize(num_threads: nat) {
                init num_threads = num_threads;
                init counter = 0;
                init unstamped_tickets = num_threads;
                init stamped_tickets = 0;
            }
        }
// ANCHOR_END: init

// ANCHOR: tr_inc
        transition!{
            tr_inc() {
                // Equivalent to:
                //    require(pre.unstamped_tickets >= 1);
                //    update unstampted_tickets = pre.unstamped_tickets - 1
                // (In any `remove` statement, the `>=` condition is always implicit.)
                remove unstamped_tickets -= (1);

                // Equivalent to:
                //    update stamped_tickets = pre.stamped_tickets + 1
                add stamped_tickets += (1);

                // These still use ordinary 'update' syntax, because `pre.counter`
                // uses the `variable` sharding strategy.
                assert(pre.counter < pre.num_threads);
                update counter = pre.counter + 1;
            }
        }
// ANCHOR_END: tr_inc

// ANCHOR: finalize
        property!{
            finalize() {
                // Equivalent to:
                //    require(pre.unstamped_tickets >= pre.num_threads);
                have stamped_tickets >= (pre.num_threads);

                assert(pre.counter == pre.num_threads);
            }
        }
// ANCHOR_END: finalize

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, num_threads: nat) { }

        #[inductive(tr_inc)]
        fn tr_inc_preserves(pre: Self, post: Self) {
        }
    }
}

struct_with_invariants!{
    pub struct Global {
        pub atomic: AtomicU32<_, X::counter, _>,
        #[verus::proof] pub instance: X::Instance,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (instance) is (v: u32, g: X::counter) {
            g@ === X::token![instance => counter => v as int]
        }

        predicate {
            self.instance.num_threads() < 0x100000000
        }
    }
}

fn do_count(num_threads: u32) {
    // Initialize protocol 

    #[verus::proof] let instance;
    #[verus::proof] let counter_token;
    #[verus::proof] let mut unstamped_tokens;
    #[verus::proof] let mut stamped_tokens;

    proof {
        #[verus::proof] let (Trk(instance0),
            Trk(counter_token0),
            Trk(unstamped_tokens0),
            Trk(stamped_tokens0)) = X::Instance::initialize(num_threads as nat);
        instance = instance0;
        counter_token = counter_token0;
        unstamped_tokens = unstamped_tokens0;
        stamped_tokens = stamped_tokens0;
    }

    // Initialize the counter

    let atomic = AtomicU32::new(instance, 0, counter_token);

    let global = Global { atomic, instance: instance.clone() };
    let global_arc = Arc::new(global);

    // ANCHOR: loop_spawn
    // Spawn threads

    let mut join_handles: Vec<JoinHandle<Proof<X::stamped_tickets>>> = Vec::new();

    let mut i = 0;
    while i < num_threads
        invariant
            0 <= i,
            i <= num_threads,
            unstamped_tokens@.count + i as int == num_threads as int,
            unstamped_tokens@.instance === instance,
            join_handles@.len() == i as int,
            forall |j: int, ret| 0 <= j && j < i ==>
                join_handles@.index(j).predicate(ret) ==>
                    ret.0@.instance === instance && ret.0@.count == 1,
            (*global_arc).wf(),
            (*global_arc).instance === instance,
    {
        #[verus::proof] let unstamped_token;
        proof {
            #[verus::proof] let (Trk(unstamped_token0), Trk(rest)) = unstamped_tokens.split(1 as nat);
            unstamped_tokens = rest;
            unstamped_token = unstamped_token0;
        }

        let global_arc = global_arc.clone();

        let join_handle = spawn(move || {
            ensures(|new_token: Proof<X::stamped_tickets>|
                new_token.0@.instance === instance
                    && new_token.0@.count == spec_cast_integer::<_, nat>(1)
            );

            #[verus::proof] let unstamped_token = unstamped_token;
            let globals = &*global_arc;

            #[verus::proof] let stamped_token;

            let _ = atomic_with_ghost!(
                &global_arc.atomic => fetch_add(1);
                update prev -> next;
                returning ret;
                ghost c => {
                    #[verus::proof] stamped_token =
                        global_arc.instance.tr_inc(&mut c, unstamped_token);
                }
            );

            Proof(stamped_token)
        });

        join_handles.push(join_handle);

        i = i + 1;
    }
    // ANCHOR_END: loop_spawn

    // ANCHOR: loop_join
    // Join threads

    let mut i = 0;
    while i < num_threads
        invariant
            0 <= i,
            i <= num_threads,
            stamped_tokens@.count == i as int,
            stamped_tokens@.instance === instance,
            join_handles@.len() as int + i as int == num_threads,
            forall |j: int, ret| 0 <= j && j < join_handles@.len() ==>
                #[trigger] join_handles@.index(j).predicate(ret) ==>
                    ret.0@.instance === instance && ret.0@.count == 1,
            (*global_arc).wf(),
            (*global_arc).instance === instance,
    {

        let join_handle = join_handles.pop();

        match join_handle.join() {
            Result::Ok(Proof(token)) => {
                stamped_tokens = stamped_tokens.join(token);
            }
            _ => { return; }
        };

        i = i + 1;
    }
    // ANCHOR_END: loop_join

    let global = &*global_arc;
    let x = atomic_with_ghost!(&global.atomic => load();
        ghost c => {
            instance.finalize(&c, &stamped_tokens);
        }
    );

    assert(x == num_threads);
}

fn main() {
    do_count(20);
}

}
// ANCHOR_END: full
