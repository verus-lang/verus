use vstd::prelude::*;
use verus_state_machines_macros::*;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::thread::*;

verus! {

state_machine!{ Y {
            fields {
                pub x: int,
                pub y: int,
                pub z: int,
            }

            init!{
                initialize(x: int, y: int, z: int) {
                    init x = x;
                    init y = y;
                    require(y <= z);
                    if x == y {
                        init z = z;
                    } else {
                        init z = z + 1;
                    }
                }
            }

            transition!{
                tr1(b: bool, c: bool) {
                    require(b);
                    assert(pre.y <= pre.z);
                    require(c);
                    update z = pre.z + 1;
                }
            }

            transition!{
                tr2(b: bool, c: bool) {
                    if b {
                        update z = pre.z + 1;
                    } else {
                        assert(pre.y <= pre.z);
                    }
                    require(c);
                }
            }

            transition!{
                tr3(b: bool, c: bool) {
                    if b {
                        assert(pre.y <= pre.z);
                    } else {
                        let j = pre.z + 1;
                        update z = j;
                    }
                    require(c);
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool { self.y <= self.z }

            #[inductive(initialize)]
            fn init_inductive(post: Self, x: int, y: int, z: int) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self, b: bool, c: bool) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self, b: bool, c: bool) { }

            #[inductive(tr3)]
            fn tr3_inductive(pre: Self, post: Self, b: bool, c: bool) { }

}}


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

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 as int } else { 0 }) + (if self.inc_b { 1 as int } else { 0 })
        }

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
                update counter = pre.counter + 1;
                update inc_a = true;
            }
        }

        transition!{
            tr_inc_b() {
                require(!pre.inc_b);
                update counter = pre.counter + 1;
                update inc_b = true;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.counter < 0xffff_ffff;
            }
        }

        property!{
            finalize() {
                require(pre.inc_a);
                require(pre.inc_b);
                assert pre.counter == 2;
            }
        }

        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(pre: Self, post: Self) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(pre: Self, post: Self) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: Self) {
        }
    }
);

struct_with_invariants!{
    pub struct Global {
        // An AtomicU32 that matches with the `counter` field of the ghost protocol.
        pub atomic: AtomicU32<_, X::counter, _>,

        // The instance of the protocol that the `counter` is part of.
        pub instance: Tracked<X::Instance>,
    }

    spec fn wf(&self) -> bool {
        // Specify the invariant that should hold on the AtomicU32<X::counter>.
        // Specifically the ghost token (`g`) should have
        // the same value as the atomic (`v`).
        // Furthermore, the ghost token should have the appropriate `instance`.
        invariant on atomic with (instance) is (v: u32, g: X::counter) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }
    }
}


fn main() {
    // Initialize protocol
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(inc_a_token),
        Tracked(inc_b_token),
    ) = X::Instance::initialize();
    // Initialize the counter
    let tr_instance: Tracked<X::Instance> = Tracked(instance.clone());
    let atomic = AtomicU32::new(Ghost(tr_instance), 0, Tracked(counter_token));
    let global = Global { atomic, instance: Tracked(instance.clone()) };
    let global_arc = Arc::new(global);

    // Spawn threads

    // Thread 1
    let global_arc1 = global_arc.clone();
    let join_handle1 = spawn(
        (move || -> (new_token: Tracked<X::inc_a>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                // `inc_a_token` is moved into the closure
                let tracked mut token = inc_a_token;
                let globals = &*global_arc1;
                let _ =
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&c);
                            globals.instance.borrow().tr_inc_a(&mut c, &mut token); // atomic increment
                        }
                    );
                Tracked(token)
            }),
    );

    // Thread 2
    let global_arc2 = global_arc.clone();
    let join_handle2 = spawn(
        (move || -> (new_token: Tracked<X::inc_b>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                // `inc_b_token` is moved into the closure
                let tracked mut token = inc_b_token;
                let globals = &*global_arc2;
                let _ =
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&mut c);
                            globals.instance.borrow().tr_inc_b(&mut c, &mut token); // atomic increment
                        }
                    );
                Tracked(token)
            }),
    );

    // Join threads
    let tracked inc_a_token;
    match join_handle1.join() {
        Result::Ok(token) => {
            proof {
                inc_a_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };
    let tracked inc_b_token;
    match join_handle2.join() {
        Result::Ok(token) => {
            proof {
                inc_b_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };

    // Join threads, load the atomic again
    let global = &*global_arc;
    let x =
        atomic_with_ghost!(&global.atomic => load();
        ghost c => {
            instance.finalize(&c, &inc_a_token, &inc_b_token);
        }
    );

    assert(x == 2);
}

} // verus!
