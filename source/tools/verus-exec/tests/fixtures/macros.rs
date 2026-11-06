#![allow(unused_imports, unused_variables, non_camel_case_types, dead_code)]
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use verus_state_machines_macros::*;
pub use vstd::{prelude, state_machine_internal, tokens};

tokenized_state_machine! {
    Tokens {
        fields {
            #[sharding(variable)]
            pub value: u32,
            #[sharding(count)]
            pub count: nat,
            #[sharding(persistent_count)]
            pub seen: nat,
        }
        init! {
            initialize() {
                init value = 0;
                init count = 0;
                init seen = 0;
            }
        }
    }
}

state_machine! {
    Plain {
        fields { pub value: u32 }
        init! { initialize() { init value = 0; } }
    }
}

tokenized_state_machine_vstd! {
    Internal {
        fields { #[sharding(variable)] pub value: u32 }
        init! { initialize() { init value = 0; } }
    }
}

verus! {
struct PlainWrap(u32);

fn unwrap_plain(PlainWrap(value): PlainWrap) -> u32 {
    value
}

struct ExecutableWrappers {
    value: u32,
    model: Ghost<u32>,
    token: Tracked<u32>,
}

fn make_wrappers(value: u32) -> (u32, Tracked<u32>, Ghost<u32>) {
    let tracked token = 3u32;
    let ghost model = 4u32;
    (value, Tracked(token), Ghost(model))
}

fn rewrap(Tracked(token,): Tracked<u32>, Ghost(r#type,): Ghost<u32>) -> (Tracked<u32>, Ghost<u32>) {
    (Tracked(token), Ghost::<u32>(r#type))
}

struct_with_invariants! {
    #[repr(C)]
    pub struct Counter {
        pub value: AtomicU32<_, (), _>,
    }
    closed spec fn wf(&self) -> bool {
        invariant on value is (v: u32, g: ()) { true }
    }
}

fn main() {
    let verus_tmp_token = 17u32;
    let r#verus_tmp_token_1 = 19u32;
    let (value, Tracked(mut token,), Ghost(model)) = make_wrappers(23);
    let (Tracked(next), Ghost(r#type)) = rewrap(Tracked(token), Ghost(model));
    let wrapped = ExecutableWrappers {
        value: unwrap_plain(PlainWrap(value)),
        model: Ghost(r#type),
        token: Tracked(next),
    };
    let ExecutableWrappers { value, model: Ghost(m), token: Tracked(t) } = wrapped;
    assert_eq!(value, 23);
    assert_eq!(verus_tmp_token, 17);
    assert_eq!(r#verus_tmp_token_1, 19);
    assert_eq!(core::mem::size_of::<ExecutableWrappers>(), core::mem::size_of::<u32>());
    let ghost_effects = std::cell::RefCell::new(Vec::<u32>::new());
    let discarded: Ghost<()> = Ghost({ ghost_effects.borrow_mut().push(99); panic!("ghost payload ran") });
    let discarded: Tracked<()> = Tracked({ ghost_effects.borrow_mut().push(100); panic!("tracked payload ran") });
    assert!(ghost_effects.borrow().is_empty());
    let _: (Ghost<u32>, Tracked<u32>) = (Ghost(m), Tracked(t));
    let counter = Counter {
        value: AtomicU32::new(Ghost::assume_new(), 10, Tracked::assume_new()),
    };
    let __verus_exec_atomic = &counter.value;
    let r#__verus_exec_operand = 3u32;
    let trace = std::cell::RefCell::new(Vec::new());
    let old = atomic_with_ghost!(
        { trace.borrow_mut().push(1); __verus_exec_atomic } =>
        compare_exchange(
            { trace.borrow_mut().push(2); 10 },
            { trace.borrow_mut().push(3); r#__verus_exec_operand }
        );
        update prev -> next;
        returning result;
        ghost g => { assert(true); }
    );
    assert_eq!(old, Ok(10));
    assert_eq!(*trace.borrow(), vec![1, 2, 3]);
    let value = atomic_with_ghost!(counter.value => load(); g => {});
    assert_eq!(value, 3);
    let value = atomic_with_ghost!(counter.value => fetch_add(2); ghost g => {});
    assert_eq!(value, 3);
    let value = atomic_with_ghost!(counter.value => fetch_sub(1); ghost g => {});
    assert_eq!(value, 5);
    let value = atomic_with_ghost!(counter.value => fetch_or(2); ghost g => {});
    assert_eq!(value, 4);
    let value = atomic_with_ghost!(counter.value => fetch_and(3); ghost g => {});
    assert_eq!(value, 6);
    let value = atomic_with_ghost!(counter.value => fetch_xor(1); ghost g => {});
    assert_eq!(value, 2);
    let value = atomic_with_ghost!(counter.value => fetch_max(8); ghost g => {});
    assert_eq!(value, 3);
    let value = atomic_with_ghost!(counter.value => fetch_min(7); ghost g => {});
    assert_eq!(value, 8);
    let value = atomic_with_ghost!(counter.value => swap(9); ghost g => {});
    assert_eq!(value, 7);
    let value = atomic_with_ghost!(counter.value => fetch_nand(3); ghost g => {});
    assert_eq!(value, 9);
    atomic_with_ghost!(counter.value => store(u32::MAX); ghost g => {});
    let value = atomic_with_ghost!(counter.value => fetch_add_wrapping(1); ghost g => {});
    assert_eq!(value, u32::MAX);
    let value = atomic_with_ghost!(counter.value => fetch_sub_wrapping(1); ghost g => {});
    assert_eq!(value, 0);
    let result = atomic_with_ghost!(counter.value => compare_exchange_weak(0, 1); ghost g => {});
    assert_eq!(result, Err(u32::MAX));
    atomic_with_ghost!(
        { trace.borrow_mut().push(4); &counter.value } => no_op();
        ghost g => {}
    );
    assert_eq!(*trace.borrow(), vec![1, 2, 3, 4]);
    println!(
        "atomic operations passed; token size {}; counter size {}; plain size {}; internal size {}",
        core::mem::size_of::<Tokens::value>(),
        core::mem::size_of::<Counter>(),
        core::mem::size_of::<Plain::State>(),
        core::mem::size_of::<Internal::value>(),
    );
}
}
