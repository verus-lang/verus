#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::rwlock::*;

verus!{

fn example1() {
    // We can create a lock with an invariant: `v == 5 || v == 13`.
    // Thus only 5 or 13 can be stored in the lock.
    let lock = RwLock::<u64, spec_fn(u64) -> bool>::new(5, Ghost(|v| v == 5 || v == 13));

    let (val, write_handle) = lock.acquire_write();
    assert(val == 5 || val == 13);
    write_handle.release_write(13);

    let read_handle1 = lock.acquire_read();
    let read_handle2 = lock.acquire_read();

    // We can take multiple read handles at the same time:

    let val1 = read_handle1.borrow();
    let val2 = read_handle2.borrow();

    // RwLock has a lemma that both read handles have the same value:

    proof { ReadHandle::lemma_readers_match(&read_handle1, &read_handle2); }
    assert(*val1 == *val2);

    read_handle1.release_read();
    read_handle2.release_read();
}

// Using higher-order functions is often cumbersome, we can use traits instead.

struct FixedParity {
    pub parity: int,
}

impl RwLockPredicate<u64> for FixedParity {
    open spec fn inv(self, v: u64) -> bool {
        v % 2 == self.parity
    }
}

fn example2() {
    let lock_even = RwLock::<u64, FixedParity>::new(20, Ghost(FixedParity { parity: 0 }));
    let lock_odd = RwLock::<u64, FixedParity>::new(23, Ghost(FixedParity { parity: 1 }));

    let read_handle_even = lock_even.acquire_read();
    let val_even = *read_handle_even.borrow();
    assert(val_even % 2 == 0);

    let read_handle_odd = lock_odd.acquire_read();
    let val_odd = *read_handle_odd.borrow();
    assert(val_odd % 2 == 1);
}

pub fn main() {
    example1();
    example2();
}

}
