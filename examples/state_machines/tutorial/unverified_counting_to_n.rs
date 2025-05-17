// rust_verify/tests/example.rs ignore --- ordinary rust, not verus

// ANCHOR: full
// Ordinary Rust code, not Verus

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::thread::spawn;

fn do_count(num_threads: u32) {
    // Initialize an atomic variable

    let atomic = AtomicU32::new(0);

    // Put it in an Arc so it can be shared by multiple threads.

    let shared_atomic = Arc::new(atomic);

    // Spawn `num_threads` threads to increment the atomic once.

    let mut handles = Vec::new();

    for _i in 0..num_threads {
        let handle = {
            let shared_atomic = shared_atomic.clone();
            spawn(move || {
                shared_atomic.fetch_add(1, Ordering::SeqCst);
            })
        };
        handles.push(handle);
    }

    // Wait on all threads. Exit if an unexpected condition occurs.

    for handle in handles.into_iter() {
        match handle.join() {
            Result::Ok(()) => {}
            _ => {
                return;
            }
        };
    }

    // Load the value, and assert that it should now be `num_threads`.

    let val = shared_atomic.load(Ordering::SeqCst);
    assert!(val == num_threads);
}

fn main() {
    do_count(20);
}
// ANCHOR_END: full
