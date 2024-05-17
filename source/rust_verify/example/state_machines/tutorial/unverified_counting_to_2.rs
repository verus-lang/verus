// rust_verify/tests/example.rs ignore --- ordinary rust, not verus

// ANCHOR: full
// Ordinary Rust code, not Verus

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::thread::spawn;

fn main() {
    // Initialize an atomic variable

    let atomic = AtomicU32::new(0);

    // Put it in an Arc so it can be shared by multiple threads.

    let shared_atomic = Arc::new(atomic);

    // Spawn a thread to increment the atomic once.

    let handle1 = {
        let shared_atomic = shared_atomic.clone();
        spawn(move || {
            shared_atomic.fetch_add(1, Ordering::SeqCst);
        })
    };

    // Spawn another thread to increment the atomic once.

    let handle2 = {
        let shared_atomic = shared_atomic.clone();
        spawn(move || {
            shared_atomic.fetch_add(1, Ordering::SeqCst);
        })
    };

    // Wait on both threads. Exit if an unexpected condition occurs.

    match handle1.join() {
        Result::Ok(()) => {}
        _ => {
            return;
        }
    };

    match handle2.join() {
        Result::Ok(()) => {}
        _ => {
            return;
        }
    };

    // Load the value, and assert that it should now be 2.

    let val = shared_atomic.load(Ordering::SeqCst);
    assert!(val == 2);
}
// ANCHOR_END: full
