// rust_verify/tests/example.rs ignore --- ordianary rust, not verus

// ANCHOR: full
// Ordinary Rust code, not Verus

use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

// ANCHOR: queue
struct Queue<T> {
    buffer: Vec<UnsafeCell<MaybeUninit<T>>>,
    head: AtomicU64,
    tail: AtomicU64,
}
// ANCHOR_END: queue

// ANCHOR: producer_consumer
pub struct Producer<T> {
    queue: Arc<Queue<T>>,
    tail: usize,
}

pub struct Consumer<T> {
    queue: Arc<Queue<T>>,
    head: usize,
}
// ANCHOR_END: producer_consumer

// ANCHOR: impl
pub fn new_queue<T>(len: usize) -> (Producer<T>, Consumer<T>) {
    // Create a vector of UnsafeCells to serve as the ring buffer

    let mut backing_cells_vec = Vec::<UnsafeCell<MaybeUninit<T>>>::new();
    while backing_cells_vec.len() < len {
        let cell = UnsafeCell::new(MaybeUninit::uninit());
        backing_cells_vec.push(cell);
    }

    // Initialize head and tail to 0 (empty)
    let head_atomic = AtomicU64::new(0);
    let tail_atomic = AtomicU64::new(0);

    // Package it all into a queue object, and make a reference-counted pointer to it
    // so it can be shared by the Producer and the Consumer.
    let queue = Queue::<T> { head: head_atomic, tail: tail_atomic, buffer: backing_cells_vec };
    let queue_arc = Arc::new(queue);

    let prod = Producer::<T> { queue: queue_arc.clone(), tail: 0 };
    let cons = Consumer::<T> { queue: queue_arc, head: 0 };
    (prod, cons)
}

impl<T> Producer<T> {
    pub fn enqueue(&mut self, t: T) {
        // Loop: if the queue is full, then block until it is not.
        loop {
            let len = self.queue.buffer.len();

            // Calculate the index of the slot right after `tail`, wrapping around
            // if necessary. If the enqueue is successful, then we will be updating
            // the `tail` to this value.
            let next_tail = if self.tail + 1 == len { 0 } else { self.tail + 1 };

            // Get the current `head` value from the shared atomic.
            let head = self.queue.head.load(Ordering::SeqCst);

            // Check to make sure there is room. (We can't advance the `tail` pointer
            // if it would become equal to the head, since `tail == head` denotes
            // an empty state.)
            // If there's no room, we'll just loop and try again.
            if head != next_tail as u64 {
                // Here's the unsafe part: writing the given `t` value into the `UnsafeCell`.
                unsafe {
                    (*self.queue.buffer[self.tail].get()).write(t);
                }

                // Update the `tail` (both the shared atomic and our local copy).
                self.queue.tail.store(next_tail as u64, Ordering::SeqCst);
                self.tail = next_tail;

                // Done.
                return;
            }
        }
    }
}

impl<T> Consumer<T> {
    pub fn dequeue(&mut self) -> T {
        // Loop: if the queue is empty, then block until it is not.
        loop {
            let len = self.queue.buffer.len();

            // Calculate the index of the slot right after `head`, wrapping around
            // if necessary. If the enqueue is successful, then we will be updating
            // the `head` to this value.
            let next_head = if self.head + 1 == len { 0 } else { self.head + 1 };

            // Get the current `tail` value from the shared atomic.
            let tail = self.queue.tail.load(Ordering::SeqCst);

            // Check to see if the queue is nonempty.
            // If it's empty, we'll just loop and try again.
            if self.head as u64 != tail {
                // Load the stored message from the UnsafeCell
                // (replacing it with "uninitialized" memory).
                let t = unsafe {
                    let mut tmp = MaybeUninit::uninit();
                    std::mem::swap(&mut *self.queue.buffer[self.head].get(), &mut tmp);
                    tmp.assume_init()
                };

                // Update the `head` (both the shared atomic and our local copy).
                self.queue.head.store(next_head as u64, Ordering::SeqCst);
                self.head = next_head;

                // Done. Return the value we loaded out of the buffer.
                return t;
            }
        }
    }
}
// ANCHOR_END: impl

fn main() {
    let (mut producer, mut consumer) = new_queue(20);
    producer.enqueue(5);
    let _x = consumer.dequeue();
}
// ANCHOR_END: full
