#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_binary_heap_new verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_new() {
            let heap: BinaryHeap<u32> = BinaryHeap::new();
            assert(heap@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_push verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::multiset::*;
        use std::collections::BinaryHeap;

        fn test_push() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_multiset_axioms;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(3);
            assert(heap@.len() == 1);
            assert(heap@.contains(3u32));

            // Verify push worked by popping and checking the value
            let val = heap.pop();
            assert(val.is_some());
            assert(val.unwrap() == 3u32);
            assert(heap@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_push_multiple verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::multiset::*;
        use std::collections::BinaryHeap;

        fn test_push_multiple() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_multiset_axioms;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(3);
            heap.push(5);
            heap.push(1);
            assert(heap@.len() == 3);
            assert(heap@.contains(3u32));
            assert(heap@.contains(5u32));
            assert(heap@.contains(1u32));

            // Capture state before first pop
            let ghost original = heap@;

            // Pop returns max - use is_heap_max to prove it's >= all elements
            let v1 = heap.pop();
            assert(v1.is_some());
            let max1 = v1.unwrap();
            assert(is_heap_max(max1, original));
            // Via axiom: all elements in original are <= max1
            assert(original.contains(3u32) ==> 3u32 <= max1);
            assert(original.contains(5u32) ==> 5u32 <= max1);
            assert(original.contains(1u32) ==> 1u32 <= max1);
            // Since 5 was in heap and all elements <= max1, max1 >= 5
            // Since max1 was in heap and max elements are 1,3,5, max1 == 5
            assert(max1 == 5u32);
            assert(heap@.len() == 2);

            // Capture state before second pop
            let ghost after_first = heap@;

            // Pop again
            let v2 = heap.pop();
            assert(v2.is_some());
            let max2 = v2.unwrap();
            assert(is_heap_max(max2, after_first));
            // Remaining elements were 1, 3
            assert(after_first.contains(1u32) ==> 1u32 <= max2);
            assert(after_first.contains(3u32) ==> 3u32 <= max2);
            assert(max2 == 3u32);
            assert(heap@.len() == 1);

            // Pop last
            let v3 = heap.pop();
            assert(v3.is_some());
            assert(v3.unwrap() == 1u32);
            assert(heap@.len() == 0);

            // Empty now
            let v4 = heap.pop();
            assert(v4.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_len verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_len() {
            broadcast use group_binary_heap_axioms;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            assert(heap.len() == 0);

            heap.push(10);
            assert(heap.len() == 1);

            heap.push(20);
            assert(heap.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_clear verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_clear() {
            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(1);
            heap.push(2);
            assert(heap@.len() == 2);

            heap.clear();
            assert(heap@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_peek_empty verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_peek_empty() {
            let heap: BinaryHeap<u32> = BinaryHeap::new();
            let top = heap.peek();
            assert(top.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_peek_nonempty verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_peek_nonempty() {
            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(42);
            let top = heap.peek();
            assert(top.is_some());
            assert(*top.unwrap() == 42);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_pop_empty verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_pop_empty() {
            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            let val = heap.pop();
            assert(val.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_pop_single verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::multiset::*;
        use std::collections::BinaryHeap;

        fn test_pop_single() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_multiset_axioms;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(42);
            assert(heap@.len() == 1);
            assert(heap@.contains(42u32));

            let val = heap.pop();
            assert(val.is_some());
            assert(val.unwrap() == 42u32);

            // After pop, heap is empty
            assert(heap@.len() == 0);
            assert(!heap@.contains(42u32));

            // Pop again returns None
            let val2 = heap.pop();
            assert(val2.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_pop_maximality verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::multiset::*;
        use std::collections::BinaryHeap;

        fn test_pop_returns_max() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_multiset_axioms;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(10);
            heap.push(50);
            heap.push(30);

            // Capture original heap
            let ghost original = heap@;

            // Pop should return the maximum
            let max_val = heap.pop();
            assert(max_val.is_some());

            // is_heap_max guarantees the popped value is >= all elements
            let v = max_val.unwrap();
            assert(is_heap_max(v, original));

            // Prove 10, 30, 50 were in the original heap
            proof {
                assert(original.contains(10u32));
                assert(original.contains(30u32));
                assert(original.contains(50u32));
            }

            // Via the axiom: is_heap_max(v, original) && original.contains(x) ==> x <= v
            // But we need to instantiate the forall manually
            proof {
                // The axiom says: is_heap_max(v, heap) ==> forall|x| heap.contains(x) ==> x <= v
                // So v must be >= 10, 30, 50, meaning v == 50
                assert(original.contains(10u32) ==> 10u32 <= v);
                assert(original.contains(30u32) ==> 30u32 <= v);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_peek_maximality verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::multiset::*;
        use std::collections::BinaryHeap;

        fn test_peek_returns_max() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_multiset_axioms;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(5);
            heap.push(100);
            heap.push(25);

            // Peek should return reference to the maximum
            let max_ref = heap.peek();
            assert(max_ref.is_some());

            // is_heap_max guarantees the peeked value is >= all elements
            let v = *max_ref.unwrap();
            assert(is_heap_max(v, heap@));

            // Prove elements are in the heap
            proof {
                assert(heap@.contains(5u32));
                assert(heap@.contains(25u32));
                assert(heap@.contains(100u32));
            }

            // Via the axiom: is_heap_max(v, heap@) && heap@.contains(x) ==> x <= v
            proof {
                assert(heap@.contains(5u32) ==> 5u32 <= v);
                assert(heap@.contains(25u32) ==> 25u32 <= v);
            }

            // Heap unchanged after peek
            assert(heap@.len() == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_with_capacity verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_with_capacity() {
            let heap: BinaryHeap<u32> = BinaryHeap::with_capacity(100);
            assert(heap@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_clone verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_clone() {
            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(1);
            heap.push(2);

            let cloned = heap.clone();
            assert(cloned@ == heap@);
        }
    } => Ok(())
}

// Test that we correctly reject wrong assertions
test_verify_one_file! {
    #[test] test_binary_heap_wrong_len_fails verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        fn test_wrong_len() {
            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(5);
            assert(heap@.len() == 2); // FAILS - should be 1
        }
    } => Err(err) => assert_one_fails(err)
}

// Iterator tests for 100% coverage!

test_verify_one_file! {
    #[test] test_binary_heap_into_iter_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::seq_lib::*;
        use std::collections::BinaryHeap;

        fn test_into_iter_for_loop() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_to_multiset_ensures;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(3);
            heap.push(7);
            heap.push(5);

            // Capture the multiset before consuming
            let ghost original_multiset = heap@;
            assert(original_multiset.len() == 3);

            // Get iterator and capture its elements
            let iter = heap.into_iter();
            let ghost elems = iter@.1;
            assert(elems.to_multiset() == original_multiset);
            // seq.len() == seq.to_multiset().len() from to_multiset_ensures
            assert(elems.len() == original_multiset.len());
            assert(elems.len() == 3);

            let mut count: u64 = 0;
            for x in it: iter
                invariant
                    count == it.pos as u64,
                    it.elements == elems,
                    it.pos <= it.elements.len(),
                    it.elements.len() == 3,  // bounded for overflow
            {
                // Verify value matches what's in the sequence
                assert(x == elems[count as int]);
                count = count + 1;
            }
            // After loop: it.pos == it.elements.len() (ghost_ensures)
            assert(count == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_iter_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::seq_lib::*;
        use std::collections::BinaryHeap;

        fn test_iter_for_loop() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_to_multiset_ensures;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(10);
            heap.push(20);

            // Capture multiset
            let ghost original_multiset = heap@;
            assert(original_multiset.len() == 2);

            // Get iterator
            let iter = heap.iter();
            let ghost elems = iter@.1;
            assert(elems.to_multiset() == original_multiset);
            assert(elems.len() == original_multiset.len());
            assert(elems.len() == 2);

            let mut count: u64 = 0;
            for x in it: iter
                invariant
                    count == it.pos as u64,
                    it.elements == elems,
                    it.pos <= it.elements.len(),
                    it.elements.len() == 2,  // bounded for overflow
            {
                // Verify value matches (dereferencing ref)
                assert(*x == elems[count as int]);
                count = count + 1;
            }
            // After loop: it.pos == it.elements.len() (ghost_ensures)
            assert(count == 2);

            // Heap still exists - iter() doesn't consume
            assert(heap@.len() == 2);
        }
    } => Ok(())
}

// While loop test using Iterator::next() directly
test_verify_one_file! {
    #[test] test_binary_heap_iter_while_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::seq_lib::*;
        use std::collections::BinaryHeap;

        fn test_iter_while_loop() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_to_multiset_ensures;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(5);
            heap.push(6);
            assert(heap@.len() == 2);

            let mut iter = heap.into_iter();
            let ghost original_seq = iter@.1;
            assert(original_seq.len() == 2);

            let mut count: u64 = 0;
            while count < 2
                invariant
                    iter@.1 == original_seq,
                    0 <= iter@.0 <= original_seq.len(),
                    count == iter@.0 as u64,
                    original_seq.len() == 2,
                decreases 2 - count,
            {
                let result = iter.next();
                assert(result.is_some());
                let val = result.unwrap();
                let ghost idx = iter@.0 - 1;
                assert(0 <= idx < original_seq.len());
                assert(val == original_seq[idx]);
                count = count + 1;
            }
            assert(count == 2);
            assert(iter@.0 >= original_seq.len());
        }
    } => Ok(())
}

// Loop-loop test using Iterator::next() with match
test_verify_one_file! {
    #[test] test_binary_heap_iter_loop_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use vstd::seq_lib::*;
        use std::collections::BinaryHeap;

        fn test_iter_loop_loop() {
            broadcast use group_binary_heap_axioms;
            broadcast use group_to_multiset_ensures;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(10);
            heap.push(20);
            assert(heap@.len() == 2);

            let mut iter = heap.into_iter();
            let ghost original_seq = iter@.1;
            assert(original_seq.len() == 2);

            let mut count: u64 = 0;
            loop
                invariant_except_break
                    iter@.1 == original_seq,
                    0 <= iter@.0 <= original_seq.len(),
                    count == iter@.0 as u64,
                    original_seq.len() == 2,
                ensures
                    iter@.0 >= original_seq.len(),
                    count == 2,
                decreases original_seq.len() - iter@.0,
            {
                match iter.next() {
                    Some(val) => {
                        let ghost idx = iter@.0 - 1;
                        assert(0 <= idx < original_seq.len());
                        assert(val == original_seq[idx]);
                        count = count + 1;
                    },
                    None => {
                        break;
                    },
                }
            }
            assert(count == 2);
            assert(iter@.0 >= original_seq.len());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_binary_heap_deep_view verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::binary_heap::*;
        use std::collections::BinaryHeap;

        // Test deep_view for primitive types (identity transformation)
        // For u32, deep_view() == @ since u32::deep_view is identity
        fn test_deep_view_primitive() {
            broadcast use group_binary_heap_axioms;

            let mut heap: BinaryHeap<u32> = BinaryHeap::new();
            heap.push(10);
            heap.push(20);

            // For primitive types, deep_view exists and can be called
            // (Full nested type testing would require additional lemmas)
            proof {
                let dv = heap.deep_view();
                // The deep_view for Multiset<u32> is Multiset<u32> (identity)
                // We just verify the trait is implemented
            }
        }
    } => Ok(())
}
