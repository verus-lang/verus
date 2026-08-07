#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_btree_map_new verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_new() {
            let map: BTreeMap<u32, u32> = BTreeMap::new();
            assert(map@.len() == 0);
            assert(map@.dom() =~= Set::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_insert verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_insert() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            let old = map.insert(1, 100);
            assert(old.is_none());
            assert(map@.contains_key(1u32));
            assert(map@[1u32] == 100u32);

            // Verify insert worked via get
            let val = map.get(&1);
            assert(val.is_some());
            assert(*val.unwrap() == 100u32);

            // Verify round-trip via remove
            let removed = map.remove(&1);
            assert(removed.is_some());
            assert(removed.unwrap() == 100u32);
            assert(!map@.contains_key(1u32));
            assert(map@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_insert_replace verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_insert_replace() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 100);
            let old = map.insert(1, 200);
            assert(old.is_some());
            assert(old.unwrap() == 100u32);
            assert(map@[1u32] == 200u32);

            // Verify new value via get
            let val = map.get(&1);
            assert(val.is_some());
            assert(*val.unwrap() == 200u32);

            // Verify round-trip via remove
            let removed = map.remove(&1);
            assert(removed.is_some());
            assert(removed.unwrap() == 200u32);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_get verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_get() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(42, 999);

            let val = map.get(&42);
            assert(val.is_some());
            assert(*val.unwrap() == 999);

            let missing = map.get(&99);
            assert(missing.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_contains_key verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_contains_key() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(5, 50);

            let has_5 = map.contains_key(&5);
            let has_10 = map.contains_key(&10);
            assert(has_5);
            assert(!has_10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_remove verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_remove() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            map.insert(2, 20);

            let removed = map.remove(&1);
            assert(removed.is_some());
            assert(removed.unwrap() == 10);
            assert(!map@.contains_key(1u32));
            assert(map@.contains_key(2u32));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_remove_missing verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_remove_missing() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);

            let removed = map.remove(&99);
            assert(removed.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_len verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_len() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            assert(map.len() == 0);

            map.insert(1, 10);
            assert(map.len() == 1);

            map.insert(2, 20);
            assert(map.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_is_empty verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_is_empty() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            let empty1 = map.is_empty();
            assert(empty1);

            map.insert(1, 10);
            let empty2 = map.is_empty();
            assert(!empty2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_clear verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_clear() {
            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            map.insert(2, 20);

            map.clear();
            assert(map@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_clone verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_clone() {
            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            map.insert(2, 20);

            let cloned = map.clone();
            assert(cloned@ == map@);
        }
    } => Ok(())
}

// Negative test
test_verify_one_file! {
    #[test] test_btree_map_wrong_value_fails verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_wrong_value() {
            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            assert(map@[1u32] == 999u32); // FAILS - should be 10
        }
    } => Err(err) => assert_one_fails(err)
}

// Iterator tests

test_verify_one_file! {
    #[test] test_btree_map_into_iter_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use vstd::seq_lib::*;
        use std::collections::BTreeMap;

        fn test_into_iter_for_loop() {
            broadcast use group_btree_map_axioms;
            broadcast use group_seq_lib_default;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            map.insert(2, 20);
            map.insert(3, 30);
            assert(map@.len() == 3);

            // Capture the kv_pairs before consuming
            let ghost original_kv_pairs = map@.kv_pairs();
            let ghost original_len = map@.len();

            // Get iterator and capture its elements
            let iter = map.into_iter();
            let ghost elems = iter@.1;
            assert(elems.to_set() == original_kv_pairs);
            assert(elems.len() == original_len);
            assert(elems.len() == 3);

            let mut count: u64 = 0;
            for kv in it: iter
                invariant
                    count == it.pos as u64,
                    it.kv_pairs == elems,
                    it.pos <= it.kv_pairs.len(),
                    it.kv_pairs.len() == 3,  // bounded for overflow
            {
                // In the body, it.pos is the index before advance, so kv == elems[count]
                // Since count == it.pos (from invariant before body runs)
                assert(kv == elems[count as int]);
                count = count + 1;
            }
            // After loop: it.pos == it.kv_pairs.len() (ghost_ensures)
            assert(count == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_iter_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use vstd::seq_lib::*;
        use std::collections::BTreeMap;

        fn test_iter_for_loop() {
            broadcast use group_btree_map_axioms;
            broadcast use group_seq_lib_default;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(10, 100);
            map.insert(20, 200);
            assert(map@.len() == 2);

            // Get iterator
            let iter = map.iter();
            let ghost elems = iter@.1;
            assert(elems.to_set() == map@.kv_pairs());
            assert(elems.len() == map@.len());
            assert(elems.len() == 2);

            let mut count: u64 = 0;
            for kv in it: iter
                invariant
                    count == it.pos as u64,
                    it.kv_pairs == elems,
                    it.pos <= it.kv_pairs.len(),
                    it.kv_pairs.len() == 2,  // bounded for overflow
            {
                // In the body, count == it.pos, so kv (dereferenced) == elems[count]
                assert((*kv.0, *kv.1) == elems[count as int]);
                count = count + 1;
            }
            assert(count == 2);

            // Map still exists - iter() doesn't consume
            assert(map@.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_keys_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use vstd::seq_lib::*;
        use std::collections::BTreeMap;

        fn test_keys_for_loop() {
            broadcast use group_btree_map_axioms;
            broadcast use group_seq_lib_default;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(5, 50);
            map.insert(6, 60);

            let keys_iter = map.keys();
            let ghost key_elems = keys_iter@.1;
            assert(key_elems.to_set() == map@.dom());
            assert(key_elems.len() == map@.len());
            assert(key_elems.len() == 2);

            let mut count: u64 = 0;
            for k in it: keys_iter
                invariant
                    count == it.pos as u64,
                    it.keys == key_elems,
                    it.pos <= it.keys.len(),
                    it.keys.len() == 2,  // bounded for overflow
            {
                // Verify value matches (dereferencing ref)
                assert(*k == key_elems[count as int]);
                count = count + 1;
            }
            assert(count == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_values_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use vstd::seq_lib::*;
        use std::collections::BTreeMap;

        fn test_values_for_loop() {
            broadcast use group_btree_map_axioms;
            broadcast use group_seq_lib_default;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(7, 70);
            map.insert(8, 80);

            let values_iter = map.values();
            let ghost val_elems = values_iter@.1;
            assert(val_elems.len() == map@.len());
            assert(val_elems.len() == 2);

            let mut count: u64 = 0;
            for v in it: values_iter
                invariant
                    count == it.pos as u64,
                    it.values == val_elems,
                    it.pos <= it.values.len(),
                    it.values.len() == 2,  // bounded for overflow
            {
                // Verify value matches (dereferencing ref)
                assert(*v == val_elems[count as int]);
                count = count + 1;
            }
            assert(count == 2);
        }
    } => Ok(())
}

// Value-checking for-loop test using into_iter (owns values, not refs)
test_verify_one_file! {
    #[test] test_btree_map_iter_for_loop_values verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use vstd::seq_lib::*;
        use std::collections::BTreeMap;

        fn test_iter_for_loop_values() {
            broadcast use group_btree_map_axioms;
            broadcast use group_seq_lib_default;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            map.insert(2, 20);
            assert(map@.len() == 2);
            let ghost map_snapshot = map@;

            let iter = map.into_iter();
            let ghost elems = iter@.1;
            assert(elems.len() == 2);
            assert(elems.to_set() == map_snapshot.kv_pairs());

            let mut count: u64 = 0;
            for kv in it: iter
                invariant
                    it.kv_pairs == elems,
                    it.pos <= it.kv_pairs.len(),
                    it.kv_pairs.len() == 2,
                    count == it.pos as u64,
            {
                // Verify value matches what's in the sequence
                assert(kv == elems[count as int]);
                count = count + 1;
            }
            // We iterated through all 2 elements
            assert(count == 2);
        }
    } => Ok(())
}

// While loop test using Iterator::next() directly
test_verify_one_file! {
    #[test] test_btree_map_iter_while_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_iter_while_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(5, 50);
            map.insert(6, 60);
            assert(map@.len() == 2);

            let mut iter = map.into_iter();
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
                let (k, v) = result.unwrap();
                let ghost idx = iter@.0 - 1;  // just advanced
                assert(0 <= idx < original_seq.len());
                assert((k, v) == original_seq[idx]);
                count = count + 1;
            }
            assert(count == 2);
            assert(iter@.0 >= original_seq.len());
        }
    } => Ok(())
}

// loop-loop test with manual break
test_verify_one_file! {
    #[test] test_btree_map_iter_loop_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_iter_loop_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(10, 100);
            map.insert(20, 200);
            assert(map@.len() == 2);

            let mut iter = map.into_iter();
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
                    Some((k, v)) => {
                        let ghost idx = iter@.0 - 1;
                        assert(0 <= idx < original_seq.len());
                        assert((k, v) == original_seq[idx]);
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

// Keys iterator - while loop
test_verify_one_file! {
    #[test] test_btree_map_keys_while_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_keys_while_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(5, 50);
            map.insert(6, 60);
            assert(map@.len() == 2);

            let mut keys = map.keys();
            let ghost original_seq = keys@.1;
            assert(original_seq.len() == 2);

            let mut count: u64 = 0;
            while count < 2
                invariant
                    keys@.1 == original_seq,
                    0 <= keys@.0 <= original_seq.len(),
                    count == keys@.0 as u64,
                    original_seq.len() == 2,
                decreases 2 - count,
            {
                let result = keys.next();
                assert(result.is_some());
                let k = result.unwrap();
                let ghost idx = keys@.0 - 1;
                assert(0 <= idx < original_seq.len());
                assert(*k == original_seq[idx]);
                count = count + 1;
            }
            assert(count == 2);
            assert(keys@.0 >= original_seq.len());
        }
    } => Ok(())
}

// Keys iterator - loop-match
test_verify_one_file! {
    #[test] test_btree_map_keys_loop_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_keys_loop_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(5, 50);
            map.insert(6, 60);
            assert(map@.len() == 2);

            let mut keys = map.keys();
            let ghost original_seq = keys@.1;
            assert(original_seq.len() == 2);

            let mut count: u64 = 0;
            loop
                invariant_except_break
                    keys@.1 == original_seq,
                    0 <= keys@.0 <= original_seq.len(),
                    count == keys@.0 as u64,
                    original_seq.len() == 2,
                ensures
                    keys@.0 >= original_seq.len(),
                    count == 2,
                decreases original_seq.len() - keys@.0,
            {
                match keys.next() {
                    Some(k) => {
                        let ghost idx = keys@.0 - 1;
                        assert(0 <= idx < original_seq.len());
                        assert(*k == original_seq[idx]);
                        count = count + 1;
                    },
                    None => {
                        break;
                    },
                }
            }
            assert(count == 2);
            assert(keys@.0 >= original_seq.len());
        }
    } => Ok(())
}

// Values iterator - while loop
test_verify_one_file! {
    #[test] test_btree_map_values_while_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_values_while_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(7, 70);
            map.insert(8, 80);
            assert(map@.len() == 2);

            let mut values = map.values();
            let ghost original_seq = values@.1;
            assert(original_seq.len() == 2);

            let mut count: u64 = 0;
            while count < 2
                invariant
                    values@.1 == original_seq,
                    0 <= values@.0 <= original_seq.len(),
                    count == values@.0 as u64,
                    original_seq.len() == 2,
                decreases 2 - count,
            {
                let result = values.next();
                assert(result.is_some());
                let v = result.unwrap();
                let ghost idx = values@.0 - 1;
                assert(0 <= idx < original_seq.len());
                assert(*v == original_seq[idx]);
                count = count + 1;
            }
            assert(count == 2);
            assert(values@.0 >= original_seq.len());
        }
    } => Ok(())
}

// Values iterator - loop-match
test_verify_one_file! {
    #[test] test_btree_map_values_loop_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_values_loop_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(7, 70);
            map.insert(8, 80);
            assert(map@.len() == 2);

            let mut values = map.values();
            let ghost original_seq = values@.1;
            assert(original_seq.len() == 2);

            let mut count: u64 = 0;
            loop
                invariant_except_break
                    values@.1 == original_seq,
                    0 <= values@.0 <= original_seq.len(),
                    count == values@.0 as u64,
                    original_seq.len() == 2,
                ensures
                    values@.0 >= original_seq.len(),
                    count == 2,
                decreases original_seq.len() - values@.0,
            {
                match values.next() {
                    Some(v) => {
                        let ghost idx = values@.0 - 1;
                        assert(0 <= idx < original_seq.len());
                        assert(*v == original_seq[idx]);
                        count = count + 1;
                    },
                    None => {
                        break;
                    },
                }
            }
            assert(count == 2);
            assert(values@.0 >= original_seq.len());
        }
    } => Ok(())
}

// IntoIter - while loop
test_verify_one_file! {
    #[test] test_btree_map_into_iter_while_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_into_iter_while_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            map.insert(2, 20);
            assert(map@.len() == 2);

            let mut iter = map.into_iter();
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
                let (k, v) = result.unwrap();
                let ghost idx = iter@.0 - 1;
                assert(0 <= idx < original_seq.len());
                assert((k, v) == original_seq[idx]);
                count = count + 1;
            }
            assert(count == 2);
            assert(iter@.0 >= original_seq.len());
        }
    } => Ok(())
}

// IntoIter - loop-match
test_verify_one_file! {
    #[test] test_btree_map_into_iter_loop_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        fn test_into_iter_loop_loop() {
            broadcast use group_btree_map_axioms;

            let mut map: BTreeMap<u32, u32> = BTreeMap::new();
            map.insert(1, 10);
            map.insert(2, 20);
            assert(map@.len() == 2);

            let mut iter = map.into_iter();
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
                    Some((k, v)) => {
                        let ghost idx = iter@.0 - 1;
                        assert(0 <= idx < original_seq.len());
                        assert((k, v) == original_seq[idx]);
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
    #[test] test_btree_map_deep_view verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_map::*;
        use std::collections::BTreeMap;

        // Test deep_view with nested type: BTreeMap<u32, Vec<u32>>
        // deep_view should transform Vec<u32> -> Seq<u32>
        fn test_deep_view_nested(map: BTreeMap<u32, Vec<u32>>, k: u32)
            requires
                map@.contains_key(k),
                map@[k]@ == seq![42u32, 43u32],
        {
            // Use the lemma that connects @ to deep_view()
            broadcast use lemma_btreemap_deepview_properties;

            // The deep_view transforms Vec<u32> values to Seq<u32>
            // Key stays u32 (identity), value becomes Seq
            assert(map.deep_view().contains_key(k));
            assert(map.deep_view()[k] == seq![42u32, 43u32]);
        }
    } => Ok(())
}

// retain - NOT TESTABLE
//
// BTreeMap::retain takes FnMut(&K, &mut V) -> bool. Verus does not support
// &mut in closure arguments, so retain cannot be called in verified code.
// See btree_map.rs spec file for full explanation.
//
// Example of what we'd test if Rust used pure predicates:
//
//   let mut map = BTreeMap::from([(1, 10), (2, 20), (3, 30), (4, 40)]);
//   map.retain(|&k, _v| k % 2 == 0);  // Keep evens, filter odds
//   assert(!map.contains_key(&1) && map.contains_key(&2));
//   assert(!map.contains_key(&3) && map.contains_key(&4));
