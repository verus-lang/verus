#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_btree_set_new verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_new() {
            broadcast use group_btree_set_axioms;
            let set: BTreeSet<u32> = BTreeSet::new();
            assert(set@.len() == 0);
            assert(set@ == Set::<u32>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_insert verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_insert() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            let was_new = set.insert(42);
            assert(was_new == false);  // 42 was not already present
            assert(set@.contains(42u32));
            assert(set@.len() == 1);

            // Verify insert worked via exec contains
            let has_42 = set.contains(&42);
            assert(has_42 == true);

            // Verify round-trip via remove
            let was_present = set.remove(&42);
            assert(was_present == true);
            assert(!set@.contains(42u32));
            assert(set@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_insert_duplicate verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_insert_duplicate() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(42);
            let was_present = set.insert(42);  // Insert duplicate
            assert(was_present == true);  // 42 was already there
            assert(set@.contains(42u32));
            assert(set@.len() == 1);  // Still just one element

            // Verify via exec contains
            let has_42 = set.contains(&42);
            assert(has_42 == true);

            // Verify round-trip via remove
            let removed = set.remove(&42);
            assert(removed == true);
            assert(!set@.contains(42u32));
            assert(set@.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_contains verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_contains() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(10);
            set.insert(20);

            let has_10 = set.contains(&10);
            let has_20 = set.contains(&20);
            let has_30 = set.contains(&30);

            assert(has_10 == true);
            assert(has_20 == true);
            assert(has_30 == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_remove verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_remove() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(1);
            set.insert(2);
            assert(set@.len() == 2);

            let was_present = set.remove(&1);
            assert(was_present == true);
            assert(!set@.contains(1u32));
            assert(set@.contains(2u32));
            assert(set@.len() == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_remove_missing verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_remove_missing() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(1);

            let was_present = set.remove(&999);
            assert(was_present == false);
            assert(set@.contains(1u32));
            assert(set@.len() == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_len verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_len() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            assert(set.len() == 0);

            set.insert(1);
            assert(set.len() == 1);

            set.insert(2);
            set.insert(3);
            assert(set.len() == 3);

            set.insert(2);  // Duplicate
            assert(set.len() == 3);  // No change
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_is_empty verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_is_empty() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            let empty1 = set.is_empty();
            assert(empty1 == true);

            set.insert(42);
            let empty2 = set.is_empty();
            assert(empty2 == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_clear verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_clear() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(1);
            set.insert(2);
            set.insert(3);
            assert(set@.len() == 3);

            set.clear();
            assert(set@.len() == 0);
            assert(set@ == Set::<u32>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_clone verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_clone() {
            broadcast use group_btree_set_axioms;
            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(10);
            set.insert(20);

            let cloned = set.clone();
            assert(cloned@ == set@);
            assert(cloned@.contains(10u32));
            assert(cloned@.contains(20u32));
        }
    } => Ok(())
}

// Negative test
test_verify_one_file! {
    #[test] test_btree_set_wrong_contains_fails verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_wrong_contains() {
            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(1);
            assert(set@.contains(999u32)); // FAILS - 999 not in set
        }
    } => Err(err) => assert_one_fails(err)
}

// Iterator tests

test_verify_one_file! {
    #[test] test_btree_set_into_iter_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use vstd::seq_lib::*;
        use std::collections::BTreeSet;

        fn test_into_iter_for_loop() {
            broadcast use group_btree_set_axioms;
            broadcast use group_seq_lib_default;

            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(1);
            set.insert(2);
            set.insert(3);
            assert(set@.len() == 3);

            let ghost original_set = set@;

            let iter = set.into_iter();
            let ghost elems = iter@.1;
            assert(elems.to_set() == original_set);
            assert(elems.len() == 3);

            let mut count: u64 = 0;
            for x in it: iter
                invariant
                    count == it.pos as u64,
                    it.elements == elems,
                    it.pos <= it.elements.len(),
                    it.elements.len() == 3,
            {
                // In the body, count == it.pos, so x == elems[count]
                assert(x == elems[count as int]);
                count = count + 1;
            }
            assert(count == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_iter_for_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use vstd::seq_lib::*;
        use std::collections::BTreeSet;

        fn test_iter_for_loop() {
            broadcast use group_btree_set_axioms;
            broadcast use group_seq_lib_default;

            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(10);
            set.insert(20);
            assert(set@.len() == 2);

            let iter = set.iter();
            let ghost elems = iter@.1;
            assert(elems.to_set() == set@);
            assert(elems.len() == set@.len());
            assert(elems.len() == 2);

            let mut count: u64 = 0;
            for x in it: iter
                invariant
                    count == it.pos as u64,
                    it.elements == elems,
                    it.pos <= it.elements.len(),
                    it.elements.len() == 2,
            {
                // In the body, count == it.pos, so *x (dereferenced) == elems[count]
                assert(*x == elems[count as int]);
                count = count + 1;
            }
            assert(count == 2);

            // Set still exists - iter() doesn't consume
            assert(set@.len() == 2);
        }
    } => Ok(())
}

// Iter (borrowing) - while loop
test_verify_one_file! {
    #[test] test_btree_set_iter_while_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_iter_while_loop() {
            broadcast use group_btree_set_axioms;

            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(5);
            set.insert(6);
            assert(set@.len() == 2);

            let mut iter = set.iter();
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
                assert(*val == original_seq[idx]);  // dereference - iter() yields &K
                count = count + 1;
            }
            assert(count == 2);
            assert(iter@.0 >= original_seq.len());

            // Set still exists - iter() doesn't consume
            assert(set@.len() == 2);
        }
    } => Ok(())
}

// Iter (borrowing) - loop-match
test_verify_one_file! {
    #[test] test_btree_set_iter_loop_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_iter_loop_loop() {
            broadcast use group_btree_set_axioms;

            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(10);
            set.insert(20);
            assert(set@.len() == 2);

            let mut iter = set.iter();
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
                        assert(*val == original_seq[idx]);  // dereference - iter() yields &K
                        count = count + 1;
                    },
                    None => {
                        break;
                    },
                }
            }
            assert(count == 2);
            assert(iter@.0 >= original_seq.len());

            // Set still exists - iter() doesn't consume
            assert(set@.len() == 2);
        }
    } => Ok(())
}

// IntoIter (consuming) - while loop
test_verify_one_file! {
    #[test] test_btree_set_into_iter_while_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_into_iter_while_loop() {
            broadcast use group_btree_set_axioms;

            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(5);
            set.insert(6);
            assert(set@.len() == 2);

            let mut iter = set.into_iter();
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
                assert(val == original_seq[idx]);  // no dereference - into_iter() yields K
                count = count + 1;
            }
            assert(count == 2);
            assert(iter@.0 >= original_seq.len());
        }
    } => Ok(())
}

// IntoIter (consuming) - loop-match
test_verify_one_file! {
    #[test] test_btree_set_into_iter_loop_loop verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        fn test_into_iter_loop_loop() {
            broadcast use group_btree_set_axioms;

            let mut set: BTreeSet<u32> = BTreeSet::new();
            set.insert(10);
            set.insert(20);
            assert(set@.len() == 2);

            let mut iter = set.into_iter();
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
                        assert(val == original_seq[idx]);  // no dereference - into_iter() yields K
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
    #[test] test_btree_set_deep_view verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::btree_set::*;
        use std::collections::BTreeSet;

        // Test deep_view with nested type: BTreeSet<Vec<u32>>
        // deep_view should transform Vec<u32> -> Seq<u32>
        // btree_set's deep_view is: self@.map(|x: K| x.deep_view())
        fn test_deep_view_nested(set: BTreeSet<Vec<u32>>, v: Vec<u32>)
            requires
                set@.contains(v),
                v@ == seq![42u32, 43u32],
        {
            broadcast use group_btree_set_axioms;

            // The deep_view transforms Vec<u32> elements to Seq<u32>
            // Since deep_view is self@.map(|x| x.deep_view()), we can reason directly
            assert(set.deep_view().contains(v.deep_view()));
            assert(v.deep_view() == seq![42u32, 43u32]);
            assert(set.deep_view().contains(seq![42u32, 43u32]));
        }
    } => Ok(())
}

// retain - NOT TESTABLE
//
// BTreeSet::retain takes FnMut(&K) -> bool. While the reference is immutable
// (unlike BTreeMap's &mut V), Verus closure support is still limited.
// See btree_set.rs spec file for explanation.
