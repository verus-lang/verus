#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_btree_map verus_code! {
        extern crate alloc;
        use alloc::collections::BTreeMap;
        use vstd::prelude::*;
        fn test()
        {
            let mut m = BTreeMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            let b = m.is_empty();
            assert(b);

            m.insert(3, 4);

            let b = m.is_empty();
            assert(!b);

            m.insert(6, -8);
            assert(m@[3] == 4);

            assert(m@.contains_key(3));
            let b = m.contains_key(&3);
            assert(b);

            let n = m.len();
            assert(n == 2);

            assert(m@.contains_key(6));
            let v = m.get(&6);
            match v {
                Some(v) => assert(*v == -8),
                None => assert(false),
            };

            m.remove(&6);
            assert(!m@.contains_key(6));
            assert(m@.contains_key(3));

            m.clear();
            assert(!m@.contains_key(3));
            let b = m.contains_key(&3);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_contains_key_equality verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test_structural<Key: Ord, Value>(m: &BTreeMap<Key, Value>, k: &Key) -> (result: bool)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_equality::<Key>(),
            ensures
                result == m@.contains_key(*k),
        {
            m.contains_key(k)
        }

        fn test_deep<Key: Ord + DeepView>(first: Key, equivalent: Key, fresh: Key)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let mut m = BTreeMap::<Key, u32>::new();
            m.insert(first, 1);
            assert(!m@.contains_key(equivalent));

            let found = m.contains_key(&equivalent);
            assert(found);
            assert(found == m.deep_view().contains_key(equivalent.deep_view()));

            let found = m.contains_key(&fresh);
            assert(!found);
            assert(found == m.deep_view().contains_key(fresh.deep_view()));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_get_equality verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test_structural<'a, Key: Ord, Value>(
            m: &'a BTreeMap<Key, Value>, k: &Key,
        ) -> (result: Option<&'a Value>)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_equality::<Key>(),
            ensures
                match result {
                    Some(v) => m@.contains_key(*k) && *v == m@[*k],
                    None => !m@.contains_key(*k),
                },
        {
            m.get(k)
        }

        fn test_deep<Key: Ord + DeepView, Value: DeepView>(
            first: Key, equivalent: Key, fresh: Key, value: Value,
        )
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let mut m = BTreeMap::<Key, Value>::new();
            let result = m.get(&equivalent);
            assert(result is None);

            let ghost expected = value.deep_view();
            m.insert(first, value);
            assert(!m@.contains_key(equivalent));

            match m.get(&equivalent) {
                Some(v) => {
                    assert(v.deep_view() == expected);
                    assert(v.deep_view() == m.deep_view()[equivalent.deep_view()]);
                },
                None => assert(false),
            }
            let result = m.get(&fresh);
            assert(result is None);
        }

        fn test_borrowed() {
            let key = 3u32;
            let mut m = BTreeMap::<&u32, u32>::new();
            m.insert(&key, 7);
            assert(m@.contains_key(&key));
            match m.get(&3u32) {
                Some(v) => assert(*v == 7),
                None => assert(false),
            }
            let result = m.get(&4u32);
            assert(result is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_remove_equality verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test_structural<Key: Ord, Value>(
            m: &mut BTreeMap<Key, Value>, k: &Key,
        ) -> (result: Option<Value>)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_equality::<Key>(),
            ensures
                final(m)@ == old(m)@.remove(*k),
                match result {
                    Some(v) => old(m)@.contains_key(*k) && v == old(m)@[*k],
                    None => !old(m)@.contains_key(*k),
                },
        {
            m.remove(k)
        }

        fn test_deep<Key: Ord + DeepView, Value: DeepView>(
            first: Key, equivalent: Key, fresh: Key, value: Value, other_value: Value,
        )
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let mut m = BTreeMap::<Key, Value>::new();
            let result = m.remove(&equivalent);
            assert(result is None);
            assert(m@ == Map::<Key, Value>::empty());

            let ghost expected = value.deep_view();
            let ghost expected_other = other_value.deep_view();
            m.insert(first, value);
            m.insert(fresh, other_value);
            assert(!m@.contains_key(equivalent));

            let ghost before = m.deep_view();
            match m.remove(&equivalent) {
                Some(v) => assert(v.deep_view() == expected),
                None => assert(false),
            }
            assert(m.deep_view() == before.remove(equivalent.deep_view()));
            assert(m.deep_view().contains_key(fresh.deep_view()));
            assert(m.deep_view()[fresh.deep_view()] == expected_other);
            assert(!m@.contains_key(first));
            assert(m@.contains_key(fresh));

            let ghost before = m@;
            let ghost deep_before = m.deep_view();
            let result = m.remove(&equivalent);
            assert(result is None);
            assert(m@ == before);
            assert(m.deep_view() == deep_before);
        }

        fn test_borrowed() {
            let key = 3u32;
            let other = 4u32;
            let mut m = BTreeMap::<&u32, u32>::new();
            m.insert(&key, 7);
            m.insert(&other, 9);
            assert(m@.contains_key(&key));
            match m.remove(&3u32) {
                Some(v) => assert(v == 7),
                None => assert(false),
            }
            assert(!m@.contains_key(&key));
            assert(m@.contains_key(&other));
            assert(m@[&other] == 9);
            let ghost before = m@;
            let result = m.remove(&3u32);
            assert(result is None);
            assert(m@ == before);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_get_mut verus_code! {
        extern crate alloc;
        use alloc::collections::BTreeMap;
        use vstd::prelude::*;

        fn test() {
            let mut m = BTreeMap::<u32, i32>::new();
            m.insert(1, 10);
            m.insert(2, 20);

            assert(m@.contains_key(1));
            match m.get_mut(&1) {
                Some(value) => {
                    assert(*value == 10);
                    *value = 11;
                },
                None => assert(false),
            }
            assert(m@[1] == 11);
            assert(m@[2] == 20);

            let ghost before = m@;
            match m.get_mut(&3) {
                Some(_) => assert(false),
                None => {},
            }
            assert(m@ == before);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_get_mut_equality verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test_structural<Key: Ord, Value>(
            m: &mut BTreeMap<Key, Value>, k: &Key, replacement: Value,
        ) -> (found: bool)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_equality::<Key>(),
            ensures
                found == old(m)@.contains_key(*k),
                final(m)@ == if found {
                    old(m)@.insert(*k, replacement)
                } else {
                    old(m)@
                },
        {
            let ghost before = m@;
            match m.get_mut(k) {
                Some(value) => {
                    assert(*value == before[*k]);
                    *value = replacement;
                    true
                },
                None => false,
            }
        }

        fn test_deep<Key: Ord + DeepView, Value: DeepView>(
            first: Key, equivalent: Key, fresh: Key,
            value: Value, other_value: Value, replacement: Value,
        )
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let ghost expected = value.deep_view();
            let ghost expected_other = other_value.deep_view();
            let ghost updated = replacement.deep_view();
            let mut m = BTreeMap::<Key, Value>::new();
            m.insert(first, value);

            let ghost before = m@;
            let ghost deep_before = m.deep_view();
            match m.get_mut(&fresh) {
                Some(_) => assert(false),
                None => {},
            }
            assert(m@ == before);
            assert(m.deep_view() == deep_before);

            m.insert(fresh, other_value);
            assert(m@.contains_key(first));
            assert(!m@.contains_key(equivalent));
            let ghost before = m.deep_view();
            match m.get_mut(&equivalent) {
                Some(value) => {
                    assert(value.deep_view() == expected);
                    *value = replacement;
                },
                None => assert(false),
            }
            assert(m.deep_view() == before.insert(equivalent.deep_view(), updated));
            assert(m@.contains_key(first));
            assert(!m@.contains_key(equivalent));
            assert(m@[first].deep_view() == updated);
            assert(m.deep_view()[fresh.deep_view()] == expected_other);
        }

        fn test_borrowed() {
            let key = 3u32;
            let other = 4u32;
            let mut m = BTreeMap::<&u32, u32>::new();
            m.insert(&key, 7);
            m.insert(&other, 9);
            assert(m@.contains_key(&key));
            match m.get_mut(&3u32) {
                Some(value) => {
                    assert(*value == 7);
                    *value = 8;
                },
                None => assert(false),
            }
            assert(m@[&key] == 8);
            assert(m@[&other] == 9);

            let ghost before = m@;
            match m.get_mut(&5u32) {
                Some(_) => assert(false),
                None => {},
            }
            assert(m@ == before);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_lower_bound_mut verus_code! {
        extern crate alloc;
        use alloc::collections::BTreeMap;
        use core::ops::Bound;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        proof fn lemma_three_keys(model: CursorMutModel<u32, i32>)
            requires
                model.wf(),
                model.map.dom() == set![1u32, 3u32, 5u32],
            ensures
                model.keys == seq![1u32, 3u32, 5u32],
        {
            assert forall|i, j| 0 <= i < j < model.keys.len()
                implies model.keys[i] < model.keys[j] by {
                assert(<u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(
                    &model.keys[i], &model.keys[j],
                ) is Less);
            }
            model.keys.unique_seq_to_set();
            assert(model.keys.len() == 3);
            assert(model.keys.to_set().contains(model.keys[0]));
            assert(model.keys.to_set().contains(model.keys[1]));
            assert(model.keys.to_set().contains(model.keys[2]));
            assert(model.keys =~= seq![1u32, 3u32, 5u32]);
        }

        fn test() {
            let mut m = BTreeMap::<u32, i32>::new();
            m.insert(1, 10);
            m.insert(3, 30);
            m.insert(5, 50);

            {
                let mut cursor = m.lower_bound_mut(Bound::Included(&3));
                assert(cursor@.wf());
                proof { lemma_three_keys(cursor@); }
                assert(before_lower_bound(1u32, Bound::Included(&3u32)));
                assert(!before_lower_bound(3u32, Bound::Included(&3u32)));
                assert(cursor@.position == 1);

                match cursor.peek_prev() {
                    Some((key, value)) => {
                        assert(*key == 1);
                        assert(*value == 10);
                    },
                    None => assert(false),
                }
                match cursor.peek_next() {
                    Some((key, value)) => {
                        assert(*key == 3);
                        assert(*value == 30);
                        *value = 31;
                    },
                    None => assert(false),
                }
            }

            assert(m@[1] == 10);
            assert(m@[3] == 31);
            assert(m@[5] == 50);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_cursor_boundaries verus_code! {
        extern crate alloc;
        use alloc::collections::BTreeMap;
        use core::ops::Bound;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        proof fn lemma_three_keys(model: CursorMutModel<u32, i32>)
            requires
                model.wf(),
                model.map.dom() == set![1u32, 3u32, 5u32],
            ensures
                model.keys == seq![1u32, 3u32, 5u32],
        {
            assert forall|i, j| 0 <= i < j < model.keys.len()
                implies model.keys[i] < model.keys[j] by {
                assert(<u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(
                    &model.keys[i], &model.keys[j],
                ) is Less);
            }
            model.keys.unique_seq_to_set();
            assert(model.keys.len() == 3);
            assert(model.keys.to_set().contains(model.keys[0]));
            assert(model.keys.to_set().contains(model.keys[1]));
            assert(model.keys.to_set().contains(model.keys[2]));
            assert(model.keys =~= seq![1u32, 3u32, 5u32]);
        }

        fn test() {
            let mut m = BTreeMap::<u32, i32>::new();
            m.insert(1, 10);
            m.insert(3, 30);
            m.insert(5, 50);

            {
                let mut cursor = m.lower_bound_mut(Bound::Unbounded::<&u32>);
                proof { lemma_three_keys(cursor@); }
                assert(!before_lower_bound(1u32, Bound::Unbounded::<&u32>));
                assert(cursor@.position == 0);
                match cursor.peek_prev() {
                    Some(_) => assert(false),
                    None => {},
                }
                match cursor.peek_next() {
                    Some((key, _)) => assert(*key == 1),
                    None => assert(false),
                }
            }

            {
                let mut cursor = m.lower_bound_mut(Bound::Excluded(&3));
                proof { lemma_three_keys(cursor@); }
                assert(before_lower_bound(3u32, Bound::Excluded(&3u32)));
                assert(!before_lower_bound(5u32, Bound::Excluded(&3u32)));
                assert(cursor@.position == 2);
                match cursor.peek_prev() {
                    Some((key, _)) => assert(*key == 3),
                    None => assert(false),
                }
                match cursor.peek_next() {
                    Some((key, _)) => assert(*key == 5),
                    None => assert(false),
                }
            }

            {
                let mut cursor = m.upper_bound_mut(Bound::Excluded(&3));
                proof { lemma_three_keys(cursor@); }
                assert(before_upper_bound(1u32, Bound::Excluded(&3u32)));
                assert(!before_upper_bound(3u32, Bound::Excluded(&3u32)));
                assert(cursor@.position == 1);
                match cursor.peek_prev() {
                    Some((key, _)) => assert(*key == 1),
                    None => assert(false),
                }
                match cursor.peek_next() {
                    Some((key, _)) => assert(*key == 3),
                    None => assert(false),
                }
            }

            {
                let mut cursor = m.upper_bound_mut(Bound::Included(&3));
                proof { lemma_three_keys(cursor@); }
                assert(before_upper_bound(3u32, Bound::Included(&3u32)));
                assert(!before_upper_bound(5u32, Bound::Included(&3u32)));
                assert(cursor@.position == 2);
                match cursor.peek_prev() {
                    Some((key, _)) => assert(*key == 3),
                    None => assert(false),
                }
                match cursor.peek_next() {
                    Some((key, _)) => assert(*key == 5),
                    None => assert(false),
                }
            }

            {
                let mut cursor = m.upper_bound_mut(Bound::Unbounded::<&u32>);
                proof { lemma_three_keys(cursor@); }
                assert(before_upper_bound(5u32, Bound::Unbounded::<&u32>));
                assert(cursor@.position == cursor@.keys.len());
                match cursor.peek_next() {
                    Some(_) => assert(false),
                    None => {},
                }
                match cursor.peek_prev() {
                    Some((key, _)) => assert(*key == 5),
                    None => assert(false),
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_cursor_operations verus_code! {
        extern crate alloc;
        use alloc::collections::BTreeMap;
        use core::ops::Bound;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        proof fn lemma_three_keys(model: CursorMutModel<u32, i32>)
            requires
                model.wf(),
                model.map.dom() == set![1u32, 3u32, 5u32],
            ensures
                model.keys == seq![1u32, 3u32, 5u32],
        {
            assert forall|i, j| 0 <= i < j < model.keys.len()
                implies model.keys[i] < model.keys[j] by {
                assert(<u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(
                    &model.keys[i], &model.keys[j],
                ) is Less);
            }
            model.keys.unique_seq_to_set();
            assert(model.keys.len() == 3);
            assert(model.keys.to_set().contains(model.keys[0]));
            assert(model.keys.to_set().contains(model.keys[1]));
            assert(model.keys.to_set().contains(model.keys[2]));
            assert(model.keys =~= seq![1u32, 3u32, 5u32]);
        }

        fn test() {
            let mut m = BTreeMap::<u32, i32>::new();
            m.insert(1, 10);
            m.insert(3, 30);
            m.insert(5, 50);

            {
                let mut cursor = m.lower_bound_mut(Bound::Unbounded::<&u32>);
                proof { lemma_three_keys(cursor@); }
                assert(!before_lower_bound(1u32, Bound::Unbounded::<&u32>));
                assert(cursor@.position == 0);

                match cursor.next() {
                    Some((key, value)) => {
                        assert(*key == 1);
                        assert(*value == 10);
                        *value = 11;
                    },
                    None => assert(false),
                }
                assert(cursor@.position == 1);

                match cursor.next() {
                    Some((key, value)) => {
                        assert(*key == 3);
                        assert(*value == 30);
                        *value = 31;
                    },
                    None => assert(false),
                }
                assert(cursor@.position == 2);

                match cursor.prev() {
                    Some((key, value)) => {
                        assert(*key == 3);
                        assert(*value == 31);
                        *value = 32;
                    },
                    None => assert(false),
                }
                assert(cursor@.position == 1);

                match cursor.prev() {
                    Some((key, value)) => {
                        assert(*key == 1);
                        assert(*value == 11);
                    },
                    None => assert(false),
                }
                assert(cursor@.position == 0);
                match cursor.prev() {
                    Some(_) => assert(false),
                    None => {},
                }
                assert(cursor@.position == 0);

                assert(key_fits_at_position(cursor@, 0u32));
                match cursor.insert_after(0, 0) {
                    Ok(()) => {},
                    Err(_) => assert(false),
                }
                assert(cursor@.keys == seq![0u32, 1u32, 3u32, 5u32]);
                assert(cursor@.position == 0);

                match cursor.next() {
                    Some((key, value)) => {
                        assert(*key == 0);
                        assert(*value == 0);
                        *value = 1;
                    },
                    None => assert(false),
                }
                assert(cursor@.position == 1);

                assert(!key_fits_at_position(cursor@, 1u32));
                let ghost before_rejected_insert = cursor@;
                match cursor.insert_after(1, 100) {
                    Ok(()) => assert(false),
                    Err(_) => {},
                }
                assert(cursor@ == before_rejected_insert);

                match cursor.remove_next() {
                    Some((key, value)) => {
                        assert(key == 1);
                        assert(value == 11);
                    },
                    None => assert(false),
                }
                assert(cursor@.keys == seq![0u32, 3u32, 5u32]);
                assert(cursor@.position == 1);

                match cursor.next() {
                    Some((key, value)) => {
                        assert(*key == 3);
                        assert(*value == 32);
                    },
                    None => assert(false),
                }
                match cursor.next() {
                    Some((key, value)) => {
                        assert(*key == 5);
                        assert(*value == 50);
                    },
                    None => assert(false),
                }
                assert(cursor@.position == cursor@.keys.len());
                match cursor.next() {
                    Some(_) => assert(false),
                    None => {},
                }
            }

            assert(m@[0] == 1);
            assert(!m@.contains_key(1));
            assert(m@[3] == 32);
            assert(m@[5] == 50);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set verus_code! {
        extern crate alloc;
        use alloc::collections::BTreeSet;
        use vstd::prelude::*;
        fn test()
        {
            let mut m = BTreeSet::<u32>::new();
            assert(m@ == Set::<u32>::empty());

            let b = m.is_empty();
            assert(b);

            let res = m.insert(3);
            assert(res);
            m.insert(6);

            let b = m.is_empty();
            assert(!b);

            let res = m.insert(3);
            assert(!res);

            assert(m@.contains(3));
            let b = m.contains(&3);
            assert(b);

            let n = m.len();
            assert(n == 2);

            assert(m@.contains(6));
            let v = m.get(&6);
            match v {
                Some(v) => assert(*v == 6),
                None => assert(false),
            };

            let res = m.remove(&6);
            assert(res);
            let res = m.remove(&6);
            assert(!res);
            assert(!m@.contains(6));
            assert(m@.contains(3));

            m.clear();
            assert(!m@.contains(3));
            let b = m.contains(&3);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_struct verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, PartialOrd, Ord, StructuralEq)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        fn test()
        {
            assume(vstd::laws_cmp::obeys_cmp::<MyStruct>());
            assert(vstd::std_specs::btree::cmp_matches_equality::<MyStruct>()) by {
                reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
                reveal(vstd::laws_cmp::obeys_cmp_ord);
            }

            let mut m = BTreeMap::<MyStruct, u32>::new();
            assert(m@ == Map::<MyStruct, u32>::empty());
            let s1 = MyStruct{ i: 3, j: 7 };
            m.insert(s1, 4);

            let s2 = MyStruct{ i: 3, j: 7 };
            assert(m@[s2] == 4);
            assert(m@.contains_key(s2));

            let b = m.contains_key(&s2);
            assert(b);

            let v = m.get(&s2);
            match v {
                Some(v) => assert(*v == 4),
                None => assert(false),
            }

            m.clear();
            assert(!m@.contains_key(s2));
            let b = m.contains_key(&s2);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_insert_deep_equality verus_code! {
        extern crate alloc;
        use alloc::collections::BTreeSet;
        use vstd::prelude::*;
        use vstd::std_specs::btree::{
            btree_set_elements_differ, cmp_matches_deep_equality,
        };

        fn test<Key: Ord + DeepView>(first: Key, equivalent: Key, fresh: Key)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let mut s = BTreeSet::<Key>::new();
            let inserted = s.insert(first);
            assert(inserted);
            assert(s@ == set![first]);
            assert(s.deep_view() == set![first.deep_view()]);

            let inserted = s.insert(equivalent);
            assert(!inserted);
            assert(s@ == set![first]);
            assert(!s@.contains(equivalent));
            assert(s.deep_view() == set![first.deep_view()]);

            let inserted = s.insert(fresh);
            assert(inserted);
            assert(s@ == set![first, fresh]);
            assert(s.deep_view() == set![first.deep_view(), fresh.deep_view()]);
            assert(btree_set_elements_differ(&s));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_contains_equality verus_code! {
        use std::collections::BTreeSet;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test_structural<Key: Ord>(s: &BTreeSet<Key>, k: &Key) -> (result: bool)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_equality::<Key>(),
            ensures
                result == s@.contains(*k),
        {
            s.contains(k)
        }

        fn test_deep<Key: Ord + DeepView>(first: Key, equivalent: Key, fresh: Key)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let mut s = BTreeSet::<Key>::new();
            s.insert(first);
            assert(!s@.contains(equivalent));

            let found = s.contains(&equivalent);
            assert(found);
            assert(found == s.deep_view().contains(equivalent.deep_view()));

            let found = s.contains(&fresh);
            assert(!found);
            assert(found == s.deep_view().contains(fresh.deep_view()));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_get_equality verus_code! {
        use std::collections::BTreeSet;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test_structural<'a, Key: Ord>(
            s: &'a BTreeSet<Key>, k: &Key,
        ) -> (result: Option<&'a Key>)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_equality::<Key>(),
            ensures
                match result {
                    Some(key) => s@.contains(*key) && *key == *k,
                    None => !s@.contains(*k),
                },
        {
            s.get(k)
        }

        fn test_deep<Key: Ord + DeepView>(first: Key, equivalent: Key, fresh: Key)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let mut s = BTreeSet::<Key>::new();
            let result = s.get(&equivalent);
            assert(result is None);

            s.insert(first);
            assert(s@ == set![first]);
            match s.get(&equivalent) {
                Some(key) => {
                    assert(*key == first);
                    assert(*key != equivalent);
                    assert(key.deep_view() == equivalent.deep_view());
                },
                None => assert(false),
            }
            let result = s.get(&fresh);
            assert(result is None);
        }

        fn test_borrowed() {
            let key = 3u32;
            let mut s = BTreeSet::<&u32>::new();
            s.insert(&key);
            assert(s@.contains(&key));
            match s.get(&3u32) {
                Some(stored) => assert(**stored == 3),
                None => assert(false),
            }
            let result = s.get(&4u32);
            assert(result is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_remove_equality verus_code! {
        use std::collections::BTreeSet;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test_structural<Key: Ord>(s: &mut BTreeSet<Key>, k: &Key) -> (result: bool)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_equality::<Key>(),
            ensures
                final(s)@ == old(s)@.remove(*k),
                result == old(s)@.contains(*k),
        {
            s.remove(k)
        }

        fn test_deep<Key: Ord + DeepView>(first: Key, equivalent: Key, fresh: Key)
            requires
                vstd::laws_cmp::obeys_cmp::<Key>(),
                cmp_matches_deep_equality::<Key>(),
                first != equivalent,
                first.deep_view() == equivalent.deep_view(),
                first.deep_view() != fresh.deep_view(),
        {
            let mut s = BTreeSet::<Key>::new();
            let removed = s.remove(&equivalent);
            assert(!removed);
            assert(s@ == Set::<Key>::empty());

            s.insert(first);
            s.insert(fresh);
            assert(s@ == set![first, fresh]);
            assert(!s@.contains(equivalent));

            let ghost before = s.deep_view();
            let removed = s.remove(&equivalent);
            assert(removed);
            assert(s.deep_view() == before.remove(equivalent.deep_view()));
            assert(s@ == set![fresh]);
            assert(s.deep_view() == set![fresh.deep_view()]);

            let ghost before = s@;
            let ghost deep_before = s.deep_view();
            let removed = s.remove(&equivalent);
            assert(!removed);
            assert(s@ == before);
            assert(s.deep_view() == deep_before);
        }

        fn test_borrowed() {
            let key = 3u32;
            let other = 4u32;
            let mut s = BTreeSet::<&u32>::new();
            s.insert(&key);
            s.insert(&other);
            assert(s@.contains(&key));
            let removed = s.remove(&3u32);
            assert(removed);
            assert(s@ == set![&other]);

            let ghost before = s@;
            let removed = s.remove(&3u32);
            assert(!removed);
            assert(s@ == before);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_set_struct verus_code! {
        use std::collections::BTreeSet;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, PartialOrd, Ord, StructuralEq)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        fn test()
        {
            assume(vstd::laws_cmp::obeys_cmp::<MyStruct>());
            assert(vstd::std_specs::btree::cmp_matches_equality::<MyStruct>()) by {
                reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
                reveal(vstd::laws_cmp::obeys_cmp_ord);
            }

            let mut m = BTreeSet::<MyStruct>::new();
            assert(m@ == Set::<MyStruct>::empty());
            let s1 = MyStruct{ i: 3, j: 7 };
            let res = m.insert(s1);
            assert(res);
            let res = m.insert(MyStruct{ i: 3, j: 7 });
            assert(!res);

            let s2 = MyStruct{ i: 3, j: 7 };
            assert(m@.contains(s2));

            let b = m.contains(&s2);
            assert(b);

            let v = m.get(&s2);
            match v {
                Some(v) => assert(*v == s2),
                None => assert(false),
            }

            let s3 = MyStruct { i: 9, j: 9 };

            m.insert(MyStruct { i: 9, j: 9 });
            assert(m@.contains(s3));
            let res = m.remove(&s3);
            assert(res);
            let res = m.remove(&s3);
            assert(!res);

            m.clear();
            assert(!m@.contains(s2));
            let b = m.contains(&s2);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_btree_map_struct_fails verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, PartialOrd, Ord)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        fn test()
        {
            // Missing `assume(vstd::laws_cmp::obeys_cmp::<MyStruct>());`

            let mut m = BTreeMap::<MyStruct, u32>::new();
            let s1 = MyStruct{ i: 3, j: 7 };
            m.insert(s1, 4);

            let s2 = MyStruct{ i: 3, j: 7 };
            assert(m@[s2] == 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_btree_set_struct_fails verus_code! {
        use std::collections::BTreeSet;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, PartialOrd, Ord)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        fn test()
        {
            // Missing `assume(vstd::laws_cmp::obeys_cmp::<MyStruct>());`

            let mut m = BTreeSet::<MyStruct>::new();
            let s1 = MyStruct{ i: 3, j: 7 };
            m.insert(s1);

            let s2 = MyStruct{ i: 3, j: 7 };
            assert(m@.contains(s2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_btree_map_deep_view verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;

        fn test(m: BTreeMap<u64, Vec<bool>>, k: u64)
            requires
                m@.contains_key(k),
                m[k]@ == seq![true],
        {
            broadcast use lemma_btree_map_deepview_properties;
            assert(m.deep_view()[k] == seq![true]);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_btree_map_keys ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::BTreeMap;
        use std::collections::btree_map::Keys;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;
        use vstd::std_specs::iter::IteratorSpec;
        use vstd::laws_cmp::obeys_cmp_spec;
        fn test()
        {
            let mut m = BTreeMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            let m_keys = m.keys();
            let ghost g_keys = m_keys.remaining();
            assert(increasing_seq(g_keys));
            assert(g_keys.no_duplicates());

            assert(g_keys == seq![&3u32, &6u32]) by {
                assert(obeys_cmp_spec::<u32>());
                assert forall|i, j| 0 <= i < j < g_keys.len() implies *g_keys[i] < *g_keys[j] by {
                    assert(<&u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(&g_keys[i], &g_keys[j]) is Less);
                    assert(<u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(g_keys[i], g_keys[j]) is Less);
                }
                assert(g_keys.len() == 2) by {
                    g_keys.unique_seq_to_set();
                    assert(set![3u32, 6u32].len() == 2);
                }
                let mapped = g_keys.unref();
                assert(mapped.to_set().contains(mapped[0]));
                assert(mapped.to_set().contains(mapped[1]));
                assert(g_keys =~= seq![&3u32, &6u32]);
            }

            let mut items = Vec::<u32>::new();
            for k in iter: m_keys
                invariant
                    g_keys == iter.seq(),
                    items@ == iter.seq()[..iter.index()].unref(),
            {
                items.push(*k);
            }
            assert(items@ == seq![3u32, 6u32]) by {
                assert(g_keys[..g_keys.len()] =~= g_keys);
            }
            assert(increasing_seq(items@));
            assert(items@.no_duplicates());
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_btree_map_values ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::BTreeMap;
        use std::collections::btree_map::Values;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;
        use vstd::std_specs::iter::IteratorSpec;
        fn test()
        {
            let mut m = BTreeMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());
            assert(m@.values() =~= Set::<i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            assert(m@.values() == set![4i8, -8i8]) by {
                assert(m@.contains_key(3u32));
                assert(m@.contains_key(6u32));
                assert(m@.values() =~= set![4i8, -8i8]);
            };
            let m_values = m.values();
            let ghost g_values = m_values.remaining();
            assert(exists |key_seq: Seq<u32>| {
                    &&& increasing_seq(key_seq)
                    &&& key_seq.to_set() == m@.dom()
                    &&& key_seq.no_duplicates()
                    &&& g_values == key_seq.map(|i: int, k: u32| &m@[k])
            });
            let ghost g_keys = choose |key_seq: Seq<u32>| {
                    &&& increasing_seq(key_seq)
                    &&& key_seq.to_set() == m@.dom()
                    &&& key_seq.no_duplicates()
                    &&& g_values == key_seq.map(|i: int, k: u32| &m@[k])
            };
            assert(increasing_seq(g_keys));
            assert(g_keys.no_duplicates());
            assert(g_values == seq![&4i8, &-8i8]) by {
                assert forall|i, j| 0 <= i < j < g_keys.len() implies g_keys[i] < g_keys[j] by {
                    assert(<u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(&g_keys[i], &g_keys[j]) is Less);
                }
                assert(g_keys.len() == 2) by {
                    g_keys.unique_seq_to_set();
                    assert(set![3u32, 6u32].len() == 2);
                }
                assert(g_keys.to_set().contains(g_keys[0]));
                assert(g_keys.to_set().contains(g_keys[1]));
                assert(g_keys == seq![3u32, 6u32]);
                assert(g_values == g_keys.map(|i: int, k: u32| &m@[k]));
            }


            let mut items = Vec::<i8>::new();

            for v in iter: m_values
                invariant
                    g_values == iter.seq(),
                    items@ == iter.seq()[..iter.index()].unref(),
            {
                items.push(*v);
            }
            assert(items@ == seq![4i8, -8i8]) by {
                assert(g_values[..g_values.len()] =~= g_values);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_btree_map_iter ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::BTreeMap;
        use std::collections::btree_map::Iter;
        use vstd::std_specs::btree::*;
        use vstd::set::{set, Set};
        use vstd::map::Map;
        use vstd::string::View;
        fn test()
        {
            broadcast use vstd::map::group_map_lemmas;
            broadcast use vstd::map_lib::group_map_extra;
            broadcast use vstd::set_lib::group_set_lib_default;

            let mut m = BTreeMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            assert(m@.dom().contains(3u32));
            assert(m@.dom().contains(6u32));

            let mut idx = 0;
            for (k, v) in iter: m.iter()
                invariant
                    m@.kv_pairs() == set![(3u32, 4i8), (6u32, -8i8)],
            {
                // OBSERVE: triggers the extensionality in the invariant
                assert(m@.kv_pairs().contains((*k, *v)));
                assert(*k == 3 ==> *v == 4);
                assert(*k == 6 ==> *v == -8);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_btree_set_iter ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::BTreeSet;
        use std::collections::btree_set::Iter;
        use vstd::std_specs::btree::*;
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;
        fn test()
        {
            let mut m = BTreeSet::<u32>::new();
            assert(m@ == Set::<u32>::empty());

            m.insert(3);
            m.insert(6);
            let m_iter = m.iter();
            assert(m_iter.remaining().unref().to_set() =~= set![3u32, 6u32]);

            let mut items = Vec::<u32>::new();

            for k in iter: m_iter
                invariant
                    iter.seq().unref().to_set() =~= set![3u32, 6u32],
                    items@ == iter.seq()[..iter.index()].unref(),
            {
                items.push(*k);
            }
            assert(items@.to_set() =~= set![3u32, 6u32]) by {
                assert(m_iter.remaining()[..m_iter.remaining().len()] == m_iter.remaining());
            }
            assert(items@.no_duplicates());
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_btree_map_decreases ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::BTreeMap;
        use vstd::std_specs::btree::*;
        use vstd::prelude::*;
        pub enum Foo {
            Base(i64),
            Rec(BTreeMap<i64, Foo>),
        }

        pub open spec fn all_positive(x: Foo) -> bool
            decreases x
        {
            match x {
                Foo::Base(i) => i > 0,
                Foo::Rec(m) => {
                    let bs = m@.map_values(|y| {
                        if m@.dom().finite() && m@.contains_value(y) {
                            all_positive(y)
                        } else {
                            arbitrary()
                        }
                    });
                    bs.values().all(|b| b)
                }
            }
        }
    } => Ok(())
}
