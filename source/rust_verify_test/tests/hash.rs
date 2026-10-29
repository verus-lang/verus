#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_default_hasher verus_code! {
        use core::hash::Hasher;
        use std::collections::hash_map::DefaultHasher;
        use vstd::prelude::*;
        fn test()
        {
            let mut h1: DefaultHasher = DefaultHasher::new();
            let mut h2: DefaultHasher = DefaultHasher::new();
            assert(h1@ == Seq::<Seq<u8>>::empty());
            let mut v1 = Vec::<u8>::new();
            let mut v2 = Vec::<u8>::new();
            v1.push(1u8); v1.push(2u8);
            v2.push(3u8); v2.push(4u8);
            h1.write(v1.as_slice()); h1.write(v2.as_slice());
            h2.write(v1.as_slice()); h2.write(v2.as_slice());
            proof {
                // We need these intermediate assertions to connect
                // the push-based construction with the sequence literal version
                let s1 = seq![1u8].push(2u8);
                let s2 = seq![3u8].push(4u8);
                assert(s1 =~= seq![1u8, 2u8]);
                assert(s2 =~= seq![3u8, 4u8]);
                let hash = seq![h1, h2];
                assert(hash =~= seq![h1].push(h2));
                assert(h1@ =~= seq![seq![1u8, 2u8], seq![3u8, 4u8]]);
            }
            let digest1 = h1.finish();
            let digest2 = h2.finish();
            assert(digest1 == digest2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_map verus_code! {
        use std::collections::HashMap;
        use vstd::prelude::*;
        fn test()
        {
            let mut m = HashMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            let b = m.is_empty();
            assert(b);

            m.insert(3, 4);

            let b = m.is_empty();
            assert(!b);

            m.insert(6, -8);
            assert(m@[3] == 4);
            assert(m@.contains_key(3));
            assert(m@.contains_key(6));

            let b = m.contains_key(&3);
            assert(b);

            let n = m.len();
            assert(n == 2);

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
    #[test] test_hash_map_capacity_with_hasher verus_code! {
        use std::collections::HashMap;
        use std::collections::hash_map::RandomState;
        use vstd::prelude::*;
        fn test()
        {
            let mut m = HashMap::<u32, i8>::new();
            let cap = m.capacity();
            assert(cap >= m@.len());

            m.insert(3, 4);
            let cap = m.capacity();
            assert(cap >= m@.len());

            let m2: HashMap<u32, i8, RandomState> = HashMap::with_hasher(RandomState::default());
            assert(m2@ == Map::<u32, i8>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_set verus_code! {
        use std::collections::HashSet;
        use vstd::prelude::*;
        fn test()
        {
            let mut m = HashSet::<u32>::new();
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
            assert(m@.contains(6));

            let b = m.contains(&3);
            assert(b);

            let n = m.len();
            assert(n == 2);

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
    #[test] test_hash_set_with_hasher verus_code! {
        use std::collections::HashSet;
        use std::collections::hash_map::RandomState;
        use vstd::prelude::*;

        fn test(hasher: RandomState) {
            let m: HashSet<u32> = HashSet::with_hasher(hasher);
            assert(m@ == Set::<u32>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_set_custom_hasher verus_code! {
        use std::collections::HashSet;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::BuildHasher;
        use vstd::prelude::*;
        use vstd::std_specs::hash::builds_valid_hashers;

        struct MyBuilder;

        #[verifier::external]
        impl BuildHasher for MyBuilder {
            type Hasher = DefaultHasher;
            fn build_hasher(&self) -> DefaultHasher {
                DefaultHasher::new()
            }
        }

        fn test()
            requires
                builds_valid_hashers::<MyBuilder>(),
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            let mut s: HashSet<u32, MyBuilder> = HashSet::with_hasher(MyBuilder);
            assert(s@ == Set::<u32>::empty());
            s.insert(3);
            assert(s@.contains(3));

            let t: HashSet<u32, MyBuilder> = HashSet::with_capacity_and_hasher(10, MyBuilder);
            assert(t@ == Set::<u32>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_map_box verus_code! {
        use std::collections::HashMap;
        use vstd::prelude::*;

        fn test()
        {
            let mut m = HashMap::<Box<u32>, i8>::new();
            assert(m@ == Map::<Box<u32>, i8>::empty());

            let three = Box::<u32>::new(3);
            let six = Box::<u32>::new(6);
            m.insert(three, 4);
            m.insert(six, -8);
            assert(m@.contains_key(three));
            assert(m@.contains_key(six));

            let b = m.contains_key(&3);
            assert(b);

            let v = m.get(&6);
            match v {
                Some(v) => assert(*v == -8),
                None => assert(false),
            };

            m.remove(&6);
            assert(!m@.contains_key(six));
            assert(m@.contains_key(three));

            m.clear();
            let b = m.contains_key(&3);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_set_box verus_code! {
        use std::collections::HashSet;
        use vstd::prelude::*;

        fn test()
        {
            let mut m = HashSet::<Box<u32>>::new();
            assert(m@ == Set::<Box<u32>>::empty());

            let three = Box::<u32>::new(3);
            let six = Box::<u32>::new(6);

            let res = m.insert(three);
            assert(res);

            m.insert(six);

            let res = m.insert(Box::<u32>::new(3));
            assert(!res);
            assert(m@.contains(three));
            assert(m@.contains(six));

            let b = m.contains(&3);
            assert(b);

            let v = m.get(&6);
            match v {
                Some(v) => assert(**v == 6),
                None => assert(false),
            };

            let res = m.remove(&6);
            assert(res);
            let res = m.remove(&6);
            assert(!res);
            assert(!m@.contains(six));
            assert(m@.contains(three));

            m.clear();
            let b = m.contains(&3);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_map_struct verus_code! {
        use core::hash::{Hash, Hasher};
        use std::collections::HashMap;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        fn test()
        {
            assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());

            let mut m = HashMap::<MyStruct, u32>::new();
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
    #[test] test_hash_set_struct verus_code! {
        use core::hash::{Hash, Hasher};
        use std::collections::HashSet;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        fn test()
        {
            assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());

            let mut m = HashSet::<MyStruct>::new();
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
    #[test] test_hash_structural_equality verus_code! {
        use core::hash::Hash;
        use std::collections::{HashMap, HashSet, hash_map::Entry};
        use vstd::prelude::*;
        use vstd::std_specs::cmp::eq_matches_equality;
        use vstd::std_specs::hash::{EntrySpecFns, obeys_key_model};

        fn test_map<Key: Hash + Eq + Copy>(m: &mut HashMap<Key, u32>, key: Key)
            requires
                obeys_key_model::<Key>(),
                eq_matches_equality::<Key>(),
        {
            let ghost before = m@;
            let previous = m.insert(key, 42);
            assert(m@ == before.insert(key, 42));
            assert(previous == if before.contains_key(key) { Some(before[key]) } else { None });
            let present = m.contains_key(&key);
            assert(present);
            let value = m.get(&key);
            assert(value == Some(&42u32));
            let removed = m.remove(&key);
            assert(removed == Some(42));
            assert(m@ == before.remove(key));
            let present = m.contains_key(&key);
            assert(!present);
            let value = m.get(&key);
            assert(value.is_none());
            let removed = m.remove(&key);
            assert(removed.is_none());
            assert(m@ == before.remove(key));
        }

        fn test_map_entry<Key: Hash + Eq + Copy>(m: &mut HashMap<Key, u32>, key: Key)
            requires
                obeys_key_model::<Key>(),
                eq_matches_equality::<Key>(),
        {
            let ghost before = m@;
            let entry = m.entry(key);
            assert(*entry.key() == key);
            assert(entry.value() == before.get(key));
            let value = entry.or_insert(42);
            assert(*value == if before.contains_key(key) { before[key] } else { 42u32 });
            *value = 43;
            assert(m@ == before.insert(key, 43));

            match m.entry(key) {
                Entry::Occupied(entry) => {
                    let (stored_key, value) = entry.remove_entry();
                    assert(stored_key == key);
                    assert(value == 43);
                },
                Entry::Vacant(_) => { assert(false); },
            }
            assert(m@ == before.remove(key));
        }

        fn test_set<Key: Hash + Eq + Copy>(m: &mut HashSet<Key>, key: Key)
            requires
                obeys_key_model::<Key>(),
                eq_matches_equality::<Key>(),
        {
            let ghost before = m@;
            let inserted = m.insert(key);
            assert(inserted == !before.contains(key));
            assert(m@ == before.insert(key));
            let inserted = m.insert(key);
            assert(!inserted);
            let present = m.contains(&key);
            assert(present);
            let stored = m.get(&key);
            assert(stored == Some(&key));
            let removed = m.remove(&key);
            assert(removed);
            assert(m@ == before.remove(key));
            let present = m.contains(&key);
            assert(!present);
            let stored = m.get(&key);
            assert(stored.is_none());
            let removed = m.remove(&key);
            assert(!removed);
            assert(m@ == before.remove(key));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_deep_equality verus_code! {
        use core::hash::Hash;
        use std::collections::{HashMap, HashSet, hash_map::Entry};
        use vstd::prelude::*;
        use vstd::std_specs::cmp::eq_matches_deep_equality;
        use vstd::std_specs::hash::{EntrySpecFns, obeys_key_model};

        fn test_map<Key: Hash + Eq + Copy + DeepView, Value: DeepView>(
            key: Key,
            equivalent: Key,
            other: Key,
            initial: Value,
            replacement: Value,
            other_value: Value,
        )
            requires
                obeys_key_model::<Key>(),
                eq_matches_deep_equality::<Key>(),
                key != equivalent,
                key.deep_view() == equivalent.deep_view(),
                key.deep_view() != other.deep_view(),
        {
            let mut m = HashMap::<Key, Value>::new();
            let present = m.contains_key(&equivalent);
            assert(!present);
            let value = m.get(&equivalent);
            assert(value.is_none());
            let removed = m.remove(&equivalent);
            assert(removed.is_none());
            assert(m@ == Map::<Key, Value>::empty());

            let previous = m.insert(key, initial);
            assert(previous.is_none());
            let previous = m.insert(other, other_value);
            assert(previous.is_none());
            assert(m@ == Map::empty().insert(key, initial).insert(other, other_value));
            let present = m.contains_key(&equivalent);
            assert(present);
            let value = m.get(&equivalent);
            assert(value.is_some());
            assert(value.unwrap().deep_view() == initial.deep_view());

            let ghost before = m.deep_view();
            let previous = m.insert(equivalent, replacement);
            assert(previous.is_some());
            assert(previous.unwrap().deep_view() == initial.deep_view());
            assert(m.deep_view() == before.insert(equivalent.deep_view(), replacement.deep_view()));
            assert(m@ == Map::empty().insert(key, replacement).insert(other, other_value));
            assert(!m@.contains_key(equivalent));
            let value = m.get(&equivalent);
            assert(value.is_some());
            assert(value.unwrap().deep_view() == replacement.deep_view());

            let ghost before = m.deep_view();
            let removed = m.remove(&equivalent);
            assert(removed.is_some());
            assert(removed.unwrap().deep_view() == replacement.deep_view());
            assert(m.deep_view() == before.remove(equivalent.deep_view()));
            assert(m@ == Map::empty().insert(other, other_value));
            let present = m.contains_key(&equivalent);
            assert(!present);
            let value = m.get(&equivalent);
            assert(value.is_none());
            let removed = m.remove(&equivalent);
            assert(removed.is_none());
            assert(m@ == Map::empty().insert(other, other_value));
        }

        fn test_map_entry<Key: Hash + Eq + Copy + DeepView, Value: DeepView>(
            m: &mut HashMap<Key, Value>,
            key: Key,
            default: Value,
            replacement: Value,
        )
            requires
                obeys_key_model::<Key>(),
                eq_matches_deep_equality::<Key>(),
        {
            let ghost before = m.deep_view();
            let entry = m.entry(key);
            assert(entry.key().deep_view() == key.deep_view());
            proof {
                match entry.value() {
                    Some(value) => {
                        assert(before.contains_key(key.deep_view()));
                        assert(value.deep_view() == before[key.deep_view()]);
                    },
                    None => { assert(!before.contains_key(key.deep_view())); },
                }
            }
            let value = entry.or_insert(default);
            assert(value.deep_view() == if before.contains_key(key.deep_view()) {
                before[key.deep_view()]
            } else {
                default.deep_view()
            });
            *value = replacement;
            assert(m.deep_view() == before.insert(key.deep_view(), replacement.deep_view()));

            match m.entry(key) {
                Entry::Occupied(entry) => {
                    let (stored_key, value) = entry.remove_entry();
                    assert(stored_key.deep_view() == key.deep_view());
                    assert(value.deep_view() == replacement.deep_view());
                },
                Entry::Vacant(_) => { assert(false); },
            }
            assert(m.deep_view() == before.remove(key.deep_view()));
        }

        fn test_set<Key: Hash + Eq + Copy + DeepView>(
            key: Key,
            equivalent: Key,
            other: Key,
        )
            requires
                obeys_key_model::<Key>(),
                eq_matches_deep_equality::<Key>(),
                key != equivalent,
                key.deep_view() == equivalent.deep_view(),
                key.deep_view() != other.deep_view(),
        {
            let mut m = HashSet::<Key>::new();
            let present = m.contains(&equivalent);
            assert(!present);
            let stored = m.get(&equivalent);
            assert(stored.is_none());
            let removed = m.remove(&equivalent);
            assert(!removed);

            let inserted = m.insert(key);
            assert(inserted);
            let inserted = m.insert(equivalent);
            assert(!inserted);
            assert(m@ == Set::empty().insert(key));
            let inserted = m.insert(other);
            assert(inserted);
            assert(m@ == Set::empty().insert(key).insert(other));
            let present = m.contains(&equivalent);
            assert(present);
            let stored = m.get(&equivalent);
            assert(stored.is_some());
            assert(*stored.unwrap() == key);
            assert(*stored.unwrap() != equivalent);
            assert(stored.unwrap().deep_view() == equivalent.deep_view());
            assert(m.deep_view().contains(equivalent.deep_view()));

            let ghost before = m.deep_view();
            let removed = m.remove(&equivalent);
            assert(removed);
            assert(m.deep_view() == before.remove(equivalent.deep_view()));
            assert(m@ == Set::empty().insert(other));
            let present = m.contains(&equivalent);
            assert(!present);
            let stored = m.get(&equivalent);
            assert(stored.is_none());
            let removed = m.remove(&equivalent);
            assert(!removed);
            assert(m@ == Set::empty().insert(other));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_borrow_equality verus_code! {
        use core::borrow::Borrow;
        use core::hash::Hash;
        use std::collections::{HashMap, HashSet};
        use vstd::prelude::*;
        use vstd::std_specs::borrow::BorrowSpec;
        use vstd::std_specs::cmp::PartialEqSpec;
        use vstd::std_specs::hash::{borrowed_key_hashing_matches, obeys_key_model};

        fn test_map<Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized>(
            key: Key,
            query: &Q,
        )
            requires
                obeys_key_model::<Key>(),
                obeys_key_model::<Q>(),
                borrowed_key_hashing_matches::<Key, Q>(),
                <Key as BorrowSpec<Q>>::obeys_borrow_spec(),
                query.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)),
        {
            let mut m = HashMap::<Key, u32>::new();
            let previous = m.insert(key, 42);
            assert(previous.is_none());
            assert(m@.contains_key(key));
            let present = m.contains_key(query);
            assert(present);
            let value = m.get(query);
            assert(value == Some(&42u32));
            let removed = m.remove(query);
            assert(removed == Some(42));
            assert(m@ == Map::<Key, u32>::empty());
            let present = m.contains_key(query);
            assert(!present);
            let value = m.get(query);
            assert(value.is_none());
            let removed = m.remove(query);
            assert(removed.is_none());
        }

        fn test_set<Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized>(
            key: Key,
            query: &Q,
        )
            requires
                obeys_key_model::<Key>(),
                obeys_key_model::<Q>(),
                borrowed_key_hashing_matches::<Key, Q>(),
                <Key as BorrowSpec<Q>>::obeys_borrow_spec(),
                query.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)),
        {
            let mut m = HashSet::<Key>::new();
            let inserted = m.insert(key);
            assert(inserted);
            assert(m@.contains(key));
            let present = m.contains(query);
            assert(present);
            let stored = m.get(query);
            assert(stored == Some(&key));
            let removed = m.remove(query);
            assert(removed);
            assert(m@ == Set::<Key>::empty());
            let present = m.contains(query);
            assert(!present);
            let stored = m.get(query);
            assert(stored.is_none());
            let removed = m.remove(query);
            assert(!removed);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_key_model_supplies_equality verus_code! {
        use core::hash::Hash;
        use std::collections::HashSet;
        use vstd::prelude::*;
        use vstd::std_specs::cmp::PartialEqSpec;
        use vstd::std_specs::hash::obeys_key_model;

        broadcast use {
            vstd::std_specs::hash::axiom_key_model_implies_obeys_eq,
            vstd::std_specs::hash::lemma_key_model_implies_obeys_eq,
        };

        fn test<Key: Hash + Eq + Copy>(key: Key)
            requires
                obeys_key_model::<Key>(),
            ensures
                vstd::laws_eq::obeys_eq::<Key>(),
        {
            let mut m = HashSet::<Key>::new();
            let inserted = m.insert(key);
            assert(inserted);
            assert(m@.contains(key));
            let present = m.contains(&key);
            assert(present);
            let stored = m.get(&key);
            assert(stored == Some(&key));
            let removed = m.remove(&key);
            assert(removed);
        }

        proof fn test_unsized<Q: Hash + Eq + ?Sized>(a: &Q, b: &Q, c: &Q)
            requires
                obeys_key_model::<Q>(),
            ensures
                <Q as PartialEqSpec>::obeys_eq_spec(),
                a.eq_spec(a),
                a.eq_spec(b) == b.eq_spec(a),
                a.eq_spec(b) && b.eq_spec(c) ==> a.eq_spec(c),
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_map_entry_eq_spec verus_code! {
        use core::hash::Hash;
        use std::collections::{HashMap, hash_map::Entry};
        use vstd::prelude::*;
        use vstd::std_specs::cmp::PartialEqSpec;
        use vstd::std_specs::hash::obeys_key_model;

        fn test_occupied<Key: Hash + Eq + Copy>(stored: Key, query: Key)
            requires
                obeys_key_model::<Key>(),
                stored != query,
                query.eq_spec(&stored),
        {
            let mut m = HashMap::<Key, u32>::new();
            m.insert(stored, 10);
            assert(m@.contains_key(stored));
            let entry = m.entry(query);
            assert(entry is Occupied);
            assert(*entry.key() == stored);
            let value = entry.or_insert(99);
            assert(*value == 10);
            *value = 42;
            assert(m@ == Map::<Key, u32>::empty().insert(stored, 42));
            assert(!m@.contains_key(query));

            match m.entry(query) {
                Entry::Occupied(entry) => {
                    let (key, value) = entry.remove_entry();
                    assert(key == stored);
                    assert(value == 42);
                },
                Entry::Vacant(_) => { assert(false); },
            }
            assert(m@ == Map::<Key, u32>::empty());
        }

        fn test_vacant<Key: Hash + Eq + Copy>(stored: Key, query: Key)
            requires
                obeys_key_model::<Key>(),
                stored != query,
                !query.eq_spec(&stored),
        {
            let mut m = HashMap::<Key, u32>::new();
            m.insert(stored, 10);
            let entry = m.entry(query);
            assert(entry is Vacant);
            assert(*entry.key() == query);
            let value = entry.or_insert(20);
            assert(*value == 20);
            assert(m@ == Map::<Key, u32>::empty().insert(stored, 10).insert(query, 20));
        }

        fn test_occupied_unused<Key: Hash + Eq + Copy>(stored: Key, query: Key)
            requires
                obeys_key_model::<Key>(),
                stored != query,
                query.eq_spec(&stored),
        {
            let mut m = HashMap::<Key, u32>::new();
            m.insert(stored, 10);
            let _entry = m.entry(query);
            assert(m@ == Map::<Key, u32>::empty().insert(stored, 10));
        }

        fn test_vacant_unused<Key: Hash + Eq + Copy>(key: Key)
            requires
                obeys_key_model::<Key>(),
        {
            let mut m = HashMap::<Key, u32>::new();
            let entry = m.entry(key);
            assert(entry is Vacant);
            match entry {
                Entry::Vacant(entry) => {
                    let returned_key = entry.into_key();
                    assert(returned_key == key);
                },
                Entry::Occupied(_) => { assert(false); },
            }
            assert(m@ == Map::<Key, u32>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_legacy_requires_structural_equality verus_code! {
        use core::hash::Hash;
        use std::collections::HashMap;
        use vstd::hash_map::HashMapWithView;
        use vstd::hash_set::HashSetWithView;
        use vstd::prelude::*;
        use vstd::std_specs::hash::obeys_key_model;

        fn test_entry<Key: Hash + Eq>(m: &mut HashMap<Key, u32>, key: Key)
            requires
                obeys_key_model::<Key>(),
        {
            let entry = m.entry(key);
            assert(entry.key() == key); // FAILS
        }

        fn test_map_new<Key: Hash + Eq + View>()
            requires
                obeys_key_model::<Key>(),
                forall|a: Key, b: Key| a@ == b@ ==> a == b,
        {
            let _ = HashMapWithView::<Key, u32>::new(); // FAILS
        }

        fn test_map_with_capacity<Key: Hash + Eq + View>()
            requires
                obeys_key_model::<Key>(),
                forall|a: Key, b: Key| a@ == b@ ==> a == b,
        {
            let _ = HashMapWithView::<Key, u32>::with_capacity(1); // FAILS
        }

        fn test_set_new<Key: Hash + Eq + View>()
            requires
                obeys_key_model::<Key>(),
                forall|a: Key, b: Key| a@ == b@ ==> a == b,
        {
            let _ = HashSetWithView::<Key>::new(); // FAILS
        }

        fn test_set_with_capacity<Key: Hash + Eq + View>()
            requires
                obeys_key_model::<Key>(),
                forall|a: Key, b: Key| a@ == b@ ==> a == b,
        {
            let _ = HashSetWithView::<Key>::with_capacity(1); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] test_hash_borrow verus_code! {
        use core::borrow::Borrow;
        use core::hash::Hash;
        use std::collections::{HashMap, HashSet};
        use vstd::prelude::*;
        use vstd::std_specs::borrow::BorrowSpec;
        use vstd::std_specs::hash::{borrowed_key_hashing_matches, obeys_key_model};

        broadcast use vstd::std_specs::hash::axiom_key_model_implies_obeys_eq;

        fn test_map<Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized>(key: Key, query: &Q)
            requires
                obeys_key_model::<Key>(),
                obeys_key_model::<Q>(),
                borrowed_key_hashing_matches::<Key, Q>(),
                <Key as BorrowSpec<Q>>::obeys_borrow_spec(),
                <Key as BorrowSpec<Q>>::spec_borrow(&key) == query,
        {
            let mut m = HashMap::<Key, u32>::new();
            m.insert(key, 42);
            assert(m@.contains_key(key));

            let present = m.contains_key(query);
            assert(present);
            let value = m.get(query);
            assert(value == Some(&42u32));
            let removed = m.remove(query);
            assert(removed == Some(42));
            assert(m@ == Map::<Key, u32>::empty());

            let present = m.contains_key(query);
            assert(!present);
            let value = m.get(query);
            assert(value.is_none());
            let removed = m.remove(query);
            assert(removed.is_none());
            assert(m@ == Map::<Key, u32>::empty());
        }

        fn test_set<Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized>(key: Key, query: &Q)
            requires
                obeys_key_model::<Key>(),
                obeys_key_model::<Q>(),
                borrowed_key_hashing_matches::<Key, Q>(),
                <Key as BorrowSpec<Q>>::obeys_borrow_spec(),
                <Key as BorrowSpec<Q>>::spec_borrow(&key) == query,
        {
            let mut m = HashSet::<Key>::new();
            m.insert(key);
            assert(m@.contains(key));

            let present = m.contains(query);
            assert(present);
            let value = m.get(query);
            assert(value == Some(&key));
            let removed = m.remove(query);
            assert(removed);
            assert(m@ == Set::<Key>::empty());

            let present = m.contains(query);
            assert(!present);
            let value = m.get(query);
            assert(value.is_none());
            let removed = m.remove(query);
            assert(!removed);
            assert(m@ == Set::<Key>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_borrow_requires_compatibility verus_code! {
        use core::borrow::Borrow;
        use core::hash::Hash;
        use std::collections::HashMap;
        use vstd::prelude::*;

        fn test<Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized>(
            m: &HashMap<Key, u32>,
            query: &Q,
        ) {
            let _ = m.contains_key(query); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_hash_map_struct_fails verus_code! {
        use core::hash::{Hash, Hasher};
        use std::collections::HashMap;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        fn test()
        {
            // Missing `assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());`

            let mut m = HashMap::<MyStruct, u32>::new();
            let s1 = MyStruct{ i: 3, j: 7 };
            m.insert(s1, 4);

            let s2 = MyStruct{ i: 3, j: 7 };
            assert(m@[s2] == 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_hash_set_struct_fails verus_code! {
        use core::hash::{Hash, Hasher};
        use std::collections::HashSet;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        fn test()
        {
            // Missing `assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());`

            let mut m = HashSet::<MyStruct>::new();
            let s1 = MyStruct{ i: 3, j: 7 };
            m.insert(s1);

            let s2 = MyStruct{ i: 3, j: 7 };
            assert(m@.contains(s2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_hash_map_with_view verus_code! {
        use core::hash::{Hash, Hasher};
        use vstd::hash_map::HashMapWithView;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        pub struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        impl View for MyStruct
        {
            type V = (MyStruct, int);
            open spec fn view(&self) -> Self::V
            {
                (*self, self.i + self.j)
            }
        }

        fn test()
        {
            assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());

            let mut m = HashMapWithView::<MyStruct, u32>::new();
            assert(m@ == Map::<(MyStruct, int), u32>::empty());

            let b = m.is_empty();
            assert(b);

            let s1 = MyStruct{ i: 3, j: 7 };
            m.insert(s1, 4);

            let b = m.is_empty();
            assert(!b);

            let s2 = MyStruct{ i: 3, j: 7 };
            let ghost w: (MyStruct, int) = (MyStruct{ i: 3, j: 7 }, 10);
            assert(s1@ == w);
            assert(s2@ == w);
            assert(m@[w] == 4);
            assert(m@.contains_key(w));

            assert(m@.len() == 1);
            assert(m.len() == 1);
            let n = m.len();
            assert(n == 1);

            let b = m.contains_key(&s2);
            assert(b);

            let v = m.get(&s2);
            match v {
                Some(v) => assert(*v == 4),
                None => assert(false),
            }

            m.remove(&s2);
            assert(!m@.contains_key(w));

            let s3 = MyStruct{ i: 3, j: 7 };
            m.insert(s3, 8);
            m.clear();
            assert(!m@.contains_key(w));
            let b = m.contains_key(&s2);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_map_with_view_equality verus_code! {
        use core::hash::Hash;
        use vstd::hash_map::HashMapWithView;
        use vstd::prelude::*;
        use vstd::std_specs::cmp::eq_matches_view_equality;
        use vstd::std_specs::hash::obeys_key_model;

        fn test<Key: Hash + Eq + View + Copy>(key: Key, equivalent: Key, other: Key)
            requires
                obeys_key_model::<Key>(),
                eq_matches_view_equality::<Key>(),
                key != equivalent,
                key@ == equivalent@,
                key@ != other@,
        {
            let mut m = HashMapWithView::<Key, u32>::with_capacity(2);
            assert(m@ == Map::<Key::V, u32>::empty());
            let empty = m.is_empty();
            assert(empty);
            m.reserve(4);
            let previous = m.insert(key, 10);
            assert(previous.is_none());
            let previous = m.insert(equivalent, 20);
            assert(previous == Some(10));
            assert(m@ == Map::<Key::V, u32>::empty().insert(key@, 20));
            assert(m.len() == 1);
            let empty = m.is_empty();
            assert(!empty);
            let present = m.contains_key(&key);
            assert(present);
            let present = m.contains_key(&equivalent);
            assert(present);
            let value = m.get(&equivalent);
            assert(value == Some(&20u32));

            let mut rhs = HashMapWithView::<Key, u32>::new();
            rhs.insert(equivalent, 30);
            let previous = rhs.insert(other, 40);
            assert(previous.is_none());
            m.union_prefer_right(rhs);
            assert(m@ == Map::<Key::V, u32>::empty().insert(key@, 30).insert(other@, 40));
            assert(m.len() == 2);
            let removed = m.remove(&equivalent);
            assert(removed == Some(30));
            assert(m@ == Map::<Key::V, u32>::empty().insert(other@, 40));
            let removed = m.remove(&key);
            assert(removed.is_none());
            let present = m.contains_key(&key);
            assert(!present);
            let value = m.get(&key);
            assert(value.is_none());
            m.clear();
            assert(m@ == Map::<Key::V, u32>::empty());
            assert(m.len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hash_set_with_view verus_code! {
        use core::hash::{Hash, Hasher};
        use vstd::hash_set::HashSetWithView;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, Clone, StructuralEq)]
        pub struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        impl View for MyStruct
        {
            type V = (MyStruct, int);
            open spec fn view(&self) -> Self::V
            {
                (*self, self.i + self.j)
            }
        }

        fn test()
        {
            assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());

            let mut m = HashSetWithView::<MyStruct>::new();
            assert(m@ == Set::<(MyStruct, int)>::empty());

            let b = m.is_empty();
            assert(b);

            let s1 = MyStruct{ i: 3, j: 7 };
            let res = m.insert(s1);
            assert(res);

            let b = m.is_empty();
            assert(!b);

            let res = m.insert(MyStruct{ i: 3, j: 7 });
            assert(!res);

            let s2 = MyStruct{ i: 3, j: 7 };
            let ghost w: (MyStruct, int) = (MyStruct{ i: 3, j: 7 }, 10);
            assert(s1@ == w);
            assert(s2@ == w);
            assert(m@.contains(w));

            assert(m@.len() == 1);
            assert(m.len() == 1) by {
                vstd::hash_set::axiom_hash_set_with_view_spec_len(&m);
            }
            let n = m.len();
            assert(n == 1);

            let b = m.contains(&s2);
            assert(b);

            let v = m.get(&s2);
            match v {
                Some(v) => assert(*v == s2),
                None => assert(false),
            }

            let res = m.remove(&s2);
            assert(res);
            let res = m.remove(&s2);
            assert(!res);
            assert(!m@.contains(w));

            let s3 = MyStruct{ i: 3, j: 7 };
            let res = m.insert(s3);
            assert(res);
            let res = m.insert(MyStruct{ i: 3, j: 7 });
            assert(!res);
            m.clear();
            assert(!m@.contains(w));
            let b = m.contains(&s2);
            assert(!b);
        }
    } => Ok(_err) => { /* Clone warnings */ }
}

test_verify_one_file! {
    #[test] test_hash_map_with_view_fails verus_code! {
        use core::hash::{Hash, Hasher};
        use vstd::hash_map::HashMapWithView;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        pub struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        impl View for MyStruct
        {
            type V = (MyStruct, int);
            open spec fn view(&self) -> Self::V
            {
                (*self, self.i + self.j)
            }
        }

        fn test()
        {
            // Missing assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());

            let mut m = HashMapWithView::<MyStruct, u32>::new(); // FAILS
            let s = MyStruct{ i: 3, j: 7 };
            m.insert(s, 4);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_hash_set_with_view_fails verus_code! {
        use core::hash::{Hash, Hasher};
        use vstd::hash_set::HashSetWithView;
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        pub struct MyStruct
        {
            pub i: u16,
            pub j: i32,
        }

        impl Hash for MyStruct
        {
            #[verifier::external_body]
            fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher
            {
                self.i.hash(state);
                self.j.hash(state);
            }
        }

        impl View for MyStruct
        {
            type V = (MyStruct, int);
            open spec fn view(&self) -> Self::V
            {
                (*self, self.i + self.j)
            }
        }

        fn test()
        {
            // Missing assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>());

            let mut m = HashSetWithView::<MyStruct>::new(); // FAILS
            let s = MyStruct{ i: 3, j: 7 };
            m.insert(s);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_string_hash_map verus_code! {
        use vstd::hash_map::StringHashMap;
        use vstd::prelude::*;
        fn test()
        {
            let mut m = StringHashMap::<i8>::new();
            assert(m@ == Map::<Seq<char>, i8>::empty());

            let b = m.is_empty();
            assert(b);

            let three: String = "three".to_owned();
            let six: String = "six".to_owned();
            let previous = m.insert(three.clone(), 4);
            assert(previous.is_none());
            let previous = m.insert("three".to_owned(), 9);
            assert(previous == Some(4));

            let b = m.is_empty();
            assert(!b);

            m.insert(six.clone(), -8);
            assert(!(three@ =~= six@)) by {
                reveal_strlit("three");
                reveal_strlit("six");
            }
            assert(m@[three@] == 9);

            let b = m.contains_key(three.as_str());
            assert(b);

            assert(m.len() == 2);
            let n = m.len();
            assert(n == 2);

            let v = m.get(six.as_str());
            match v {
                Some(v) => assert(*v == -8),
                None => assert(false),
            };

            m.remove(six.as_str());
            assert(!m@.contains_key(six@));
            assert(m@.contains_key(three@));

            m.clear();
            assert(!m@.contains_key(three@));
            let b = m.contains_key(three.as_str());
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_hash_map_verified_operations verus_code! {
        use vstd::hash_map::StringHashMap;
        use vstd::prelude::*;

        fn test() {
            let key = "caf\u{e9}";
            let other = "tea";
            assert(key@ != other@) by {
                reveal_strlit("caf\u{e9}");
                reveal_strlit("tea");
            }
            let mut m = StringHashMap::<Vec<u8>>::with_capacity(2);
            m.reserve(4);
            let previous = m.insert(key.to_owned(), vec![1u8]);
            assert(previous.is_none());
            let previous = m.insert(key.to_owned(), vec![2u8]);
            let previous = previous.unwrap();
            assert(previous@ == seq![1u8]);
            let value = m.get(key).unwrap();
            assert(value@ == seq![2u8]);
            let count = m.len();
            assert(count == 1);

            let mut rhs = StringHashMap::<Vec<u8>>::new();
            rhs.insert(key.to_owned(), vec![3u8]);
            rhs.insert(other.to_owned(), vec![4u8]);
            m.union_prefer_right(rhs);
            let value = m.get(key).unwrap();
            assert(value@ == seq![3u8]);
            let value = m.get(other).unwrap();
            assert(value@ == seq![4u8]);
            assert(m@.dom() =~= set![key@, other@]);
            let count = m.len();
            assert(count == 2);

            m.remove(key);
            let present = m.contains_key(key);
            assert(!present);
            let value = m.get(key);
            assert(value.is_none());
            let ghost before = m@;
            m.remove(key);
            assert(m@ == before);
            let value = m.get(other).unwrap();
            assert(value@ == seq![4u8]);
            m.clear();
            let empty = m.is_empty();
            assert(empty);
            let count = m.len();
            assert(count == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_hash_map_requires_well_formed verus_code! {
        use vstd::hash_map::StringHashMap;
        use vstd::prelude::*;

        fn test_read(m: &StringHashMap<u32>) {
            let _ = m.get("key"); // FAILS
        }

        fn test_mutate(m: &mut StringHashMap<u32>, key: String) {
            m.insert(key, 1); // FAILS
        }

        fn test_union(m: &mut StringHashMap<u32>, other: StringHashMap<u32>)
            requires
                old(m).well_formed(),
        {
            m.union_prefer_right(other); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_hash_map_deep_view verus_code! {
        use std::collections::HashMap;
        use vstd::prelude::*;
        use vstd::std_specs::hash::*;

        fn test(m: HashMap<u64, Vec<bool>>, k: u64)
            requires
                m@.contains_key(k),
                m[k]@ == seq![true],
        {
            broadcast use lemma_hashmap_deepview_properties;
            assert(m.deep_view()[k] == seq![true]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_hash_set verus_code! {
        use vstd::hash_set::StringHashSet;
        use vstd::prelude::*;
        fn test()
        {
            let mut m = StringHashSet::new();
            assert(m@ == Set::<Seq<char>>::empty());

            let b = m.is_empty();
            assert(b);

            let three: String = "three".to_owned();
            let six: String = "six".to_owned();

            let res = m.insert(three.clone());
            assert(res);

            let b = m.is_empty();
            assert(!b);

            m.insert(six.clone());

            let res = m.insert("three".to_owned());
            assert(!res);

            assert(!(three@ =~= six@)) by {
                reveal_strlit("three");
                reveal_strlit("six");
                assert(three@.len() != six@.len());
            }

            let b = m.contains(three.as_str());
            assert(b);

            assert(m.len() == 2) by {
                vstd::hash_set::axiom_string_hash_set_spec_len(&m);
            }
            let n = m.len();
            assert(n == 2);

            let v = m.get(six.as_str());
            match v {
                Some(v) => assert((*v)@ == six@),
                None => assert(false),
            };

            let res = m.remove(six.as_str());
            assert(res);
            let res = m.remove(six.as_str());
            assert(!res);
            assert(!m@.contains(six@));
            assert(m@.contains(three@));

            m.clear();
            assert(!m@.contains(three@));
            let b = m.contains(three.as_str());
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_hash_map_keys ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::HashMap;
        use std::collections::hash_map::Keys;
        use vstd::prelude::*;
        use vstd::std_specs::hash::*;
        use vstd::std_specs::iter::IteratorSpec;
        fn test()
        {
            let mut m = HashMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            let m_keys = m.keys();

            let mut items = Vec::<u32>::new();
            for k in iter: m_keys
                invariant
                    items@ == iter.seq()[..iter.index()].unref(),
            {
                items.push(*k);
            }
            assert(items@.to_set() =~= set![3u32, 6u32]) by {
                assert(m_keys.remaining()[..m_keys.remaining().len()] == m_keys.remaining());
            }
            assert(items@.no_duplicates());
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_hash_map_values ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::HashMap;
        use std::collections::hash_map::Values;
        use vstd::prelude::*;
        use vstd::std_specs::hash::*;
        use vstd::std_specs::iter::IteratorSpec;
        fn test_values()
        {
            let mut m = HashMap::<u32, i8>::new();
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
            let mut items = Vec::<i8>::new();
            for v in iter: m_values
                invariant
                    items@ == iter.seq()[..iter.index()].unref(),
            {
                items.push(*v);
            }
            assert(items@.to_set() =~= set![4i8, -8i8]) by {
                assert(m_values.remaining()[..m_values.remaining().len()] == m_values.remaining());
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_hash_map_iter ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::HashMap;
        use std::collections::hash_map::Iter;
        use vstd::prelude::*;
        use vstd::std_specs::hash::*;
        use vstd::std_specs::iter::IteratorSpec;
        fn test_iter()
        {
            let mut m = HashMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            assert(m@.contains_pair(3u32, 4i8));
            assert(m@.contains_pair(6u32, -8i8));

            let mut idx = 0;
            for (k, v) in iter: m.iter()
                invariant
                    iter.seq().unref().to_set() =~= set![(3u32, 4i8), (6u32, -8i8)],
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
    #[test] test_hash_set_iter ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::HashSet;
        use std::collections::hash_set::Iter;
        use vstd::std_specs::iter::IteratorSpec;
        use vstd::prelude::*;
        use vstd::std_specs::hash::*;
        fn test_set()
        {
            let mut m = HashSet::<u32>::new();
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
    #[test] test_hash_map_decreases ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::HashMap;
        use vstd::prelude::*;
        use vstd::std_specs::hash::*;
        pub enum Foo {
            Base(i64),
            Rec(HashMap<i64, Foo>),
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
