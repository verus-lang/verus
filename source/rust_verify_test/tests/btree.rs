#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_btree_map verus_code! {
        use std::collections::BTreeMap;
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
    #[test] test_btree_set verus_code! {
        use std::collections::BTreeSet;
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
    #[test] test_btree_map_struct verus_code! {
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
            assume(vstd::laws_cmp::obeys_cmp_spec::<MyStruct>());

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
    #[test] test_btree_set_struct verus_code! {
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
            assume(vstd::laws_cmp::obeys_cmp_spec::<MyStruct>());

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
            // Missing `assume(vstd::laws_cmp::obeys_cmp_spec::<MyStruct>());`

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
            // Missing `assume(vstd::laws_cmp::obeys_cmp_spec::<MyStruct>());`

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
            let ghost m_keys = m.keys();
            let ghost g_keys = m_keys.remaining();
            assert(increasing_seq(g_keys));
            assert(g_keys.no_duplicates());

            // REVIEW: Needed because vstd lacks OrdSpec impl for &T
            assume(obeys_cmp_spec::<&u32>());
            assume(forall|a: &u32, b: &u32| (#[trigger] <&u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(&a, &b)) == <u32 as vstd::std_specs::cmp::OrdSpec>::cmp_spec(a, b));

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
                let mapped = g_keys.map_values(|v: &u32| *v);
                assert(mapped.to_set().contains(mapped[0]));
                assert(mapped.to_set().contains(mapped[1]));
                assert(g_keys =~= seq![&3u32, &6u32]);
            }

            let mut items = Vec::<u32>::new();
            for k in iter: m.keys()
                invariant
                    g_keys == iter.seq(),
                    items@ == iter.seq().take(iter.index@).map_values(|v: &u32| *v),
            {
                items.push(*k);
            }
            assert(items@ == seq![3u32, 6u32]) by {
                assert(g_keys.take(g_keys.len() as int) =~= g_keys);
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
                    items@ == iter.seq().take(iter.index@).map_values(|v: &i8| *v),
            {
                items.push(*v);
            }
            assert(items@ == seq![4i8, -8i8]) by {
                assert(g_values.take(g_values.len() as int) =~= g_values);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_btree_map_iter ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::BTreeMap;
        use std::collections::btree_map::Iter;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test()
        {
            let mut m = BTreeMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);

            let mut idx = 0;
            for (k, v) in iter: m.iter()
                invariant
                    iter.seq().map_values(|v: (&u32, &i8)| (*v.0, *v.1)).to_set() =~= set![(3u32, 4i8), (6u32, -8i8)],
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
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;
        use vstd::std_specs::btree::*;
        fn test()
        {
            let mut m = BTreeSet::<u32>::new();
            assert(m@ == Set::<u32>::empty());

            m.insert(3);
            m.insert(6);
            let ghost m_iter = m.iter();
            assert(m_iter.remaining().map_values(|v: &u32| *v).to_set() =~= set![3u32, 6u32]);
            
            let mut items = Vec::<u32>::new();

            for k in iter: m.iter()
                invariant
                    iter.seq().map_values(|v: &u32| *v).to_set() =~= set![3u32, 6u32],
                    items@ == iter.seq().take(iter.index@).map_values(|v: &u32| *v),
            {
                items.push(*k);
            }
            assert(items@.to_set() =~= set![3u32, 6u32]) by {
                assert(m_iter.remaining().take(m_iter.remaining().len() as int) == m_iter.remaining());
            }
            assert(items@.no_duplicates());
        }        
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_btree_map_decreases ["exec_allows_no_decreases_clause"] => verus_code! {
        use std::collections::BTreeMap;
        use vstd::prelude::*;
        use vstd::std_specs::btree::*;
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
