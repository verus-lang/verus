#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_vec_into_iter verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::vec::*;

        fn test() {
            let mut v1: Vec<u32> = Vec::new();
            let mut v2: Vec<u32> = Vec::new();
            v1.push(3);
            v1.push(4);
            assert(v1@ == seq![3u32, 4u32]);

            v2.push(5);
            assert(v2.len() == 1);
            v2.push(7);
            assert(v2@.len() == 2);
            v2.insert(1, 6);
            assert(v2@ == seq![5u32, 6u32, 7u32]);

            v1.append(&mut v2);
            assert(v2@.len() == 0);
            assert(v1@.len() == 5);
            assert(v1@ == seq![3u32, 4u32, 5u32, 6u32, 7u32]);
            v1.remove(2);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32]);

            v1.push(8u32);
            v1.push(9u32);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

            v1.swap_remove(5);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32]);

            let mut i: usize = 0;
            for x in it: v1
                invariant
                    i == it.index(),
                    it.seq() == seq![3u32, 4u32, 6u32, 7u32, 8u32],
            {
                assert(x > 2);
                assert(x < 10);
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_vec_dec verus_code! {
        use vstd::prelude::*;
        struct Tree {
            children: Vec<Tree>,
        }

        fn recurse(tree: &Tree)
            decreases *tree
        {
            if tree.children.len() > 0 {
                recurse(&tree.children[0]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_vec_as_ref verus_code! {
        use vstd::prelude::*;
        fn test(v: Vec<u8>) {
            let s: &[u8] = v.as_ref();
            assert(s@ == v@);
            assert(s@.len() == 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] clone_from_contracts verus_code! {
        use vstd::prelude::*;

        // Arbitrary lengths cover empty, growing, equal, shrinking, and clearing vectors.
        fn clone_from_lengths(dest: &mut Vec<u64>, source: &Vec<u64>) {
            let ghost before = source@;
            <Vec<u64> as Clone>::clone_from(dest, source);
            assert(dest@ == source@);
            assert(source@ == before);
            assert(*dest == *source); // FAILS: contents do not determine whole-Vec equality.
        }

        fn nested_containers(dest: &mut Vec<[u64; 3]>, source: &Vec<[u64; 3]>)
            ensures final(dest).deep_view() == source.deep_view(),
        {
            let nested = vec![vec![7u64, 8], vec![9u64]];
            let mut copy = vec![vec![1u64]];
            copy.clone_from(&nested);
            assert(copy.deep_view() == nested.deep_view());
            dest.clone_from(source);
        }

        pub struct Value { pub id: u64, pub scratch: u64 }
        impl View for Value {
            type V = u64;
            open spec fn view(&self) -> u64 { self.id }
        }
        impl Clone for Value {
            fn clone(&self) -> (result: Self)
                ensures result@ == self@,
            { Value { id: self.id, scratch: 0 } }
            fn clone_from(&mut self, source: &Self)
                ensures final(self)@ == source@,
            { self.id = source.id; }
        }

        fn update_generic<T: Clone + View>(dest: &mut T, source: &T)
            requires forall|source: T, previous: T, result: T|
                #[trigger] cloned_from(source, previous, result) ==> result@ == source@,
            ensures final(dest)@ == source@,
        {
            dest.clone_from(source);
            assert(cloned_from(*source, *old(dest), *dest));
        }

        fn grow(dest: &mut Vec<Value>, source: &Vec<Value>)
            requires old(dest).len() <= source.len(),
            ensures
                final(dest).len() == source.len(),
                forall|i: int| 0 <= i < source.len() ==> final(dest)@[i]@ == source@[i]@,
        {
            assert forall|source: Value, previous: Value, result: Value|
                #[trigger] cloned_from(source, previous, result) implies result@ == source@ by {}
            let mut value = Value { id: 0, scratch: 1 };
            update_generic(&mut value, &Value { id: 7, scratch: 2 });
            assert(value@ == 7);
            dest.clone_from(source);
        }
    } => Err(err) => assert_one_fails(err)
}

// Handwritten Clone plus Copy still calls clone_from for reused elements.
#[test]
fn handwritten_clone_and_copy_reuses_elements() {
    #[derive(Copy)]
    struct Value(u64);
    impl Clone for Value {
        fn clone(&self) -> Self {
            *self
        }
        fn clone_from(&mut self, _source: &Self) {
            self.0 = 0;
        }
    }
    let mut dest = vec![Value(1)];
    dest.clone_from(&vec![Value(7), Value(8)]);
    assert!(matches!(dest.as_slice(), [Value(0), Value(8)]));
}
