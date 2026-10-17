#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] all_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.all(
                |i: u32| -> (ret: bool)
                    ensures ret == (i < 10)
                {i < 10}
            );
            if v_result {
                // If `all` returned true, every element was below 10.
                assert(forall |i| 0 <= i < v.len() ==> v[i] < 10);
            } else {
                // If `all` returned false, at least one element was >= 10.
                // The witness is the (consumed) element that failed the predicate.
                let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                assert(0 <= idx < v.len() && v[idx] >= 10);
                assert(exists |i| 0 <= i < v.len() && v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] any_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.any(
                |i: u32| -> (ret: bool)
                    ensures ret == (i < 10)
                {i < 10}
            );
            if v_result {
                // If `any` returned true, at least one element was below 10.
                // The witness is the (consumed) element that satisfied the predicate.
                let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                assert(0 <= idx < v.len() && v[idx] < 10);
                assert(exists |i| 0 <= i < v.len() && v[i] < 10);
            } else {
                // If `any` returned false, every element was >= 10.
                assert(forall |i| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] chars_next_falls_back_to_iterator_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(s: &str)
            requires
                s@.len() >= 1,
        {
            let mut it = s.chars();
            assert(it.remaining() == s@);
            let r = it.next();
            assert(r == Some(s@[0]));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] collect_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().collect();
            assert(v@ == w@);
            let x: Vec<u32> = w.into_iter().rev().collect();
            assert(x@ == seq![4u32, 3, 2, 1]);

            let y: Vec<u32> = vec![1, 2, 3, 4];
            let z: Vec<u32> = y.into_iter().rev().rev().collect();
            assert(z@ == y@);
        }
    } => Ok(())
}

// Regression tests for issue #3165.
test_verify_one_file! {
    #[test] from_iter_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        fn direct() {
            let v = vec![1u8, 2, 3];
            let w: Vec<u8> = Vec::from_iter(v.into_iter());
            assert(w@ == v@);
        }

        fn mut_ref() {
            let v = vec![1u8, 2, 3];
            let mut it = v.into_iter();
            let x: Vec<u8> = Vec::from_iter(&mut it);
            assert(x@ == v@);
        }

        fn zip() {
            let v = vec![1u8, 2, 3];
            let y: Vec<(u8, u8)> = Vec::from_iter(v.into_iter().zip(vec![4u8, 5]));
            assert(y@ == seq![(1u8, 4u8), (2, 5)]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] from_iter_requires_iterator_laws verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        pub struct It;

        impl Iterator for It {
            type Item = u8;

            fn next(&mut self) -> Option<u8> {
                None
            }
        }

        impl IteratorSpecImpl for It {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }

            #[verifier::prophetic]
            open spec fn remaining(&self) -> Seq<u8> { seq![7u8] }

            #[verifier::prophetic]
            open spec fn will_return_none(&self) -> bool { true }

            open spec fn decrease(&self) -> Option<nat> { None }

            open spec fn peek(&self, index: int) -> Option<u8> { None }
        }

        fn direct() {
            let v: Vec<u8> = Vec::from_iter(It);
            assert(v.len() == 1); // FAILS
        }

        fn mut_ref() {
            let mut it = It;
            let v: Vec<u8> = Vec::from_iter(&mut it);
            assert(v.len() == 1); // FAILS
        }

        fn zip() {
            let w = vec![1u8, 2];
            let v: Vec<(u8, u8)> = Vec::from_iter(w.into_iter().zip(It));
            assert(v.len() == 1); // FAILS
        }

        proof fn explicit_axiom_call() {
            from_iter_ensures::<u8, It>(It); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] from_iter_remaining_is_prophetic verus_code! {
        use vstd::modes::tracked_swap;
        use vstd::prelude::*;
        use vstd::proph::ProphecyGhost;
        use vstd::std_specs::iter::*;

        pub struct IterCtr {
            pub count: u64,
            pub len: Tracked<ProphecyGhost<nat>>,
        }

        impl Iterator for IterCtr {
            type Item = u64;

            fn next(&mut self) -> (ret: Option<u64>) {
                proof {
                    let tracked mut new = ProphecyGhost::new();
                    tracked_swap(&mut new, &mut self.len);
                    new.resolve_dependent(&self.len, |x: nat| (x + 1) as nat);
                }
                let ret = self.count;
                if self.count == u64::MAX {
                    self.count = 0;
                } else {
                    self.count = self.count + 1;
                }
                Some(ret)
            }
        }

        impl IteratorSpecImpl for IterCtr {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool { true }

            #[verifier::prophetic]
            open spec fn remaining(&self) -> Seq<u64> {
                Seq::new(self.len@.value(), |i: int|
                    ((i + self.count) % (u64::MAX as int + 1)) as u64)
            }

            open spec fn will_return_none(&self) -> bool { false }

            open spec fn decrease(&self) -> Option<nat> { None }

            open spec fn peek(&self, index: int) -> Option<u64> {
                Some((index % (u64::MAX as int + 1)) as u64)
            }
        }

        fn paradox() {
            let it = IterCtr { count: 0, len: Tracked(ProphecyGhost::new()) };
            let ghost g = it;
            let ghost n = into_iter_remaining::<u64, IterCtr>(g).len();
            let IterCtr { count, len } = it;
            proof {
                from_iter_ensures::<u64, IterCtr>(g);
                let tracked l = len.get();
                l.resolve((n + 1) as nat);
                assert(IteratorSpec::remaining(&g).len() == g.len@.value());
                assert(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for argument to proof-mode function with tracked parameters")
}

test_verify_one_file! {
    #[test] from_iter_into_iterator_can_vary code! {
        use vstd::prelude::*;
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        verus! {
            pub struct Src;

            fn two() -> (r: (Vec<u64>, Vec<u64>))
                ensures r.0@ == r.1@, // FAILS
            {
                let a: Vec<u64> = Vec::from_iter(Src);
                let b: Vec<u64> = Vec::from_iter(Src);
                (a, b)
            }
        }

        impl IntoIterator for Src {
            type Item = u64;
            type IntoIter = std::vec::IntoIter<u64>;

            fn into_iter(self) -> Self::IntoIter {
                vec![COUNTER.fetch_add(1, Ordering::SeqCst)].into_iter()
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] filter_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        fn test() {
            let p = |x: &u32| -> (b: bool)
                ensures b == (*x % 2 == 0)
            { *x % 2 == 0 };

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().filter(p)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w.len() <= 4);
            assert(forall |i| 0 <= i < w.len() ==> w[i] % 2 == 0);
            assert(forall |i| #![auto] 0 <= i < w.len() ==> v@.contains(w[i]));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] find_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let v_result = v.into_iter().find(
                |i| -> (ret: bool)
                ensures ret == (*i < 10)
                {*i < 10}
            );
            if let Some(i) = v_result {
                assert(i < 10);
                assert(v@.contains(i));
            } else {
                assert(forall |i| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] find_map_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.find_map(
                |x| -> (ret: Option<u32>)
                    ensures ret == if x % 4 == 0 { Some(x / 4) } else { None },
                {
                    if x % 4 == 0 { Some(x / 4) } else { None }
                }
            );
            match v_result {
                Some(r) => {
                    // If `find_map` returned Some, it must have stopped at a valid element.
                    let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                    // find_map stopped at a valid element.
                    assert(0 <= idx < v.len());
                    // That element produced the returned Some value.
                    assert(v[idx] % 4 == 0);
                    assert(r == v[idx] / 4);
                    // Every previous element produced None.
                    assert(forall |j| 0 <= j < idx ==> v[j] % 4 != 0);
                }
                None => {
                    // If `find_map` returned None, every element mapped to None.
                    assert(forall |j| 0 <= j < v.len() ==> v[j] % 4 != 0);
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] map_works verus_code! {
        use vstd::prelude::*;

        fn double_it() {
            let v = vec![1u32, 2, 3, 4];
            let mut w = Vec::new();
            for x in iter: v.iter().map(|x: &u32| -> (y: u32) requires *x < 10, ensures y == x * 2 { *x * 2 })
                invariant
                    w.len() == iter.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == v[i] * 2,
            {
                w.push(x);
            }
            assert(w@ == seq![2u32, 4, 6, 8]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mut_ref_forwarding verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        pub fn next_test<I: Iterator>(i: &mut I)
            requires
                i.obeys_prophetic_iter_laws(),
                i.will_return_none(),
            ensures
                // TODO: The number of operators needed here is unfortunate
                (&(*final(i))).obeys_prophetic_iter_laws(),
                (&(*final(i))).will_return_none(),
        {
            i.next();

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] position_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>) {
            let v_result = v.into_iter().position(
                |i| -> (ret: bool)
                ensures ret == (i < 10),
                {i < 10},
            );
            if let Some(index) = v_result {
                assert(index < v.len());
                assert(v@.contains(v[index as int]));
                assert(v[index as int] < 10);
                assert(forall |i: int| 0 <= i < index as int ==> v[i] >= 10);
            } else {
                assert(forall |i: int| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] range_works verus_code! {
        use vstd::prelude::*;

        fn test()
        {
            let mut v = vec![];
            for i in iter: 0..4
            invariant
                v.len() == iter.index(),
                iter.index() <= 4,
            {
                assert(i < 4);
                v.push(i);
            }
            assert(v.len() == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] range_inclusive_works verus_code! {
        use vstd::prelude::*;

        fn test()
        {
            let mut v = vec![];
            for i in iter: 0..=4
            invariant
                v.len() == iter.index(),
                i <= 5,
            {
                assert(i <= 4);
                v.push(i);
            }
            assert(v.len() == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] skip_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().skip(2).collect();
            assert(w@ == seq![3, 4]);


            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().skip(2)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w@ == seq![3, 4]);

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().skip(2).rev().collect();
            assert(w@ == seq![4u32, 3]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] take_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().take(2).collect();
            assert(w@ == seq![1, 2]);


            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().take(3)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w@ == seq![1, 2, 3]);

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().take(2).rev().collect();
            assert(w@ == seq![2u32, 1]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] take_skip verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test<I: Iterator>(v: Vec<u32>, n: usize)
            requires
                n <= v.len(),
        {
            // Creusot:
            //   assert!(iter.take(n).skip(n).next().is_none())
            // Verus:
            let mut r = v.into_iter().take(n).skip(n);
            assert(r.remaining().len() == 0);
            let out = r.next();
            assert(out is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vec_iter_mut_works verus_code! {
        use vstd::prelude::*;

        fn client_for_loop() {
            let mut v: Vec<u32> = vec![1, 2, 3, 4];
            for x in it: v.iter_mut()
                invariant
                    forall |i: int| #![auto] 0 <= i < it.index() ==> *final(it.seq()[i]) == 0,
            {
                *x = 0;
            }
            assert(forall |i: int| 0 <= i < v.len() ==> v[i] == 0);
            assert(v@ == seq![0, 0, 0, 0]);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] zip_works verus_code! {
        use vstd::prelude::*;

        fn zip_works() {
            let x1 = vec![1u32, 2, 3];
            let x2 = vec![2u32, 4, 6];
            let y1 = vec![2u32, 4, 6];
            let y2 = vec![1u32, 2];
            let z1 = vec![1u32, 2];
            let z2 = vec![2u32, 4, 6, 8, 10];

            let x: Vec<(u32, u32)> = x1.into_iter().zip(x2).collect();
            assert(x@ == seq![(1u32,2u32), (2, 4), (3, 6)]);

            let y: Vec<(u32, u32)> = y1.into_iter().zip(y2).collect();
            assert(y@ == seq![(2u32,1u32), (4, 2)]);

            let z: Vec<(u32, u32)> = z1.into_iter().zip(z2).collect();
            assert(z@ == seq![(1u32,2u32), (2, 4)]);
        }
    } => Ok(())
}
