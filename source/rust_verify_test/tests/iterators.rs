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

// `len` does not run the closure of a `Map`, so `remaining()` (which stops at a closure that fails to return)
// may be shorter than `len`.  We can only equate them if the iterator will return None.
test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/3165
    #[test] len_needs_will_return_none verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::{IteratorSpec, filter_keep};

        #[verifier::exec_allows_no_decreases_clause]
        fn diverge()
            ensures
                false,
        {
            let b: bool = true;
            while b
                invariant
                    b,
            {
            }
        }

        fn len_direct() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let n = m.len();
            assert(n == 0); // FAILS
        }

        fn len_skip() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let s = m.skip(1);
            let n = s.len();
            assert(n == 0); // FAILS
        }

        fn len_mut_ref() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let n = (&mut m).len();
            assert(n == 0); // FAILS
        }

        fn len_rev() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let r = m.rev();
            let n = r.len();
            assert(n == 0); // FAILS
        }

        fn len_zip() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let mut w: Vec<u32> = vec![5, 6];
            let z = w.iter_mut().zip(m);
            let ghost gz = z;
            proof {
                assert(gz.remaining().len() == 0);
            }
            let n = z.len();
            assert(n == 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

// `next_back` starts at the other end, so it can succeed even if `remaining()` was truncated by
// a closure that fails to return on an earlier element.
test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/3165
    #[test] next_back_needs_will_return_none verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::{IteratorSpec, filter_keep};

        #[verifier::exec_allows_no_decreases_clause]
        fn diverge()
            ensures
                false,
        {
            let b: bool = true;
            while b
                invariant
                    b,
            {
            }
        }

        fn next_back_direct() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let r = m.next_back();
            assert(r is None); // FAILS
        }

        fn next_back_skip() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let mut s = m.skip(0);
            let r = s.next_back();
            assert(r is None); // FAILS
        }

        fn next_back_mut_ref() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let r = (&mut m).next_back();
            assert(r is None); // FAILS
        }

        fn filter_next_back() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let p = |x: &u32| -> (b: bool)
                ensures
                    *x != 1,
                {
                    if *x == 1 {
                        diverge();
                    }
                    true
                };
            let ghost gp = p;
            let mut m = it.filter(p);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                assert(forall|k| #![auto] 0 <= k < g.remaining().len() ==> call_requires(gp, (&g.remaining()[k],)));
                let keep = filter_keep(gm);
                if keep.len() > 0 {
                    assert(call_ensures(gp, (&g.remaining()[0],), keep[0]));
                    assert(false);
                }
                assert(keep.len() == 0);
                assert(gm.remaining().len() == 0);
            }
            let r = m.next_back();
            assert(r is None); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

// `Rev` calls `next_back`, so its `remaining()` is only the reverse of the inner `remaining()`
// if the inner iterator will return None.
test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/3165
    #[test] rev_needs_will_return_none verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::{IteratorSpec, filter_keep};

        #[verifier::exec_allows_no_decreases_clause]
        fn diverge()
            ensures
                false,
        {
            let b: bool = true;
            while b
                invariant
                    b,
            {
            }
        }

        fn rev_next() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let mut r = m.rev();
            let x = r.next();
            assert(x is None); // FAILS
        }

        fn rev_for_loop() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let r = m.rev();
            let ghost gr = r;
            proof {
                assert(gr.remaining().len() == 0); // FAILS
            }
            for x in iter: r
                invariant
                    iter.seq() == gr.remaining(),
                    gr.remaining().len() == 0,
            {
                // Reachable at runtime, since the closure returns on 2 (the first element of the reversed iterator)
                assert(false);
            }
        }

        fn rev_take_collect() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let ghost g = it;
            let f = |x: u32| -> (y: u32)
                ensures
                    x != 1,
                {
                    if x == 1 {
                        diverge();
                    }
                    x
                };
            let ghost gf = f;
            let mut m = it.map(f);
            let ghost gm = m;
            proof {
                assert(g.remaining()[0] == 1);
                if gm.remaining().len() > 0 {
                    assert(call_ensures(gf, (g.remaining()[0],), gm.remaining()[0]));
                    assert(false);
                }
                assert(gm.remaining().len() == 0);
            }
            let c: Vec<u32> = m.rev().take(1).collect();
            assert(c@.len() == 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

// Well-behaved iterators (which never run user closures) still get precise `len`/`next_back`/`rev` specs.
test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/3165
    #[test] len_next_back_rev_precise_for_simple_iterators verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn vec_into_iter_next_back() {
            let v: Vec<u32> = vec![1, 2];
            let mut it = v.into_iter();
            let r = it.next_back();
            assert(r == Some(2u32));
        }

        fn vec_into_iter_len() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.into_iter();
            let n = it.len();
            assert(n == 2);
        }

        fn vec_iter_next_back() {
            let v: Vec<u32> = vec![1, 2];
            let mut it = v.iter();
            let r = it.next_back();
            assert(r == Some(&2u32));
        }

        fn vec_iter_len() {
            let v: Vec<u32> = vec![1, 2];
            let it = v.iter();
            let n = it.len();
            assert(n == 2);
        }

        fn range_next_back() {
            let mut it = 0..3u32;
            let r = it.next_back();
            assert(r == Some(2u32));
        }

        fn vec_into_iter_rev_next() {
            let v: Vec<u32> = vec![1, 2];
            let mut it = v.into_iter().rev();
            let r = it.next();
            assert(r == Some(2u32));
        }

        fn rev_after_collect_on_map() {
            // `collect` establishes `will_return_none`, which makes the reversal precise
            let v: Vec<u32> = vec![1, 2];
            let w: Vec<u32> = v.into_iter().map(|x: u32| -> (y: u32) ensures y == x { x }).rev().collect();
            assert(w@ == seq![2u32, 1u32]);
        }
    } => Ok(())
}

// Closure preconditions must cover values reachable from the back, even when
// the inner iterator's forward prophecy is empty.
test_verify_one_file! {
    #[test] nested_adapters_require_completion_or_unconditional_callability verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        #[verifier::exec_allows_no_decreases_clause]
        fn diverge()
            ensures false,
        {
            loop {}
        }

        fn first(x: u32) -> (y: u32)
            ensures x != 1, y == x,
        {
            if x == 1 { diverge(); }
            x
        }

        fn nested_map() {
            let input = vec![1u32, 2, 3].into_iter();
            let ghost original = input;
            let middle = input.map(first);
            proof {
                if middle.remaining().len() > 0 {
                    assert(call_ensures(first, (original.remaining()[0],), middle.remaining()[0]));
                    assert(false);
                }
                assert(middle.remaining().len() == 0);
            }
            let second = |x: u32| -> u32
                requires x != 3,
            {
                if x == 3 {
                    assert(false);
                    panic!("");
                }
                x
            };
            let mut output = middle.map(second); // FAILS
            output.next_back();
        }

        fn nested_filter() {
            let input = vec![1u32, 2, 3].into_iter();
            let ghost original = input;
            let middle = input.map(first);
            proof {
                if middle.remaining().len() > 0 {
                    assert(call_ensures(first, (original.remaining()[0],), middle.remaining()[0]));
                    assert(false);
                }
                assert(middle.remaining().len() == 0);
            }
            let predicate = |x: &u32| -> bool
                requires *x != 3,
            { true };
            let mut output = middle.filter(predicate); // FAILS
            output.next_back();
        }

        fn filter_then_map() {
            let predicate = |x: &u32| -> (keep: bool)
                ensures *x != 1, keep,
            {
                if *x == 1 { diverge(); }
                true
            };
            let middle = vec![1u32, 2, 3].into_iter().filter(predicate);
            let second = |x: u32| -> u32
                requires x != 3,
            { x };
            let mut output = middle.map(second); // FAILS
            output.next_back();
        }

        fn through_skip() {
            let middle = vec![1u32, 2, 3].into_iter().map(first).skip(0);
            let second = |x: u32| -> u32
                requires x != 3,
            { x };
            let mut output = middle.map(second); // FAILS
            output.next_back();
        }

        fn through_take() {
            let middle = vec![1u32, 2, 3].into_iter().map(first).take(3);
            let second = |x: u32| -> u32
                requires x != 3,
            { x };
            let mut output = middle.map(second); // FAILS
            output.next_back();
        }

        fn through_rev() {
            let middle = vec![1u32, 2, 3].into_iter().map(first).rev();
            let second = |x: u32| -> u32
                requires x != 3,
            { x };
            let mut output = middle.map(second); // FAILS
            output.next();
        }

        fn through_mut_ref() {
            let mut middle = vec![1u32, 2, 3].into_iter().map(first);
            let second = |x: u32| -> u32
                requires x != 3,
            { x };
            let mut output = (&mut middle).map(second); // FAILS
            output.next_back();
        }

        fn through_zip() {
            let middle = vec![1u32, 2, 3].into_iter().map(first).zip(0..3u32);
            let second = |x: (u32, u32)| -> u32
                requires x.0 != 3,
            { x.0 };
            let mut output = middle.map(second); // FAILS
            output.next_back();
        }

        struct Unspecified;

        impl Iterator for Unspecified {
            type Item = u32;

            fn next(&mut self) -> Option<u32> { Some(3) }
        }

        impl vstd::std_specs::iter::IteratorSpecImpl for Unspecified {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }
            open spec fn remaining(&self) -> Seq<u32> { Seq::empty() }
            // Without the iterator laws, this completion claim cannot justify
            // checking closure preconditions against the empty sequence.
            open spec fn will_return_none(&self) -> bool { true }
            open spec fn decrease(&self) -> Option<nat> { None }
            open spec fn peek(&self, index: int) -> Option<u32> { None }
        }

        fn no_laws_means_arbitrary_inputs() {
            let second = |x: u32| -> u32
                requires x != 3,
            { x };
            let mut output = Unspecified.map(second); // FAILS
            output.next();
        }

        fn safe_partial_closure_is_conservatively_rejected() {
            let middle = vec![1u32, 2, 3].into_iter().map(first);
            let second = |x: u32| -> u32
                requires x != 1,
            { x };
            // This closure accepts every actual output of `first`, but without
            // completion, Option 1 requires it to accept every u32.
            let mut output = middle.map(second); // FAILS
            output.next_back();
        }
    } => Err(err) => assert_fails(err, 10)
}

test_verify_one_file! {
    #[test] unconditionally_callable_adapters_allow_backward_iteration_without_completion verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        #[verifier::exec_allows_no_decreases_clause]
        fn diverge()
            ensures false,
        {
            loop {}
        }

        fn first(x: u32) -> (y: u32)
            ensures x != 1, y == x,
        {
            if x == 1 { diverge(); }
            x
        }

        fn safe_nested_map() {
            let input = vec![1u32, 2, 3].into_iter();
            let ghost original = input;
            let middle = input.map(first);
            proof {
                if middle.remaining().len() > 0 {
                    assert(call_ensures(first, (original.remaining()[0],), middle.remaining()[0]));
                    assert(false);
                }
                assert(middle.remaining().len() == 0);
                assert(!middle.will_return_none());
            }
            let second = |x: u32| -> (y: u32)
                requires x <= u32::MAX,
                ensures y == x,
            { x };
            let mut output = middle.map(second);
            let _ = output.next_back();
        }

        fn safe_nested_filter_and_rev() {
            let middle = vec![1u32, 2, 3].into_iter().map(first);
            let predicate = |x: &u32| -> (keep: bool)
                requires *x <= u32::MAX,
                ensures keep,
            { true };
            let mut output = middle.filter(predicate).rev();
            let _ = output.next();
        }

        fn unconditionally_callable_after_next_back() {
            let mut middle = vec![1u32, 2, 3].into_iter().map(first);
            middle.next_back();
            let second = |x: u32| -> (y: u32)
                requires x <= u32::MAX,
                ensures y == x,
            { x };
            let mut output = middle.map(second);
            let _ = output.next_back();
        }

        fn completing_inputs_allow_partial_closures() {
            let input = vec![2u32, 3].into_iter();
            let mapped = input.map(|x: u32| -> (y: u32)
                requires x > 1,
                ensures y == x,
            { x });
            let values: Vec<u32> = mapped.collect();
            assert(values@ == seq![2u32, 3u32]);

            let input = vec![2u32, 3].into_iter();
            let filtered = input.filter(|x: &u32| -> (keep: bool)
                requires *x > 1,
                ensures keep,
            { true });
            let values: Vec<u32> = filtered.collect();
            proof { reveal_with_fuel(Seq::filter_index, 3); }
            assert(values@ == seq![2u32, 3u32]);
        }

        fn take_zero_supplies_a_complete_empty_input() {
            let input = vec![1u32, 2, 3].into_iter().map(first).take(0);
            assert(input.will_return_none());
            let mapped = input.map(|x: u32| -> u32
                requires false,
            { x });
            let values: Vec<u32> = mapped.collect();
            assert(values@.len() == 0);
        }

        fn zip_must_reach_the_completing_side() {
            let input = vec![1u32, 2, 3].into_iter();
            let ghost original = input;
            let middle = input.map(first);
            proof {
                if middle.remaining().len() > 0 {
                    assert(call_ensures(first, (original.remaining()[0],), middle.remaining()[0]));
                    assert(false);
                }
                assert(!middle.will_return_none());
            }
            let output = middle.zip(0..3u32);
            assert(!output.will_return_none());

            let input = vec![1u32, 2, 3].into_iter();
            let ghost original = input;
            let middle = input.map(first);
            proof {
                if middle.remaining().len() > 0 {
                    assert(call_ensures(first, (original.remaining()[0],), middle.remaining()[0]));
                    assert(false);
                }
                assert(!middle.will_return_none());
            }
            let output = (0..3u32).zip(middle);
            assert(!output.will_return_none());
        }

        fn zip_checks_the_first_side_before_the_second() {
            let input = vec![1u32].into_iter();
            let ghost original = input;
            let middle = input.map(first);
            proof {
                if middle.remaining().len() > 0 {
                    assert(call_ensures(first, (original.remaining()[0],), middle.remaining()[0]));
                    assert(false);
                }
                assert(!middle.will_return_none());
            }
            let mut output = Vec::<u32>::new().into_iter().zip(middle);
            assert(output.will_return_none());
            let result = output.next();
            assert(result is None);

            let input = vec![1u32].into_iter();
            let ghost original = input;
            let middle = input.map(first);
            proof {
                if middle.remaining().len() > 0 {
                    assert(call_ensures(first, (original.remaining()[0],), middle.remaining()[0]));
                    assert(false);
                }
                assert(!middle.will_return_none());
            }
            let output = middle.zip(Vec::<u32>::new().into_iter());
            assert(!output.will_return_none());
        }
    } => Ok(())
}
