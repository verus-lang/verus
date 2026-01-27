#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] temporary_place_in_assign ["new-mut-ref"] => verus_code! {
        fn mut_ref_pairs<'a, 'b>(a: &'a mut u64, b: &'b mut u64) -> (ret: (&'a mut u64, &'b mut u64))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *mut_ref_pairs(&mut a, &mut b).0 = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test1_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *mut_ref_pairs(&mut a, &mut b).0 = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *(&mut a) = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test2_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *(&mut a) = 5;

            assert(a == 5);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            // this does nothing; `(a, b)` creates a temporary,
            // so this only assigns to the temporary
            (a, b).0 = 5;

            assert(a == 0);
            assert(b == 0);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            (a, b).0 = 5;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *(&mut a, &mut b).0 = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *(&mut a, &mut b).0 = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            *({ y = y + 1; (&mut a, &mut b) }).0 = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            *({ y = y + 1; (&mut a, &mut b) }).0 = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *({ a = a + 1; (&mut a, &mut b) }).0 = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *({ a = a + 1; (&mut a, &mut b) }).0 = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            *({ y = y + 1; &mut a }) = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            *({ y = y + 1; &mut a }) = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *({ a = a + 1; &mut a }) = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test8_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            *({ a = a + 1; &mut a }) = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        spec fn arbitrary_pair() -> (u64, u64) { (10u64, 12u64) }

        fn test9() {
            proof { arbitrary_pair().0 = 3u64; }
            assert(false); // FAILS
        }

    } => Err(e) => assert_fails(e, 9)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_assign_op ["new-mut-ref"] => verus_code! {
        fn mut_ref_pairs<'a, 'b>(a: &'a mut u64, b: &'b mut u64) -> (ret: (&'a mut u64, &'b mut u64))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *mut_ref_pairs(&mut a, &mut b).0 += 5;

            assert(a == 6);
            assert(b == 1);
        }

        fn test1_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *mut_ref_pairs(&mut a, &mut b).0 += 5;

            assert(a == 6);
            assert(b == 1);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *(&mut a) += 5;

            assert(a == 6);
            assert(b == 1);
        }

        fn test2_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *(&mut a) += 5;

            assert(a == 6);
            assert(b == 1);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            // this does nothing; `(a, b)` creates a temporary, so this only assigns to the temporary
            (a, b).0 += 5;

            assert(a == 1);
            assert(b == 1);
        }

        fn test3_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            // this does nothing; `(a, b)` creates a temporary, so this only assigns to the temporary
            (a, b).0 += 5;

            assert(a == 1);
            assert(b == 1);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *(&mut a, &mut b).0 += 5;

            assert(a == 6);
            assert(b == 1);
        }

        fn test4_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *(&mut a, &mut b).0 += 5;

            assert(a == 6);
            assert(b == 1);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            let mut y = 0;

            *({ y = y + 1; (&mut a, &mut b) }).0 += 5;

            assert(y == 1);
            assert(a == 6);
            assert(b == 1);
        }

        fn test5_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            let mut y = 0;

            *({ y = y + 1; (&mut a, &mut b) }).0 += 5;

            assert(y == 1);
            assert(a == 6);
            assert(b == 1);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *({ a = a + 1; (&mut a, &mut b) }).0 += 5;

            assert(a == 7);
            assert(b == 1);
        }

        fn test6_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *({ a = a + 1; (&mut a, &mut b) }).0 += 5;

            assert(a == 7);
            assert(b == 1);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            let mut y = 0;

            *({ y = y + 1; &mut a }) += 5;

            assert(y == 1);
            assert(a == 6);
            assert(b == 1);
        }

        fn test7_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            let mut y = 0;

            *({ y = y + 1; &mut a }) += 5;

            assert(y == 1);
            assert(a == 6);
            assert(b == 1);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *({ a = a + 1; &mut a }) += 5;

            assert(a == 7);
            assert(b == 1);
        }

        fn test8_fails() {
            let mut a: u64 = 1;
            let mut b: u64 = 1;

            *({ a = a + 1; &mut a }) += 5;

            assert(a == 7);
            assert(b == 1);
            assert(false); // FAILS
        }

        spec fn arbitrary_pair() -> (u64, u64) { (10u64, 12u64) }

        fn test9() {
            proof { arbitrary_pair().0 += 3u64; }
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 9)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_assign_op_with_overflow ["new-mut-ref"] => verus_code! {
        fn mut_ref_pairs<'a, 'b>(a: &'a mut u8, b: &'b mut u8) -> (ret: (&'a mut u8, &'b mut u8))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a: u8 = 200;
            let mut b: u8 = 200;

            *mut_ref_pairs(&mut a, &mut b).0 += 200; // FAILS
        }

        fn test2() {
            let mut a: u8 = 200;
            let mut b: u8 = 200;

            *(&mut a) += 100; // FAILS
        }

        fn test3() {
            let mut a: u8 = 200;
            let mut b: u8 = 200;

            // this does nothing; `(a, b)` creates a temporary, so this only assigns to the temporary
            (a, b).0 += 200; // FAILS
        }

        fn test4() {
            let mut a: u8 = 200;
            let mut b: u8 = 1;

            *(&mut a, &mut b).0 += 100; // FAILS
        }

        fn test5() {
            let mut a: u8 = 1;
            let mut b: u8 = 1;

            let mut y = 0;

            *({ y = y + 1; (&mut a, &mut b) }).0 += 255; // FAILS
        }

        fn test6() {
            let mut a: u8 = 100;
            let mut b: u8 = 1;

            *({ a = a + 100; (&mut a, &mut b) }).0 += 100; // FAILS
        }

        fn test7() {
            let mut a: u8 = 200;
            let mut b: u8 = 1;

            let mut y = 0;

            *({ y = y + 1; &mut a }) += 100; // FAILS
        }

        fn test8() {
            let mut a: u8 = 100;

            *({ a = a + 100; &mut a }) += 100; // FAILS
        }

        spec fn arbitrary_pair() -> (u8, u8) { (200u8, 12u8) }

        fn test9() {
            proof {
                // this is ok because it's spec code
                arbitrary_pair().0 += 56u8;
            }
        }
    } => Err(e) => assert_fails(e, 8)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_move ["new-mut-ref"] => verus_code! {
        fn mut_ref_pairs<'a, 'b>(a: &'a mut u64, b: &'b mut u64) -> (ret: (&'a mut u64, &'b mut u64))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn update1(a: &mut u64)
            ensures mut_ref_future(a) == 10,
        {
            *a = 10;
        }

        fn update2(a: (&mut u64, &mut u64))
            ensures
               mut_ref_future(a.0) == 20,
               mut_ref_future(a.1) == 30,
        {
            *a.0 = 20;
            *a.1 = 30;
        }

        fn update_add_10(a: &mut u64)
            requires mut_ref_current(a) < 100
            ensures mut_ref_future(a) == mut_ref_current(a) + 10
        {
            *a = *a + 10;
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update1(mut_ref_pairs(&mut a, &mut b).0);

            assert(a == 10);
            assert(b == 0);
        }

        fn test1_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update1(mut_ref_pairs(&mut a, &mut b).0);

            assert(a == 10);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update1(({ &mut a }));

            assert(a == 10);
            assert(b == 0);
        }

        fn test2_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update1(({ &mut a }));

            assert(a == 10);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update1((&mut a, &mut b).0);

            assert(a == 10);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update1((&mut a, &mut b).0);

            assert(a == 10);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            update2({ y = y + 1; (&mut a, &mut b) });

            assert(y == 1);
            assert(a == 20);
            assert(b == 30);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            update2({ y = y + 1; (&mut a, &mut b) });

            assert(y == 1);
            assert(a == 20);
            assert(b == 30);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update_add_10(({ a = a + 1; (&mut a, &mut b) }).0);

            assert(a == 11);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update_add_10(({ a = a + 1; (&mut a, &mut b) }).0);

            assert(a == 11);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            update_add_10(({ y = y + 1; &mut a }));

            assert(y == 1);
            assert(a == 10);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            update_add_10(({ y = y + 1; &mut a }));

            assert(y == 1);
            assert(a == 10);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update_add_10({ a = a + 1; &mut a });

            assert(a == 11);
            assert(b == 0);
        }

        fn test9() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            update_add_10({ a = a + 1; &mut a });

            assert(a == 11);
            assert(b == 0);
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 7)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_ctor_update_tail ["new-mut-ref"] => verus_code! {
        broadcast proof fn stronger_resolver_axiom<A, B>(pair: TGPair<A, B>) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.t)
        {
        }

        proof fn consume_tracked<A>(tracked a: A) { }

        tracked struct TGPair<A, B> {
            tracked t: A,
            ghost g: B,
        }

        struct Pair<A, B> {
            a: A,
            b: B,
        }

        fn mut_ref_pairs<'a, 'b>(a: &'a mut u64, b: &'b mut u64) -> (ret: Pair<&'a mut u64, &'b mut u64>)
            ensures
                mut_ref_current(ret.a) == mut_ref_current(a),
                mut_ref_future(ret.a) == mut_ref_future(a),
                mut_ref_current(ret.b) == mut_ref_current(b),
                mut_ref_future(ret.b) == mut_ref_future(b),
        {
            Pair { a: a, b: b }
        }

        fn mut_ref_pairs2<'a, 'b, 'c, 'd>(a: &'a mut u64, b: &'b mut u64, c: &'c mut u64, d: &'d mut u64) -> (ret: (Pair<&'a mut u64, &'b mut u64>, Pair<&'c mut u64, &'d mut u64>))
            ensures
                mut_ref_current(ret.0.a) == mut_ref_current(a),
                mut_ref_future(ret.0.a) == mut_ref_future(a),
                mut_ref_current(ret.0.b) == mut_ref_current(b),
                mut_ref_future(ret.0.b) == mut_ref_future(b),
                mut_ref_current(ret.1.a) == mut_ref_current(c),
                mut_ref_future(ret.1.a) == mut_ref_future(c),
                mut_ref_current(ret.1.b) == mut_ref_current(d),
                mut_ref_future(ret.1.b) == mut_ref_future(d),
        {
            (Pair { a: a, b: b }, Pair { a: c, b: d })
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. mut_ref_pairs(&mut b, &mut c)
            };
            *z.a = 1;
            *z.b = 2;

            assert(a == 1);
            assert(c == 2);
            assert(b == 0);
        }

        fn test1_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. mut_ref_pairs(&mut b, &mut c)
            };
            *z.a = 1;
            *z.b = 2;

            assert(a == 1);
            assert(c == 2);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            *(Pair {
                a: &mut a,
                .. mut_ref_pairs(&mut b, &mut c)
            }).a = 20;

            assert(a == 20);
            assert(b == 0);
            assert(c == 0);
        }

        fn test2_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            *(Pair {
                a: &mut a,
                .. mut_ref_pairs(&mut b, &mut c)
            }).a = 20;

            assert(a == 20);
            assert(b == 0);
            assert(c == 0);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            *(Pair {
                a: &mut a,
                .. mut_ref_pairs(&mut b, &mut c)
            }).b = 20;

            assert(a == 0);
            assert(b == 0);
            assert(c == 20);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            *(Pair {
                a: &mut a,
                .. mut_ref_pairs(&mut b, &mut c)
            }).b = 20;

            assert(a == 0);
            assert(b == 0);
            assert(c == 20);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. Pair { a: &mut b, b: &mut c }
            };
            *z.a = 1;
            *z.b = 2;

            assert(a == 1);
            assert(c == 2);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. Pair { a: &mut b, b: &mut c }
            };
            *z.a = 1;
            *z.b = 2;

            assert(a == 1);
            assert(c == 2);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;
            let mut d: u64 = 0;
            let mut e: u64 = 0;

            *(Pair {
                a: &mut a,
                .. mut_ref_pairs2(&mut b, &mut c, &mut d, &mut e).0
            }).a = 20;

            assert(a == 20);
            assert(b == 0);
            assert(c == 0);
            assert(d == 0);
            assert(e == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;
            let mut d: u64 = 0;
            let mut e: u64 = 0;

            *(Pair {
                a: &mut a,
                .. mut_ref_pairs2(&mut b, &mut c, &mut d, &mut e).0
            }).a = 20;

            assert(a == 20);
            assert(b == 0);
            assert(c == 0);
            assert(d == 0);
            assert(e == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;
            let mut y: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. ({ y = y + 1; Pair { a: &mut b, b: &mut c } })
            };
            *z.a = 1;
            *z.b = 2;

            assert(a == 1);
            assert(c == 2);
            assert(b == 0);
            assert(y == 1);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;
            let mut y: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. ({ y = y + 1; Pair { a: &mut b, b: &mut c } })
            };
            *z.a = 1;
            *z.b = 2;

            assert(a == 1);
            assert(c == 2);
            assert(b == 0);
            assert(y == 1);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. ({ c = c + 1; Pair { a: &mut b, b: &mut c } })
            };
            *z.a = 1;
            *z.b += 8;

            assert(a == 1);
            assert(c == 9);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let z = Pair {
                a: &mut a,
                .. ({ c = c + 1; Pair { a: &mut b, b: &mut c } })
            };
            *z.a = 1;
            *z.b += 8;

            assert(a == 1);
            assert(c == 9);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;
            let c_ref = &mut c;

            let tracked z = TGPair {
                t: a_ref,
                .. TGPair { t: b_ref, g: c_ref }
            };
            proof { consume_tracked(z); }

            broadcast use stronger_resolver_axiom;

            assert(a == 0); // FAILS
            assert(b == 0);
            assert(c == 0);
        }

        fn test9() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let mut c: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;
            let c_ref = &mut c;

            let tracked z = TGPair {
                g: a_ref,
                .. TGPair { t: b_ref, g: c_ref }
            };
            proof { consume_tracked(z); }

            assert(b == 0);  // FAILS
        }
    } => Err(e) => assert_fails(e, 9)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_let_stmt ["new-mut-ref"] => verus_code! {
        broadcast proof fn stronger_resolver_axiom<A, B>(pair: (A, B)) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.0) && has_resolved(pair.1)
        { }

        broadcast proof fn stronger_resolver_axiom2<A, B>(pair: TGPair<A, B>) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.t)
        { }

        fn consume<A>(a: A) { }

        uninterp spec fn arbitrary<A>() -> A;

        tracked struct TGPair<A, B> {
            tracked t: A,
            ghost g: B,
        }

        proof fn id_tg_pair<A, B>(tracked a: A, b: B) -> (tracked ret: TGPair<A, B>)
            ensures ret == (TGPair { t: a, g: b })
        {
            TGPair { t: a, g: b }
        }


        fn id_pair<A, B>(a: A, b: B) -> (ret: (A, B))
            ensures ret == (a, b)
        {
            (a, b)
        }

        fn mut_ref_pairs<'a, 'b>(a: &'a mut u64, b: &'b mut u64) -> (ret: (&'a mut u64, &'b mut u64))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = mut_ref_pairs(&mut a, &mut b).0;

            *x = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test1_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = mut_ref_pairs(&mut a, &mut b).0;

            *x = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test2<A, B>(a: A, b: B) {
            let x = id_pair(a, b).0;

            assert(has_resolved(a));
            assert(has_resolved(b));
        }

        fn test2_fails<A, B>(a: A, b: B) {
            let x = id_pair(a, b).0;

            assert(has_resolved(a));
            assert(has_resolved(b));
            assert(false); // FAILS
        }

        fn test3<A, B>(a: A, b: B) {
            let x = id_pair(a, b).0;
            consume(x);

            assert(has_resolved(a)); // FAILS
            assert(has_resolved(b));
        }

        fn test3_fails<A, B>(a: A, b: B) {
            let x = id_pair(a, b).0;
            consume(x);

            assert(has_resolved(a)); // FAILS
            assert(has_resolved(b));
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = (&mut a, &mut b).0;

            *x = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = (&mut a, &mut b).0;

            *x = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let x = ({ y = y + 1; (&mut a, &mut b) }).0;

            *x = 5;

            assert(a == 5);
            assert(b == 0);
            assert(y == 1);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let x = ({ y = y + 1; (&mut a, &mut b) }).0;

            *x = 5;

            assert(a == 5);
            assert(b == 0);
            assert(y == 1);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = ({ a = a + 1; (&mut a, &mut b) }).0;

            *x = *x + 5;

            assert(a == 6);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = ({ a = a + 1; (&mut a, &mut b) }).0;

            *x = *x + 5;

            assert(a == 6);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let ghost x = arbitrary::<(&mut u64, &mut u64)>().0;
            assert(has_resolved(x)); // FAILS
        }

        fn test8() {
            let ghost x = arbitrary::<(&mut u64, &mut u64)>().0;
            assert(has_resolved(arbitrary::<(&mut u64, &mut u64)>().1)); // FAILS
        }

        fn test9() {
            let mut a = 0;
            let g: Ghost<u64> = Ghost(0);
            let x = id_pair(&mut a, g).1;

            broadcast use stronger_resolver_axiom;
            assert(a == 0);
        }

        fn test9_fails() {
            let mut a = 0;
            let g: Ghost<u64> = Ghost(0);
            let x = id_pair(&mut a, g).1;

            broadcast use stronger_resolver_axiom;
            assert(a == 0);
            assert(false); // FAILS
        }

        proof fn test10<A>(tracked a0: A) {
            let g: Ghost<u64> = Ghost(0);
            let x = id_tg_pair(a0, g).g;

            broadcast use stronger_resolver_axiom2;
            assert(has_resolved(a0));
        }

        proof fn test10_fails<A>(tracked a0: A) {
            let g: Ghost<u64> = Ghost(0);
            let x = id_tg_pair(a0, g).g;

            broadcast use stronger_resolver_axiom2;
            assert(has_resolved(a0));
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 12)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_let_stmt_with_pattern ["new-mut-ref"] => verus_code! {
        broadcast proof fn stronger_resolver_axiom<A, B>(pair: TGPair<A, B>) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.t)
        {
        }

        tracked struct TGPair<A, B> {
            tracked t: A,
            ghost g: B,
        }

        spec fn id<A>(a: A) -> A { a }

        fn mut_ref_pairs2<'a, 'b, 'c, 'd>(a: &'a mut u64, b: &'b mut u64, c: &'c mut u64, d: &'d mut u64) -> (ret: ((&'a mut u64, &'b mut u64), (&'c mut u64, &'d mut u64)))
            ensures
                mut_ref_current(ret.0.0) == mut_ref_current(a),
                mut_ref_future(ret.0.0) == mut_ref_future(a),
                mut_ref_current(ret.0.1) == mut_ref_current(b),
                mut_ref_future(ret.0.1) == mut_ref_future(b),
                mut_ref_current(ret.1.0) == mut_ref_current(c),
                mut_ref_future(ret.1.0) == mut_ref_future(c),
                mut_ref_current(ret.1.1) == mut_ref_current(d),
                mut_ref_future(ret.1.1) == mut_ref_future(d),
        {
            ((a, b), (c, d))
        }

        fn test1() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let (x, y) = mut_ref_pairs2(&mut a, &mut b, &mut c, &mut d).0;
            assert(*x == 0);
            assert(*y == 1);
            *x = 10;
            *y = 12;

            assert(a == 10);
            assert(b == 12);
            assert(c == 2);
            assert(d == 3);
        }

        fn test1_fails() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let (x, y) = mut_ref_pairs2(&mut a, &mut b, &mut c, &mut d).0;
            assert(*x == 0);
            assert(*y == 1);
            *x = 10;
            *y = 12;

            assert(a == 10);
            assert(b == 12);
            assert(c == 2);
            assert(d == 3);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let (x, y) = (&mut a, &mut b);
            *x = 3;
            *y = 4;

            assert(a == 3);
            assert(b == 4);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let (x, y) = (&mut a, &mut b);
            *x = 3;
            *y = 4;

            assert(a == 3);
            assert(b == 4);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = (&mut a, &mut b).0;
            *x = 3;

            assert(a == 3);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = (&mut a, &mut b).0;
            *x = 3;

            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let x = ({ y = y + 1; (&mut a, &mut b) }).0;
            *x = 3;

            assert(y == 1);
            assert(a == 3);
            assert(b == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let x = ({ y = y + 1; (&mut a, &mut b) }).0;
            *x = 3;

            assert(y == 1);
            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = ({ a = a + 1; (&mut a, &mut b) }).0;
            assert(*x == 1);
            *x = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = ({ a = a + 1; (&mut a, &mut b) }).0;
            assert(*x == 1);
            *x = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let x = ({ y = y + 1; &mut a });
            assert(*x == 0);
            *x = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let x = ({ y = y + 1; &mut a });
            assert(*x == 0);
            *x = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = ({ a = a + 1; &mut a });
            assert(*x == 1);
            *x = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test8_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let x = ({ a = a + 1; &mut a });
            assert(*x == 1);
            *x = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test9() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                let TGPair { g, t: _ } = (TGPair { g: a_ref, t: b_ref });
                assert(*g == 0);
            }

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(b == 0);
        }

        fn test9_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                let TGPair { g, t: _ } = (TGPair { g: a_ref, t: b_ref });
                assert(*g == 0);
            }

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test10() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                let TGPair { g: _, t } = (TGPair { g: id(a_ref), t: b_ref });
            }

            broadcast use stronger_resolver_axiom;

            assert(has_resolved(a_ref)); // FAILS

            *a_ref = 20;
        }
    } => Err(e) => assert_fails(e, 9)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_let_stmt_with_mut_pat ["new-mut-ref"] => verus_code! {
        fn mut_ref_pairs<'a, 'b, A, B>(a: &'a mut A, b: &'b mut B) -> (ret: (&'a mut A, &'b mut B))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (x, y) = mut_ref_pairs(&mut a, &mut b).0;
            assert(*x == 0);
            assert(*y == 1);
            *x = 10;
            *y = 12;

            assert(a === (10, 12));
            assert(b === (2, 3));
        }

        fn test1_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (x, y) = mut_ref_pairs(&mut a, &mut b).0;
            assert(*x == 0);
            assert(*y == 1);
            *x = 10;
            *y = 12;

            assert(a === (10, 12));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: (u64, u64) = (0, 1);

            let (x, y) = &mut a;
            assert(*x == 0 && *y == 1);
            *x = 3;
            *y = 4;

            assert(a === (3, 4));
        }

        fn test2_fails() {
            let mut a: (u64, u64) = (0, 1);

            let (x, y) = &mut a;
            assert(*x == 0 && *y == 1);
            *x = 3;
            *y = 4;

            assert(a === (3, 4));
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            let ((x, y), _) = (&mut a, &mut b);
            assert(*x == 0 && *y == 1);
            *x = 10;
            *y = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test3_fails() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            let ((x, y), _) = (&mut a, &mut b);
            assert(*x == 0 && *y == 1);
            *x = 10;
            *y = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test4() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (x, y) = (&mut a, &mut b).0;
            assert(*x == 0 && *y == 1);
            *x = 10;
            *y = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test4_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (x, y) = (&mut a, &mut b).0;
            assert(*x == 0 && *y == 1);
            *x = 10;
            *y = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test5() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            let (i, j) = ({ y = y + 1; (&mut a, &mut b) }).0;
            assert(y == 1);
            assert(*i == 0 && *j == 1);
            *i = 10;
            *j = 11;

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test5_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            let (i, j) = ({ y = y + 1; (&mut a, &mut b) }).0;
            assert(y == 1);
            assert(*i == 0 && *j == 1);
            *i = 10;
            *j = 11;

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test6() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (i, j) = ({ a.0 = a.0 + 20; (&mut a, &mut b) }).0;
            assert(*i == 20 && *j == 1);
            *i = 10;
            *j = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test6_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (i, j) = ({ a.0 = a.0 + 20; (&mut a, &mut b) }).0;
            assert(*i == 20 && *j == 1);
            *i = 10;
            *j = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test7() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            let (i, j) = ({ y = y + 1; &mut a });
            assert(y == 1);
            assert(*i == 0 && *j == 1);
            *i = 10;
            *j = 11;

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test7_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            let (i, j) = ({ y = y + 1; &mut a });
            assert(y == 1);
            assert(*i == 0 && *j == 1);
            *i = 10;
            *j = 11;

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test8() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (i, j) = ({ a.0 = a.0 + 40; &mut a });
            assert(*i == 40 && *j == 1);
            *i = 10;
            *j = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test8_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let (i, j) = ({ a.0 = a.0 + 40; &mut a });
            assert(*i == 40 && *j == 1);
            *i = 10;
            *j = 11;

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 8)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_match ["new-mut-ref"] => verus_code! {
        broadcast proof fn stronger_resolver_axiom<A, B>(pair: TGPair<A, B>) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.t)
        {
        }

        tracked struct TGPair<A, B> {
            tracked t: A,
            ghost g: B,
        }

        spec fn id<A>(a: A) -> A { a }

        fn mut_ref_pairs2<'a, 'b, 'c, 'd>(a: &'a mut u64, b: &'b mut u64, c: &'c mut u64, d: &'d mut u64) -> (ret: ((&'a mut u64, &'b mut u64), (&'c mut u64, &'d mut u64)))
            ensures
                mut_ref_current(ret.0.0) == mut_ref_current(a),
                mut_ref_future(ret.0.0) == mut_ref_future(a),
                mut_ref_current(ret.0.1) == mut_ref_current(b),
                mut_ref_future(ret.0.1) == mut_ref_future(b),
                mut_ref_current(ret.1.0) == mut_ref_current(c),
                mut_ref_future(ret.1.0) == mut_ref_future(c),
                mut_ref_current(ret.1.1) == mut_ref_current(d),
                mut_ref_future(ret.1.1) == mut_ref_future(d),
        {
            ((a, b), (c, d))
        }

        fn test1() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            match mut_ref_pairs2(&mut a, &mut b, &mut c, &mut d).0 {
                (x, y) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
            }

            assert(a == 10);
            assert(b == 12);
            assert(c == 2);
            assert(d == 3);
        }

        fn test1_fails() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            match mut_ref_pairs2(&mut a, &mut b, &mut c, &mut d).0 {
                (x, y) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
            }

            assert(a == 10);
            assert(b == 12);
            assert(c == 2);
            assert(d == 3);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match &mut a {
                x => {
                    *x = 3;
                }
            }

            assert(a == 3);
            assert(b == 0);
        }

        fn test2_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match &mut a {
                x => {
                    *x = 3;
                }
            }

            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match (&mut a, &mut b) {
                (x, y) => {
                    *x = 3;
                    *y = 4;
                }
            }

            assert(a == 3);
            assert(b == 4);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match (&mut a, &mut b) {
                (x, y) => {
                    *x = 3;
                    *y = 4;
                }
            }

            assert(a == 3);
            assert(b == 4);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match (&mut a, &mut b).0 {
                x => {
                    *x = 3;
                }
            }

            assert(a == 3);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match (&mut a, &mut b).0 {
                x => {
                    *x = 3;
                }
            }

            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; (&mut a, &mut b) }).0 {
                x => {
                    *x = 3;
                }
            }

            assert(y == 1);
            assert(a == 3);
            assert(b == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; (&mut a, &mut b) }).0 {
                x => {
                    *x = 3;
                }
            }

            assert(y == 1);
            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; (&mut a, &mut b) }).0 {
                x => {
                    assert(*x == 1);
                    *x = 5;
                }
            }

            assert(a == 5);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; (&mut a, &mut b) }).0 {
                x => {
                    assert(*x == 1);
                    *x = 5;
                }
            }

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; &mut a }) {
                x => {
                    assert(*x == 0);
                    *x = 5;
                }
            }

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; &mut a }) {
                x => {
                    assert(*x == 0);
                    *x = 5;
                }
            }

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; &mut a }) {
                x => {
                    assert(*x == 1);
                    *x = 5;
                }
            }

            assert(a == 5);
            assert(b == 0);
        }

        fn test8_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; &mut a }) {
                x => {
                    assert(*x == 1);
                    *x = 5;
                }
            }

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test9() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                match (TGPair { g: a_ref, t: b_ref }) {
                    TGPair { g, t: _ } => {
                        assert(*g == 0);
                    }
                }
            }

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(b == 0);
        }

        fn test9_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                match (TGPair { g: a_ref, t: b_ref }) {
                    TGPair { g, t: _ } => {
                        assert(*g == 0);
                    }
                }
            }

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test10() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            // We have to be careful here that resolving tmp.t
            // does not also resolve tmp.g (which is a ghost place)

            proof {
                match (TGPair { g: id(a_ref), t: b_ref }) {
                    TGPair { g: _, t } => {
                    }
                }
            }

            broadcast use stronger_resolver_axiom;

            assert(has_resolved(a_ref)); // FAILS

            *a_ref = 20;
        }
    } => Err(e) => assert_fails(e, 10)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_match_with_mut ["new-mut-ref"] => verus_code! {
        fn mut_ref_pairs<'a, 'b, A, B>(a: &'a mut A, b: &'b mut B) -> (ret: (&'a mut A, &'b mut B))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match mut_ref_pairs(&mut a, &mut b).0 {
                (x, y) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
            }

            assert(a === (10, 12));
            assert(b === (2, 3));
        }

        fn test1_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match mut_ref_pairs(&mut a, &mut b).0 {
                (x, y) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
            }

            assert(a === (10, 12));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: (u64, u64) = (0, 1);

            match &mut a {
                (x, y) => {
                    assert(*x == 0 && *y == 1);
                    *x = 3;
                    *y = 4;
                }
            }

            assert(a === (3, 4));
        }

        fn test2_fails() {
            let mut a: (u64, u64) = (0, 1);

            match &mut a {
                (x, y) => {
                    assert(*x == 0 && *y == 1);
                    *x = 3;
                    *y = 4;
                }
            }

            assert(a === (3, 4));
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            match (&mut a, &mut b) {
                ((x, y), _) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test3_fails() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            match (&mut a, &mut b) {
                ((x, y), _) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test4() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match (&mut a, &mut b).0 {
                (x, y) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test4_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match (&mut a, &mut b).0 {
                (x, y) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test5() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            match ({ y = y + 1; (&mut a, &mut b) }).0 {
                (i, j) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test5_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            match ({ y = y + 1; (&mut a, &mut b) }).0 {
                (i, j) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }


        fn test6() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match ({ a.0 = a.0 + 20; (&mut a, &mut b) }).0 {
                (i, j) => {
                    assert(*i == 20 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test6_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match ({ a.0 = a.0 + 20; (&mut a, &mut b) }).0 {
                (i, j) => {
                    assert(*i == 20 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test7() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            match ({ y = y + 1; &mut a }) {
                (i, j) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test7_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            let mut y = 0;

            match ({ y = y + 1; &mut a }) {
                (i, j) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(y == 1);
            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test8() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match ({ a.0 = a.0 + 40; &mut a }) {
                (i, j) => {
                    assert(*i == 40 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
        }

        fn test8_fails() {
            let mut a = (0, 1);
            let mut b = (2, 3);

            match ({ a.0 = a.0 + 40; &mut a }) {
                (i, j) => {
                    assert(*i == 40 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
            }

            assert(a === (10, 11));
            assert(b === (2, 3));
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 8)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_match_with_mut_and_option ["new-mut-ref"] => verus_code! {
        enum Option<V> {
            Some(V), None
        }
        use crate::Option::Some;
        use crate::Option::None;

        fn mut_ref_pairs<'a, 'b, A, B>(a: &'a mut A, b: &'b mut B) -> (ret: (&'a mut A, &'b mut B))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match mut_ref_pairs(&mut a, &mut b).0 {
                Some((x, y)) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 12)));
            assert(b === Some((2, 3)));
        }

        fn test1_fails() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match mut_ref_pairs(&mut a, &mut b).0 {
                Some((x, y)) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 12)));
            assert(b === Some((2, 3)));
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: Option<(u64, u64)> = Some((0, 1));

            match &mut a {
                Some((x, y)) => {
                    assert(*x == 0 && *y == 1);
                    *x = 3;
                    *y = 4;
                }
                _ => { assert(false); }
            }

            assert(a === Some((3, 4)));
        }

        fn test2_fails() {
            let mut a: Option<(u64, u64)> = Some((0, 1));

            match &mut a {
                Some((x, y)) => {
                    assert(*x == 0 && *y == 1);
                    *x = 3;
                    *y = 4;
                }
                _ => { assert(false); }
            }

            assert(a === Some((3, 4)));
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: Option<(u64, u64)> = Some((0, 1));
            let mut b: Option<(u64, u64)> = Some((2, 3));

            match (&mut a, &mut b) {
                (Some((x, y)), _) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
        }

        fn test3_fails() {
            let mut a: Option<(u64, u64)> = Some((0, 1));
            let mut b: Option<(u64, u64)> = Some((2, 3));

            match (&mut a, &mut b) {
                (Some((x, y)), _) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
            assert(false); // FAILS
        }

        fn test4() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match (&mut a, &mut b).0 {
                Some((x, y)) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
        }

        fn test4_fails() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match (&mut a, &mut b).0 {
                Some((x, y)) => {
                    assert(*x == 0 && *y == 1);
                    *x = 10;
                    *y = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
            assert(false); // FAILS
        }

        fn test5() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            let mut y = 0;

            match ({ y = y + 1; (&mut a, &mut b) }).0 {
                Some((i, j)) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(y == 1);
            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
        }

        fn test5_fails() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            let mut y = 0;

            match ({ y = y + 1; (&mut a, &mut b) }).0 {
                Some((i, j)) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(y == 1);
            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
            assert(false); // FAILS
        }

        fn test6() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match ({ a = Some((20, 21)); (&mut a, &mut b) }).0 {
                Some((i, j)) => {
                    assert(*i == 20 && *j == 21);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
        }

        fn test6_fails() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match ({ a = Some((20, 21)); (&mut a, &mut b) }).0 {
                Some((i, j)) => {
                    assert(*i == 20 && *j == 21);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
            assert(false); // FAILS
        }

        fn test7() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            let mut y = 0;

            match ({ y = y + 1; &mut a }) {
                Some((i, j)) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(y == 1);
            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
        }

        fn test7_fails() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            let mut y = 0;

            match ({ y = y + 1; &mut a }) {
                Some((i, j)) => {
                    assert(y == 1);
                    assert(*i == 0 && *j == 1);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(y == 1);
            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
            assert(false); // FAILS
        }

        fn test8() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match ({ a = Some((40, 41)); &mut a }) {
                Some((i, j)) => {
                    assert(*i == 40 && *j == 41);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
        }

        fn test8_fails() {
            let mut a = Some((0, 1));
            let mut b = Some((2, 3));

            match ({ a = Some((40, 41)); &mut a }) {
                Some((i, j)) => {
                    assert(*i == 40 && *j == 41);
                    *i = 10;
                    *j = 11;
                }
                _ => { assert(false); }
            }

            assert(a === Some((10, 11)));
            assert(b === Some((2, 3)));
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 8)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_match_with_option ["new-mut-ref"] => verus_code! {
        enum Option<V> {
            Some(V), None
        }
        use crate::Option::Some;
        use crate::Option::None;

        broadcast proof fn stronger_resolve_axiom_opt<A>(opt: Option<A>) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(opt) ==> opt is Some ==> has_resolved(opt->Some_0)
        {
        }

        broadcast proof fn stronger_resolver_axiom<A, B>(pair: TGPair<A, B>) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.t)
        {
        }

        tracked struct TGPair<A, B> {
            tracked t: A,
            ghost g: B,
        }

        spec fn id<A>(a: A) -> A { a }

        fn mut_ref_pairs2<'a, 'b, 'c, 'd>(a: &'a mut u64, b: &'b mut u64, c: &'c mut u64, d: &'d mut u64) -> (ret: (Option<(&'a mut u64, &'b mut u64)>, Option<(&'c mut u64, &'d mut u64)>))
            ensures
                ret.0 is Some,
                ret.1 is Some,
                mut_ref_current(ret.0->Some_0.0) == mut_ref_current(a),
                mut_ref_future(ret.0->Some_0.0) == mut_ref_future(a),
                mut_ref_current(ret.0->Some_0.1) == mut_ref_current(b),
                mut_ref_future(ret.0->Some_0.1) == mut_ref_future(b),
                mut_ref_current(ret.1->Some_0.0) == mut_ref_current(c),
                mut_ref_future(ret.1->Some_0.0) == mut_ref_future(c),
                mut_ref_current(ret.1->Some_0.1) == mut_ref_current(d),
                mut_ref_future(ret.1->Some_0.1) == mut_ref_future(d),
        {
            (Some((a, b)), Some((c, d)))
        }

        fn test1() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            match mut_ref_pairs2(&mut a, &mut b, &mut c, &mut d).0 {
                Some((x, y)) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
                _ => { assert(false); }
            }

            assert(a == 10);
            assert(b == 12);
            assert(c == 2);
            assert(d == 3);
        }

        fn test1_fails() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            match mut_ref_pairs2(&mut a, &mut b, &mut c, &mut d).0 {
                Some((x, y)) => {
                    assert(*x == 0);
                    assert(*y == 1);
                    *x = 10;
                    *y = 12;
                }
                _ => { assert(false); }
            }

            assert(a == 10);
            assert(b == 12);
            assert(c == 2);
            assert(d == 3);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match Some(&mut a) {
                Some(x) => {
                    *x = 3;
                }
                _ => { assert(false); }
            }

            assert(a == 3);
            assert(b == 0);
        }

        fn test2_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match Some(&mut a) {
                Some(x) => {
                    *x = 3;
                }
                _ => { assert(false); }
            }

            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match Some((&mut a, &mut b)) {
                Some((x, y)) => {
                    *x = 3;
                    *y = 4;
                }
                _ => { assert(false); }
            }

            assert(a == 3);
            assert(b == 4);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match Some((&mut a, &mut b)) {
                Some((x, y)) => {
                    *x = 3;
                    *y = 4;
                }
                _ => { assert(false); }
            }

            assert(a == 3);
            assert(b == 4);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match (Some(&mut a), Some(&mut b)).0 {
                Some(x) => {
                    *x = 3;
                }
                _ => { assert(false); }
            }

            broadcast use stronger_resolve_axiom_opt;

            assert(a == 3);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match (Some(&mut a), Some(&mut b)).0 {
                Some(x) => {
                    *x = 3;
                }
                _ => { assert(false); }
            }

            broadcast use stronger_resolve_axiom_opt;

            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; (Some(&mut a), Some(&mut b)) }).0 {
                Some(x) => {
                    *x = 3;
                }
                _ => { assert(false); }
            }

            broadcast use stronger_resolve_axiom_opt;

            assert(y == 1);
            assert(a == 3);
            assert(b == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; (Some(&mut a), Some(&mut b)) }).0 {
                Some(x) => {
                    *x = 3;
                }
                _ => { assert(false); }
            }

            broadcast use stronger_resolve_axiom_opt;

            assert(y == 1);
            assert(a == 3);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; (Some(&mut a), Some(&mut b)) }).0 {
                Some(x) => {
                    assert(*x == 1);
                    *x = 5;
                }
                _ => { assert(false); }
            }

            broadcast use stronger_resolve_axiom_opt;

            assert(a == 5);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; (Some(&mut a), Some(&mut b)) }).0 {
                Some(x) => {
                    assert(*x == 1);
                    *x = 5;
                }
                _ => { assert(false); }
            }

            broadcast use stronger_resolve_axiom_opt;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; Some(&mut a) }) {
                Some(x) => {
                    assert(*x == 0);
                    *x = 5;
                }
                _ => { assert(false); }
            }

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            match ({ y = y + 1; Some(&mut a) }) {
                Some(x) => {
                    assert(*x == 0);
                    *x = 5;
                }
                _ => { assert(false); }
            }

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; Some(&mut a) }) {
                Some(x) => {
                    assert(*x == 1);
                    *x = 5;
                }
                _ => { assert(false); }
            }

            assert(a == 5);
            assert(b == 0);
        }

        fn test8_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            match ({ a = a + 1; Some(&mut a) }) {
                Some(x) => {
                    assert(*x == 1);
                    *x = 5;
                }
                _ => { assert(false); }
            }

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test9() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                match Some(TGPair { g: a_ref, t: b_ref }) {
                    Some(TGPair { g, t: _ }) => {
                        assert(*g == 0);
                    }
                    _ => { assert(false); }
                }
            }

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(b == 0);
        }

        fn test9_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                match Some(TGPair { g: a_ref, t: b_ref }) {
                    Some(TGPair { g, t: _ }) => {
                        assert(*g == 0);
                    }
                    _ => { assert(false); }
                }
            }

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test10() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            proof {
                match Some((TGPair { g: id(a_ref), t: b_ref })) {
                    Some(TGPair { g: _, t }) => {
                    }
                    _ => { assert(false); }
                }
            }

            broadcast use stronger_resolve_axiom_opt;
            broadcast use stronger_resolver_axiom;

            assert(has_resolved(a_ref)); // FAILS

            *a_ref = 20;
        }
    } => Err(e) => assert_fails(e, 10)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_mut_borrow ["new-mut-ref"] => verus_code! {
        fn mut_ref_pairs<'a, 'b>(a: &'a mut (u64, u64), b: &'b mut (u64, u64)) -> (ret: (&'a mut (u64, u64), &'b mut (u64, u64)))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test0() {
            let mut a = 0;

            // This does not modify a
            *(&mut ({ a })) = 5;

            assert(a == 0);
        }

        fn test0_fails() {
            let mut a = 0;

            // This does not modify a
            *(&mut ({ a })) = 5;

            assert(a == 0);
            assert(false); // FAILS
        }

        fn test00() {
            let mut a = 0;

            // This does not modify a
            *({ (&mut ({ a })) }) = 5;

            assert(a == 0);
        }

        fn test00_fails() {
            let mut a = 0;

            // This does not modify a
            *({ (&mut ({ a })) }) = 5;

            assert(a == 0);
            assert(false); // FAILS
        }

        fn test1() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            *(&mut mut_ref_pairs(&mut a, &mut b).0.0) = 5;

            assert(a === (5, 1));
            assert(b === (2, 3));
        }

        fn test1_fails() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            *(&mut mut_ref_pairs(&mut a, &mut b).0.0) = 5;

            assert(a === (5, 1));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test1b() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            *({ (&mut mut_ref_pairs(&mut a, &mut b).0.0) }) = 5;

            assert(a === (5, 1));
            assert(b === (2, 3));
        }

        fn test1b_fails() {
            let mut a: (u64, u64) = (0, 1);
            let mut b: (u64, u64) = (2, 3);

            *({ (&mut mut_ref_pairs(&mut a, &mut b).0.0) }) = 5;

            assert(a === (5, 1));
            assert(b === (2, 3));
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            // this does nothing; `(a, b)` creates a temporary, so this only assigns to the temporary
            let mr = (&mut (a, b).0);
            *mr = 5;

            assert(a == 0);
            assert(b == 0);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            // this does nothing; `(a, b)` creates a temporary, so this only assigns to the temporary
            let mr = (&mut (a, b).0);
            *mr = 5;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mr = &mut *(&mut a, &mut b).0;
            *mr = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mr = &mut *(&mut a, &mut b).0;
            *mr = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let mr = &mut *({ y = y + 1; (&mut a, &mut b) }).0;
            *mr = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let mr = &mut *({ y = y + 1; (&mut a, &mut b) }).0;
            *mr = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mr = &mut *({ a = a + 1; (&mut a, &mut b) }).0;
            *mr = 5;

            assert(a == 5);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mr = &mut *({ a = a + 1; (&mut a, &mut b) }).0;
            *mr = 5;

            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let mr = &mut *({ y = y + 1; &mut a });
            *mr = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let mr = &mut *({ y = y + 1; &mut a });
            *mr = 5;

            assert(y == 1);
            assert(a == 5);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mr = &mut *({ a = a + 1; &mut a });
            *mr = *mr + 5;

            assert(a == 6);
            assert(b == 0);
        }

        fn test8_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mr = &mut *({ a = a + 1; &mut a });
            *mr = *mr + 5;

            assert(a == 6);
            assert(b == 0);
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 10)
}

test_verify_one_file_with_options! {
    #[test] mut_refs_of_mut_refs ["new-mut-ref"] => verus_code! {
        fn test1() {
            let mut a = 0;
            let x = &mut &mut a;
            **x = 5;
            assert(a == 5);
        }

        fn test1_fails() {
            let mut a = 0;
            let x = &mut &mut a;
            **x = 5;
            assert(a == 5);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a = 0;
            let x = { &mut &mut a };
            **x = 5;
            assert(a == 5);
        }

        fn test2_fails() {
            let mut a = 0;
            let x = { &mut &mut a };
            **x = 5;
            assert(a == 5);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a = 0;
            let x = &mut { &mut a };
            **x = 5;
            assert(a == 5);
        }

        fn test3_fails() {
            let mut a = 0;
            let x = &mut { &mut a };
            **x = 5;
            assert(a == 5);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a = 0;
            let x = &mut &mut &mut &mut a;
            ****x = 5;
            assert(a == 5);
        }

        fn test4_fails() {
            let mut a = 0;
            let x = &mut &mut &mut &mut a;
            ****x = 5;
            assert(a == 5);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a = 0;
            let x = &mut &mut &mut &mut a;
            assert(a == 0);
        }

        fn test5_fails() {
            let mut a = 0;
            let x = &mut &mut &mut &mut a;
            assert(a == 0);
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 5)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_in_shared_borrow ["new-mut-ref"] => verus_code! {
        broadcast axiom fn stronger_resolver_axiom<A, B>(pair: (A, B)) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.0) && has_resolved(pair.1);


        fn mut_ref_pairs<'a, 'b>(a: &'a mut u64, b: &'b mut u64) -> (ret: (&'a mut u64, &'b mut u64))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &mut_ref_pairs(&mut a, &mut b).0;

            assert(a == 0);
            assert(b == 0);
        }

        fn test1_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &mut_ref_pairs(&mut a, &mut b).0;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &(&mut a);

            assert(a == 0);
            assert(b == 0);
        }

        fn test2_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &(&mut a);

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &(a, b).0;

            assert(a == 0);
            assert(b == 0);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &(a, b).0;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test4() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            broadcast use stronger_resolver_axiom;

            let shr = &(&mut a, &mut b).0;

            assert(a == 0);
            assert(b == 0);
        }

        fn test4_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            broadcast use stronger_resolver_axiom;

            let shr = &(&mut a, &mut b).0;

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let shr = &({ y = y + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(y == 1);
            assert(a == 0);
            assert(b == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let shr = &({ y = y + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(y == 1);
            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &({ a = a + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(a == 1);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &({ a = a + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(a == 1);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let shr = &({ y = y + 1; &mut a });

            assert(y == 1);
            assert(a == 0);
            assert(b == 0);
        }

        fn test7_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            let shr = &({ y = y + 1; &mut a });

            assert(y == 1);
            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test8() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &({ a = a + 1; &mut a });

            assert(a == 1);
            assert(b == 0);
        }

        fn test8_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let shr = &({ a = a + 1; &mut a });

            assert(a == 1);
            assert(b == 0);
            assert(false); // FAILS
        }

        spec fn arbitrary_pair() -> (u64, u64) { (10u64, 12u64) }

        fn test9() {
            proof { let shr = &arbitrary_pair().0; }
            broadcast use stronger_resolver_axiom;
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 9)
}

test_verify_one_file_with_options! {
    #[test] temporary_place_unused ["new-mut-ref"] => verus_code! {
        broadcast axiom fn stronger_resolver_axiom<A, B>(pair: (A, B)) // TODO(new_mut_ref)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.0) && has_resolved(pair.1);

        uninterp spec fn arbitrary<A>() -> A;

        fn mut_ref_pairs<'a, 'b>(a: &'a mut u64, b: &'b mut u64) -> (ret: (&'a mut u64, &'b mut u64))
            ensures
                mut_ref_current(ret.0) == mut_ref_current(a),
                mut_ref_future(ret.0) == mut_ref_future(a),
                mut_ref_current(ret.1) == mut_ref_current(b),
                mut_ref_future(ret.1) == mut_ref_future(b),
        {
            (a, b)
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            mut_ref_pairs(&mut a, &mut b);

            assert(a == 0);
            assert(b == 0);
        }

        fn test1_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            mut_ref_pairs(&mut a, &mut b);

            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 0;
            &mut a;
            assert(a == 0);
        }

        fn test2_fails() {
            let mut a: u64 = 0;
            &mut a;
            assert(a == 0);
            assert(false); // FAILS
        }

        fn test3() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            (&mut a, &mut b);

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(a == 0);
        }

        fn test3_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            (&mut a, &mut b);

            broadcast use stronger_resolver_axiom;

            assert(a == 0);
            assert(a == 0);
            assert(false); // FAILS
        }

        fn test5() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            ({ y = y + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(y == 1);
            assert(a == 0);
            assert(b == 0);
        }

        fn test5_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let mut y = 0;

            ({ y = y + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(y == 1);
            assert(a == 0);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test6() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            ({ a = a + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(a == 1);
            assert(b == 0);
        }

        fn test6_fails() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            ({ a = a + 1; (&mut a, &mut b) }).0;

            broadcast use stronger_resolver_axiom;

            assert(a == 1);
            assert(b == 0);
            assert(false); // FAILS
        }

        fn test7() {
            proof { arbitrary::<(&mut u64, &mut u64)>().0; }
            assert(has_resolved(arbitrary::<(&mut u64, &mut u64)>().0)); // FAILS
        }

        fn test8() {
            proof { arbitrary::<(&mut u64, &mut u64)>().0; }
            assert(has_resolved(arbitrary::<(&mut u64, &mut u64)>().1)); // FAILS
        }
    } => Err(e) => assert_fails(e, 7)
}

test_verify_one_file_with_options! {
    #[test] resolving_and_side_effects_in_ghost_temporary ["new-mut-ref"] => verus_code! {
        spec fn some_int() -> int { 0 }

        fn test() {
            let mut a: Ghost<int> = Ghost(0);
            let a_ref = &mut a;

            proof {
                let ghost x = ({
                    *a_ref.borrow_mut() = 20;
                    some_int()
                });
            }

            assert(a == 20);
        }

        fn fails() {
            let mut a: Ghost<int> = Ghost(0);
            let a_ref = &mut a;

            proof {
                let ghost x = ({
                    *a_ref.borrow_mut() = 20;
                    some_int()
                });
            }

            assert(a == 20);
            assert(false); // FAILS
        }

        proof fn consume<T>(tracked t: T) -> T {
            t
        }

        proof fn test_consume<T>(tracked t: T) {
            let x = consume(t);
            assert(has_resolved(t)); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] assign_eval_ordering_with_temporary ["new-mut-ref"] => verus_code! {
        fn mut_ref_id(a: &mut u64) -> (ret: &mut u64)
            ensures
                mut_ref_current(ret) == 30,
                mut_ref_future(a) == mut_ref_future(ret),
        {
            *a = 30;
            a
        }

        fn test1() {
            let mut a: u64 = 20;
            *mut_ref_id(&mut a) = a;
            assert(a == 20);
        }

        fn fails1() {
            let mut a: u64 = 20;
            *mut_ref_id(&mut a) = a;
            assert(a == 20);
            assert(false); // FAILS
        }

        fn test2() {
            let mut a: u64 = 20;
            *mut_ref_id(&mut a) += a;
            assert(a == 50);
        }

        fn fails2() {
            let mut a: u64 = 20;
            *mut_ref_id(&mut a) += a;
            assert(a == 50);
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}
