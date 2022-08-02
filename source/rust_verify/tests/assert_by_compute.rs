#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] bit_vectors code! {

        #[spec]
        fn shifter(x: u64, amt: usize) -> u64 {
            decreases(amt);
            if amt == 0 { x } else { shifter(x << 1, amt - 1) }
        }

        const one32: u32 = 1;
        const two32: u32 = 2;
        const two_to_31: u32 = 0x8000_0000;
        const one64: u64 = 1;
        const two64: u64 = 2;
        fn test(x: u64) {
            assert_by_compute_only(!(-1) == 0);
            assert_by_compute_only(!(-2) == 1);
            assert_by_compute_only(!one32 == 0xFFFF_FFFE);
            assert_by_compute_only(!two32 == 0xFFFF_FFFD);
            assert_by_compute_only(!one64 == 0xFFFF_FFFF_FFFF_FFFE);
            assert_by_compute_only(!two64 == 0xFFFF_FFFF_FFFF_FFFD);
            assert_by_compute_only(one32 ^ two32 == 3);
            assert_by_compute_only(two32 ^ one32 == 3);
            assert_by_compute_only(one32 & two32 == 0);
            assert_by_compute_only(one32 | two32 == 3);
            assert_by_compute_only(one32 << 3 == 8);
            assert_by_compute_only(two32 << 3 == 16);
            assert_by_compute_only(one32 >> 1 == 0);
            assert_by_compute_only(two32 >> 1 == 1);
            assert_by_compute_only(two32 >> 2 == 0);
            assert_by_compute_only(two_to_31 >> 1 == 0x4000_0000);
            assert_by_compute_only(two_to_31 << 1 == 0);
            assert_by_compute_only(-1 << 3 == -8);
            assert_by_compute_only(x ^ x == 0);
            assert_by_compute_only(x & x == x);
            assert_by_compute_only(0 & x == 0);
            assert_by_compute_only(x & 0 == 0);
            assert_by_compute_only(0 | x == x);
            assert_by_compute_only(x | 0 == x);
            assert_by_compute_only(x | x == x);
            assert_by_compute_only(shifter(1, 10) == 1024);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] arith code! {
        fn test(x: u64) {
            assert_by_compute_only((7 + 7 * 2 > 20) && (22 - 5 <= 10 * 10));
            // TODO: The examples below that don't use the "_only" version
            // result in something like: uClip(64, x) == x,
            // due to the same issue mentioned in if_then_else below
            assert_by_compute(x + 0 == x);
            assert_by_compute(0 + x == x);
            assert_by_compute(x - 0 == x);
            assert_by_compute(x * 1 == x);
            assert_by_compute(1 * x == x);
            assert_by_compute_only(x * 0 == 0);
            assert_by_compute_only(0 * x == 0);
            assert_by_compute_only(x - x == 0);
            assert_by_compute(x / 1 == x);
            assert_by_compute_only(x % 1 == 0);

            // Make sure we've implemented Euclidean div and mod
            assert_by_compute_only(( 8 as int) / ( 3 as int) == 2);
            assert_by_compute_only(( 8 as int) / (-3 as int) == -2);
            assert_by_compute_only((-8 as int) / ( 3 as int) == -3);
            assert_by_compute_only((-8 as int) / (-3 as int) == 3);

            assert_by_compute_only(( 1 as int) / ( 2 as int) == 0);
            assert_by_compute_only(( 1 as int) / (-2 as int) == 0);
            assert_by_compute_only((-1 as int) / ( 2 as int) == -1);
            assert_by_compute_only((-1 as int) / (-2 as int) == 1);

            assert_by_compute_only(( 8 as int) % ( 3 as int) == 2);
            assert_by_compute_only(( 8 as int) % (-3 as int) == 2);
            assert_by_compute_only((-8 as int) % ( 3 as int) == 1);
            assert_by_compute_only((-8 as int) % (-3 as int) == 1);

            assert_by_compute_only(( 1 as int) % ( 2 as int) == 1);
            assert_by_compute_only(( 1 as int) % (-2 as int) == 1);
            assert_by_compute_only((-1 as int) % ( 2 as int) == 1);
            assert_by_compute_only((-1 as int) % (-2 as int) == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] if_then_else code! {

        fn test(x: u64) {
            assert_by_compute_only(9 == if 7 > 3 { 9 } else { 5 });
            assert_by_compute_only(if true { true } else { false });
            assert_by_compute_only(if !true { false } else { true });
            assert_by_compute_only(if !!true { true } else { false });
            // TODO: The example below fails the expr_to_pure_exp check,
            // due to the overflow checks that are inserted.
            // They are inserted because the mode checker treats constants as Exec,
            // which leads to the arith being marked as Exec, and the mode checker
            // confirms that an Exec expression can be passed as a Spec arg,
            // but it doesn't "upgrade" the expression to Spec.
            // This should be addressed when we move to the new syntax.
            //assert_by_compute_only(9 == if (7 + 7 * 2 > 20) { 7 + 2 } else { 22 - 5 + 10*10 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lets code! {

        fn test(x: u64) {
            assert_by_compute_only({
                #[spec]
                let x = true;
                x
            });

            assert_by_compute_only({
                #[spec]
                let x = 7;
                x > 4
            });

            assert_by_compute_only({
                #[spec]
                let x: u32 = 7;
                #[spec]
                let y = 14;
                x + y > 20
            });

            assert_by_compute_only({
                #[spec]
                let x: u32 = 7;
                #[spec]
                let y: u32 = x + 1;
                x + y == 15
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lets_bad code! {

        #[spec]
        fn f(n:nat) -> nat {
            n + 1
        }

        fn test() {
            assert_by_compute({
                #[spec]
                let x = 4;
                #[spec]
                let r1 = f(x);
                #[spec]
                let x = 5;
                #[spec]
                let r2 = f(x);
                r1 == r2
            });     // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] datatype code! {
        #[allow(unused_imports)]
        use pervasive::option::Option;

        fn test(x: u64) {
            assert_by_compute_only(match Option::Some(true) {
                Option::Some(b) => b,
                _ => 10 > 20,
            });

            assert_by_compute_only(match Option::Some(false) {
                Option::Some(b) => !b,
                _ => 10 > 20,
            });

            assert_by_compute_only(match Option::<bool>::None {
                Option::Some(_) => false,
                _ => 20 > 10,
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tuples code! {
        #[spec]
        fn mk_tuple() -> (u32, u32, u64, bool) {
            (42, 330, 0x1_0000_0000, false)
        }

        fn test() {
            assert_by_compute_only(mk_tuple().0 == 42);
            assert_by_compute_only(mk_tuple().1 == 330);
            assert_by_compute_only(mk_tuple().2 - 0xFFFF_FFFF == 1);
            assert_by_compute_only(!mk_tuple().3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] structs code! {
        struct Example {
            u1: u32,
            u2: u64,
            b: bool,
        }

        fn test(e: Example) {
            assert_by_compute_only(e.u1 == e.u1);
            assert_by_compute_only(e.u2 == e.u2);
            assert_by_compute_only(e.b == e.b);

            assert_by_compute_only({
                #[spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                e1.u1 > 5
            });
            assert_by_compute_only({
                #[spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                e1.u2 == 0x1_0000_0000
            });
            assert_by_compute_only({
                #[spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                !e1.b
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] closures code! {

        fn test(x: u64) {
            assert_by_compute_only((|x| x + 1)(5) == 6);
            let y = 5;
            // Reduces to clip(5 + y) == 10, since the let is outside the assert
            assert_by_compute((|x| x + y)(5) == 10);
            assert_by_compute_only({
                #[spec]
                let y = 10;
                (|x| x + y)(5) == 15
            });
            assert_by_compute_only((|x,y| x + y)(40, 2) == 42);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_calls_good code! {
        #[spec]
        fn f(x: int, y: int) -> bool { x == y }

        #[spec]
        fn g(x: int) -> bool { f(3, x) }

        #[spec]
        fn sum(x: nat) -> nat {
            decreases(x);
            if x == 0 { 0 } else { 1 + sum(x - 1) }
        }

        #[spec]
        #[verifier(external_body)]
        fn f_no_body(x: nat) -> nat {
            0
        }

        #[spec]
        #[verifier(external_body)]
        fn g_no_body(x: nat) -> nat {
            0
        }

        fn test() {
            assert_by_compute_only(sum(20) == 20);
            assert_by_compute_only(sum(10) == 10);
            assert_by_compute_only(sum(0) == 0);
            assert_by_compute_only({
                #[spec] let x = 22;
                #[spec] let z = g(x);
                !!!z    // Exercise an unusual recursive case inside the interpreter
            });
            assert_by_compute_only(f_no_body(5) == f_no_body(5));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_calls_bad1 code! {
        #[spec]
        #[verifier(external_body)]
        fn f_no_body(x: nat) -> nat {
            0
        }

        #[spec]
        #[verifier(external_body)]
        fn g_no_body(x: nat) -> nat {
            0
        }

        fn test() {
            assert_by_compute_only(f_no_body(5) != f_no_body(6)); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fn_calls_bad2 code! {
        #[spec]
        #[verifier(external_body)]
        fn f_no_body(x: nat) -> nat {
            0
        }

        #[spec]
        #[verifier(external_body)]
        fn g_no_body(x: nat) -> nat {
            0
        }

        fn test() {
            assert_by_compute_only(f_no_body(5) == g_no_body(5)); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fn_calls_bad3 code! {
        mod privacy_invasion {
            #[allow(unused_imports)]
            use builtin::assert_by_compute_only;

            mod mostly_private {
                #[spec] pub fn f() -> u32 { 1 }
            }

            fn test() {
                assert_by_compute_only(mostly_private::f() == 1); // FAILS
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] sequences code! {
        #[allow(unused_imports)]
        use crate::pervasive::seq::*;

        #[proof]
        fn test() {
            assert_by_compute_only(Seq::<u32>::empty().len() == 0);
            assert_by_compute_only(Seq::<u32>::empty().push(4).len() == 1);
            assert_by_compute_only(Seq::<u32>::empty().push(4).last() == 4);
            assert_by_compute_only(Seq::<u32>::empty().push(1).push(2).index(1) == 2);
            assert_by_compute_only(seq![1, 2, 3].len() == 3);
            assert_by_compute_only(seq![1, 2, 3].index(0) == 1);
            assert_by_compute_only(seq![1, 2, 3].index(1) == 2);
            assert_by_compute_only(seq![1, 2, 3].index(2) == 3);
            assert_by_compute_only(seq![1, 2, 3].last() == 3);
            assert_by_compute_only(seq![1, 2, 3].update(1, 5).index(0) == 1);
            assert_by_compute_only(seq![1, 2, 3].update(1, 5).index(1) == 5);
            assert_by_compute_only(seq![1, 2, 3].update(1, 5).index(2) == 3);
            assert_by_compute_only(seq![1, 2, 3].add(seq![4, 5]).len() == 5);
            assert_by_compute_only(seq![1, 2, 3].ext_equal(seq![1].add(seq![2, 3])));
            assert_by_compute_only(seq![1, 2].subrange(1, 2).ext_equal(seq![2]));
            assert_by_compute_only(seq![1, 2, 3, 4, 5].subrange(2, 4).ext_equal(seq![3, 4]));
            assert_by_compute_only(Seq::new(5, |x| x).index(3) == 3);
            assert_by_compute_only(Seq::new(5, |x| x + x).index(3) == 6);
            assert_by_compute_only(Seq::new(5, |x| x + x).last() == 8);
            assert_by_compute_only(Seq::new(5, |x| x + x).subrange(1,4).ext_equal(seq![2, 4, 6]));
        }

        #[spec]
        fn use_seq(s: &Seq<u32>) -> (u32, u32) {
            let s_new = s.update(1, 42);
            let s_add = s.push(13).add(seq![14, 15, 16]);
            (s_new.index(1), s_add.index(4))
        }

        fn test_seq_modification() {
            assert({
                #[spec]
                let v = seq![0, 1, 2];
                use_seq(&v).0 == 42 && use_seq(&v).1 == 14 && v.index(1) == 1
            });
        }
    } => Ok(())
}
