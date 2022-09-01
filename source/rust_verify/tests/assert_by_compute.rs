#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] bit_vectors verus_code! {

        spec fn shifter(x: u64, amt: usize) -> u64
            decreases amt
        {
            if amt == 0 { x } else { shifter(x << 1, (amt - 1) as usize) }
        }

        const one32: u32 = 1;
        const two32: u32 = 2;
        const two_to_31: u32 = 0x8000_0000;
        const one64: u64 = 1;
        const two64: u64 = 2;
        fn test(x: u64) {
            assert(!sub(0i32,1) == 0) by (compute);
            assert(!sub(0i32,2) == 1) by (compute_only);
            assert(!one32 == 0xFFFF_FFFE) by (compute_only);
            assert(!two32 == 0xFFFF_FFFD) by (compute_only);
            assert(!one64 == 0xFFFF_FFFF_FFFF_FFFE) by (compute_only);
            assert(!two64 == 0xFFFF_FFFF_FFFF_FFFD) by (compute_only);
            assert(one32 ^ two32 == 3) by (compute_only);
            assert(two32 ^ one32 == 3) by (compute_only);
            assert(one32 & two32 == 0) by (compute_only);
            assert(one32 | two32 == 3) by (compute_only);
            assert(one32 << 3 == 8) by (compute_only);
            assert(two32 << 3 == 16) by (compute_only);
            assert(one32 >> 1 == 0) by (compute_only);
            assert(two32 >> 1 == 1) by (compute_only);
            assert(two32 >> 2 == 0) by (compute_only);
            assert(two_to_31 >> 1 == 0x4000_0000) by (compute_only);
            assert(two_to_31 << 1 == 0) by (compute_only);
            assert(sub(0i32,1) << 3 == -8) by (compute_only);
            assert(x ^ x == 0) by (compute_only);
            assert(x & x == x) by (compute_only);
            assert(0 & x == 0) by (compute_only);
            assert(x & 0 == 0) by (compute_only);
            assert(0 | x == x) by (compute_only);
            assert(x | 0 == x) by (compute_only);
            assert(x | x == x) by (compute_only);
            assert(shifter(1, 10) == 1024) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] arith verus_code! {
        proof fn test(x: u64) {
            assert((7 + 7 * 2 > 20) && (22 - 5 <= 10 * 10)) by (compute_only);
            // TODO: The examples below that don't use the "_only" version
            // result in something like: uClip(64, x) == x,
            // due to the same issue mentioned in if_then_else below
            assert(x + 0 == x) by (compute);
            assert(0int + x == x) by (compute_only);
            assert(x - 0 == x) by (compute);
            assert(x * 1 == x) by (compute);
            assert(1 * x == x) by (compute);
            assert(x * 0 == 0) by (compute_only);
            assert(0 * x == 0) by (compute_only);
            assert(x - x == 0) by (compute_only);
            assert(x / 1 == x) by (compute);
            assert(x % 1 == 0) by (compute_only);

            // Make sure we've implemented Euclidean div and mod
            assert( 8int /  3 == 2) by (compute_only);
            assert( 8int / -3 == -2) by (compute_only);
            assert(-8int /  3 == -3) by (compute_only);
            assert(-8int / -3 == 3) by (compute_only);

            assert( 1int /  2 == 0) by (compute_only);
            assert( 1int / -2 == 0) by (compute_only);
            assert(-1int /  2 == -1) by (compute_only);
            assert(-1int / -2 == 1) by (compute_only);

            assert( 8int %  3 == 2) by (compute_only);
            assert( 8int % -3 == 2) by (compute_only);
            assert(-8int %  3 == 1) by (compute_only);
            assert(-8int % -3 == 1) by (compute_only);

            assert( 1int %  2 == 1) by (compute_only);
            assert( 1int % -2 == 1) by (compute_only);
            assert(-1int %  2 == 1) by (compute_only);
            assert(-1int % -2 == 1) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] if_then_else verus_code! {

        proof fn test(x: u64) {
            assert(9int == if 7 > 3 { 9int } else { 5 }) by (compute);
            assert(if true { true } else { false }) by (compute_only);
            assert(if !true { false } else { true }) by (compute_only);
            assert(if !!true { true } else { false }) by (compute_only);
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
    #[test] lets verus_code! {

        fn test(x: u64) {
            assert({
                let x = true;
                x
            }) by (compute_only);

            assert({
                let x:int = 7;
                x > 4
            }) by (compute_only);

            assert({
                let x:int = 7;
                let y:int = 14;
                x + y > 20
            }) by (compute_only);

            assert({
                let x:int = 7;
                let y:int = x + 1;
                x + y == 15
            }) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lets_bad verus_code! {

        spec fn f(n:nat) -> nat {
            n + 1
        }

        fn test() {
            assert({
                let x = 4;
                let r1 = f(x);
                let x = 5;
                let r2 = f(x);
                r1 == r2
            }) by (compute_only);     // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] datatype verus_code! {
        #[allow(unused_imports)]
        use pervasive::option::Option;

        fn test(x: u64) {
            assert(match Option::Some(true) {
                Option::Some(b) => b,
                _ => 10 > 20,
            }) by (compute_only);

            assert(match Option::Some(false) {
                Option::Some(b) => !b,
                _ => 10 > 20,
            }) by (compute_only);

            assert(match Option::<bool>::None {
                Option::Some(_) => false,
                _ => 20 > 10,
            }) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tuples verus_code! {
        spec fn mk_tuple() -> (u32, u32, u64, bool) {
            (42, 330, 0x1_0000_0000, false)
        }

        fn test() {
            assert(mk_tuple().0 == 42) by (compute_only);
            assert(mk_tuple().1 == 330) by (compute_only);
            assert(mk_tuple().2 - 0xFFFF_FFFF == 1) by (compute_only);
            assert(!mk_tuple().3) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] structs verus_code! {
        struct Example {
            u1: u32,
            u2: u64,
            b: bool,
        }

        fn test(e: Example) {
            assert(e.u1 == e.u1) by (compute_only);
            assert(e.u2 == e.u2) by (compute_only);
            assert(e.b == e.b) by (compute_only);

            assert({
                #[spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                e1.u1 > 5
            }) by (compute_only);
            assert({
                #[spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                e1.u2 == 0x1_0000_0000
            }) by (compute_only);
            assert({
                #[spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                !e1.b
            }) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] closures verus_code! {

        fn test(x: u64) {
            assert((|x:int| x + 1)(5) == 6) by (compute_only);
            let y = 5;
            assert((|x:int| x + y)(5) == 10) by (compute);
            assert({
                let y:int = 10;
                (|x:int| x + y)(5) == 15
            }) by (compute_only);
            assert((|x:int,y:int| x + y)(40, 2) == 42) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_calls_good verus_code! {
        spec fn f(x: int, y: int) -> bool { x == y }

        spec fn g(x: int) -> bool { f(3int, x) }

        spec fn sum(x: nat) -> nat 
            decreases(x)
        {
            if x == 0 { 0 } else { 1 + sum((x - 1) as nat) }
        }

        #[verifier(external_body)]
        spec fn f_no_body(x: nat) -> nat {
            0
        }

        #[verifier(external_body)]
        spec fn g_no_body(x: nat) -> nat {
            0
        }

        fn test() {
            assert(sum(20) == 20) by (compute_only);
            assert(sum(10) == 10) by (compute_only);
            assert(sum(0) == 0) by (compute_only);
            assert({
                let x = 22;
                let z = g(x);
                !!!z    // Exercise an unusual recursive case inside the interpreter
            }) by (compute_only);
            assert(f_no_body(5) == f_no_body(5)) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_calls_bad1 verus_code! {
        #[verifier(external_body)]
        spec fn f_no_body(x: nat) -> nat {
            0
        }

        #[verifier(external_body)]
        spec fn g_no_body(x: nat) -> nat {
            0
        }

        fn test() {
            assert(f_no_body(5) != f_no_body(6)) by (compute_only); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fn_calls_bad2 verus_code! {
        #[verifier(external_body)]
        spec fn f_no_body(x: nat) -> nat {
            0
        }

        #[verifier(external_body)]
        spec fn g_no_body(x: nat) -> nat {
            0
        }

        fn test() {
            assert(f_no_body(5) == g_no_body(5)) by (compute_only); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fn_calls_bad3 verus_code! {
        mod privacy_invasion {
            #[allow(unused_imports)]
            use builtin::assert_by_compute_only;

            mod mostly_private {
                pub closed spec fn f() -> u32 { 1 }
            }

            fn test() {
                assert(mostly_private::f() == 1) by (compute_only); // FAILS
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] sequences verus_code! {
        #[allow(unused_imports)]
        use crate::pervasive::seq::*;

        proof fn test() {
            assert(Seq::<u32>::empty().len() == 0) by (compute_only);
            assert(Seq::<u32>::empty().push(4).len() == 1) by (compute_only);
            assert(Seq::<u32>::empty().push(4).last() == 4) by (compute_only);
            assert(Seq::<u32>::empty().push(1).push(2).index(1) == 2) by (compute_only);
            assert(seq![1int, 2, 3].len() == 3) by (compute_only);
            assert(seq![1int, 2, 3].index(0) == 1) by (compute_only);
            assert(seq![1int, 2, 3].index(1) == 2) by (compute_only);
            assert(seq![1int, 2, 3].index(2) == 3) by (compute_only);
            assert(seq![1int, 2, 3].last() == 3) by (compute_only);
            assert(seq![1int, 2, 3].update(1, 5).index(0) == 1) by (compute_only);
            assert(seq![1int, 2, 3].update(1, 5).index(1) == 5) by (compute_only);
            assert(seq![1int, 2, 3].update(1, 5).index(2) == 3) by (compute_only);
            assert(seq![1int, 2, 3].add(seq![4, 5]).len() == 5) by (compute_only);
            assert(seq![1int, 2, 3].ext_equal(seq![1].add(seq![2, 3]))) by (compute_only);
            assert(seq![1int, 2].subrange(1, 2).ext_equal(seq![2])) by (compute_only);
            assert(seq![1int, 2, 3, 4, 5].subrange(2, 4).ext_equal(seq![3, 4])) by (compute_only);
            assert(Seq::new(5, |x| x).index(3) == 3) by (compute_only);
            assert(Seq::new(5, |x| x + x).index(3) == 6) by (compute_only);
            assert(Seq::new(5, |x| x + x).last() == 8) by (compute_only);
            assert(Seq::new(5, |x| x + x).subrange(1,4).ext_equal(seq![2, 4, 6])) by (compute_only);
        }

        spec fn use_seq(s: &Seq<u32>) -> (u32, u32) {
            let s_new = s.update(1, 42);
            let s_add = s.push(13).add(seq![14, 15, 16]);
            (s_new.index(1), s_add.index(4))
        }

        fn test_seq_modification() {
            assert({
                let v = seq![0, 1, 2];
                use_seq(&v).0 == 42 && use_seq(&v).1 == 14 && v.index(1) == 1
            }) by (compute_only);
        }
    } => Ok(())
}
