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
            assert(!sub(0i32,1) == 0) by (compute_only);
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
        proof fn test(x: int) {
            assert((7 + 7 * 2 > 20) && (22 - 5 <= 10 * 10)) by (compute_only);
            assert(x + 0 == x) by (compute_only);
            assert(0 + x == x) by (compute_only);
            assert(x - 0 == x) by (compute_only);
            assert(x * 1 == x) by (compute_only);
            assert(1 * x == x) by (compute_only);
            assert(x * 0 == 0) by (compute_only);
            assert(0 * x == 0) by (compute_only);
            assert(x - x == 0) by (compute_only);
            assert(x / 1 == x) by (compute_only);
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

        proof fn test() {
            assert(9int == if 7 > 3 { 9int } else { 5 }) by (compute_only);
            assert(if true { true } else { false }) by (compute_only);
            assert(if !true { false } else { true }) by (compute_only);
            assert(if !!true { true } else { false }) by (compute_only);
            assert(9int == if (7 + 7 * 2 > 20) { 7int + 2 } else { 22 - 5 + 10*10 }) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lets verus_code! {

        fn test() {
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
    } => Err(err) => assert_vir_error_msg(err, "expression simplifies to false")
}

test_verify_one_file! {
    #[test] datatype verus_code! {
        use vstd::prelude::*;

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
                #[verifier::spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                e1.u1 > 5
            }) by (compute_only);
            assert({
                #[verifier::spec]
                let e1 = Example { u1: 42, u2: 0x1_0000_0000, b: false };
                e1.u2 == 0x1_0000_0000
            }) by (compute_only);
            assert({
                #[verifier::spec]
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
            // This cannot use compute_only, since it relies on
            // z3 filling in the value of y
            assert((|x:int| x + y)(5) == 10) by (compute);
            assert({
                let y:int = 10;
                (|x:int| x + y)(5) == 15
            }) by (compute_only);
            assert((|x:int,y:int| x + y)(40, 2) == 42) by (compute_only);
        }

        spec fn call_it(f: spec_fn(int) -> int, arg: int) -> int {
            let y: int = 100;
            f(arg)
        }

        proof fn scoping_test() {
            assert({
                let y: int = 10;
                call_it(|x: int| x + y, 3) == 13
            }) by (compute_only);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] closures_fail verus_code! {

        #[verifier(external_body)]
        spec fn call_it(f: spec_fn(int) -> int, arg: int) -> bool
        {
            true
        }

        fn test(x: u64) {
            assert({
                let f = |x:int| x + 7;
                call_it(f, 2)
            }) by (compute);   // FAILS
        }

    } => Err(err) => assert_vir_error_msg(err, "Proof by computation included a closure literal that wasn't applied")
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
    } => Err(err) => assert_vir_error_msg(err, "failed to simplify down to true")
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
    } => Err(err) => assert_vir_error_msg(err, "failed to simplify down to true")
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
    } => Err(err) => assert_vir_error_msg(err, "failed to simplify down to true")
}

test_verify_one_file! {
    #[test] sequences verus_code! {
        #[allow(unused_imports)]
        use vstd::seq::*;

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
            assert(seq![1int, 2, 3] =~= seq![1].add(seq![2, 3])) by (compute_only);
            assert(seq![1int, 2].subrange(1, 2) =~= seq![2]) by (compute_only);
            assert(seq![1int, 2, 3, 4, 5].subrange(2, 4) =~= seq![3, 4]) by (compute_only);
            assert(Seq::new(5, |x: int| x).index(3) == 3) by (compute_only);
            assert(Seq::new(5, |x: int| x + x).index(3) == 6) by (compute_only);
            assert(Seq::new(5, |x: int| x + x).last() == 8) by (compute_only);
            assert(Seq::new(5, |x: int| x + x).subrange(1,4) =~= seq![2, 4, 6]) by (compute_only);
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

        // GitHub issue 294: Make sure we don't let local variable names
        // leak out, even when a sequence function can't concretely evaluate
        spec fn f(s: &Seq<int>, idx: int) -> int {
            s.index(idx)
        }

        spec fn g(a: &Seq<int>, b: Seq<int>) -> Seq<int> {
            a.add(b)
        }

        // Try various combinations of simplified sequence
        // literal and symbolic values
        proof fn test_github_issue_294() {
            let x = seq![1, 2, 3];
            assert(f(&x, 0) == 1) by (compute);
            let y = seq![4, 5, 6];
            assert(g(&x, y).len() == 6) by (compute);
            assert({
                let z = seq![7, 8, 9];
                g(&x, z).len() == 6 &&
                g(&z, x).len() == 6
            }) by (compute);
            assert({
                let z: Seq<int> = seq![4, 5, 6];
                y == z &&
                z == y
            }) by (compute);
            assert({
                let z = seq![4int, 5int, 6int];
                y == z &&
                z == y
            }) by (compute);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mut_ref_and_ghost verus_code! {
        #[allow(unused_imports)]
        use vstd::seq::*;

        fn test(a: &mut u64)
            requires *old(a) < 1000,
            ensures *a == *old(a) + 30,
        {
            let ghost old_a = *a;
            *a = *a + 5 * 6;
            assert(*a == old_a + 5 * 6) by (compute);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] arch_specific_handling_1_test_regression_380 verus_code! {
        // GitHub issue 380: we should make sure not to make incorrect assumptions on size of
        // usize/isize when `size_of usize` is not set.
        fn test() {
            assert((1usize << 40usize) == 0usize) by (compute_only); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "failed to simplify down to true")
}

test_verify_one_file! {
    #[test] arch_specific_handling_2_test_regression_380 verus_code! {
        // GitHub issue 380: we should make sure not to make incorrect assumptions on size of
        // usize/isize when `size_of usize` is not set.
        //
        // Note that we should not be able to deduce `!= 0` here either.
        fn test() {
            assert((1usize << 40usize) != 0usize) by (compute_only); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "failed to simplify down to true")
}

test_verify_one_file! {
    #[test] arch_specific_handling_3_test_regression_380 verus_code! {
        // GitHub issue 380: we should make sure not to make incorrect assumptions on size of
        // usize/isize when `size_of usize` is not set.
        //
        // Note that we still do know that it is either 32-bit or 64-bit, so we should still be able
        // to deduce things about values that remain consistent amongst the two.
        fn test() {
            assert((1usize << 20usize) != 0usize) by (compute_only);
            assert((1usize << 100usize) == 0usize) by (compute_only);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] partially_simplified_boxed_sequence_699 verus_code! {
        #[allow(unused_imports)]
        use vstd::seq::*;

        // GitHub issue 699: When converting partially simplified
        // sequences to SST, handle boxed sequence types as well
        proof fn test() {
            let s: Seq<int> = seq![1, 2, 3, 4, 5];
            let even: Seq<int> = s.filter(|x: int| x % 2 == 0);
            assert(even =~= seq![2, 4]) by (compute);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] shift_regression_928_1 ["vstd"] => verus_code! {
        pub open spec fn id(x:int) -> int;

        pub proof fn bar() {
            assert(
                { (10 as u64 >> (id(5) as u64)) as int }
                == 0) by (compute); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] shift_regression_928_2 ["vstd"] => verus_code! {
        spec fn foo(size: int) -> int {
            let bits = usize::BITS as int;
            if bits == 1 {
                0
            } else {
                bits
            }
        }

        proof fn bar() {
            assert(foo(0) == 0) by (compute); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] char_casting verus_code! {
        proof fn assert_compute_test_int_to_char(c: char) {
            assert(0int as char == 0) by(compute_only);
            assert(0xD7FFint as char == 0xD7FF) by(compute_only);
            assert(0xE000int as char == 0xE000) by(compute_only);
            assert(0x10FFFFint as char == 0x10FFFF) by(compute_only);
        }
        proof fn assert_compute_test_int_to_char_fail1(c: char) {
            assert((-1int) as char == -1) by(compute); // FAILS
        }
        proof fn assert_compute_test_int_to_char_fail2(c: char) {
            assert((0xD800int) as char == 0xD800) by(compute); // FAILS
        }
        proof fn assert_compute_test_int_to_char_fail3(c: char) {
            assert((0xDFFFint) as char == 0xDFFF) by(compute); // FAILS
        }
        proof fn assert_compute_test_int_to_char_fail4(c: char) {
            assert((0x110000int) as char == 0x110000) by(compute); // FAILS
        }
        proof fn assert_compute_test_char_to_u8(c: char) {
            assert(('\u{3b1}' as u8) == '\u{3b1}') by(compute); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] array_literals verus_code! {
        use vstd::prelude::*;

        const MyArray: [u32; 3] = [31, 32, 33];

        proof fn mytest() {
            assert([41u32, 42][1] == 42) by (compute_only);
            assert(MyArray[1] == 32) by (compute_only);
            let x = 0;
            assert(MyArray[x] == 31) by (compute);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] array_incompletely_resolved verus_code! {
        use vstd::prelude::*;

        const MyArray: [u32; 3] = [1, 2, 3];

        proof fn test() {
            let x:int = 0;
            assert(MyArray[x] == 2) by (compute_only);     // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "failed to simplify down to true")
}
