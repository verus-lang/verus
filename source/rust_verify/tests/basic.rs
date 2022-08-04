#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        fn test1() {
            assert(true);
            assert(!false);
            assert(true && true);
            assert(true || false);
            assert(true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        fn test1() {
            assert(true);
            assert(true && false); // FAILS
            assert(false);
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        spec fn f(i: int, j: int) -> bool;

        fn test2(b: bool, x: int, y: int, z: int) {
            assert(b || !b);

            assume(b);
            assert(b);

            assert(x == y ==> f(x, y) == f(y, x));

            assert(x + y == y + x);

            assume(x <= y && y <= z);
            assert(x <= z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        fn test2(b: bool, x: int, y: int, z: int) {
            assume(x <= y && y <= z);
            assert(x < z); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_assign verus_code! {
        fn test_assign(a: int, b: int) {
            let c = a + b;
            assert(c == a + b);

            let d = false;
            assert(!d);

            assert(c < a + b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_assign_mut verus_code! {
        fn test_assign_mut(a: int, b: int) {
            let mut c = a;
            c = c + b;
            assert(c == a + b);
            assert(c == a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_spec_fn verus_code! {
        spec fn f1(i: int, j: int) -> bool {
            i <= j
        }

        spec fn f2(i: int, j: int) -> bool {
            let x = i;
            let y = j;
            x < y
        }

        #[verifier(opaque)]
        spec fn f3(i: int, j: int) -> bool {
            f1(j, i)
        }

        fn test_spec_fn(a: int, b: int) {
            hide(f2);

            assume(f2(a, b));
            reveal(f2);
            assert(f1(a, b));

            reveal(f3);
            assert(f3(b, a));
            assert(f3(a, b)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

const TEST_REQUIRES1: &str = verus_code_str! {
    proof fn test_requires1(a: int, b: int, c: int)
        requires
            a <= b,
            b <= c,
    {
        assert(a <= c);
    }
};

test_verify_one_file! {
    #[test] test_requires2 TEST_REQUIRES1.to_string() + verus_code_str! {
        proof fn test_requires2(a: int, b: int, c: int) {
            assume(a <= b);
            assume(b <= c);
            test_requires1(a + a, b + b, c + c);
            test_requires1(a + a, b + b, a + c); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_requires3 TEST_REQUIRES1.to_string() + verus_code_str! {
        fn test_requires3(a: int, b: int, c: int) {
            assume(a <= b);
            assume(b <= c);
            proof {
                test_requires1(a + a, b + b, c + c);
                test_requires1(a + c, b + b, c + c); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

const TEST_RET: &str = verus_code_str! {
    proof fn test_ret(a: int, b: int) -> (ret: int)
        requires
            a <= b,
        ensures
            ret <= a + b,
            ret <= a + a, // FAILS
            ret <= b + b,
    {
        a + b
    }
};

test_verify_one_file! {
    #[test] test_ret TEST_RET.to_string() => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_ret2 TEST_RET.to_string() + verus_code_str! {
        proof fn test_ret2(a: int, b: int) -> (ret: int)
            requires
                a <= b,
            ensures
                ret <= a + b,
                ret <= a + a,
                ret <= b + b,
        {
            let mut x = test_ret(a, a);
            x = test_ret(x, x);
            assert(x <= 4 * a);
            x = test_ret(b, b);
            x = test_ret(x, x);
            assert(x <= 4 * b);
            x = test_ret(a + 1, a + 2);
            x = test_ret(x + 3, x + 4);
            assert(x <= 4 * a + 4 + 6);
            x = test_ret(a, b);
            x
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_exec_fun1 verus_code! {
        fn f(x: u64) -> u64 {
            5
        }

        fn g(x: u64) -> u64 {
            f(x)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_short_circuit verus_code! {
        use crate::pervasive::modes::*;
        fn f1(a: bool, b: bool) {
            let mut x: u64 = 0;
            let y = a && b;
            let z = a && { x = x + 1; b };
            assert(y == z);
            assert((x == 1) == a);
        }

        fn f2(a: bool, b: bool) {
            let mut x: u64 = 0;
            let y = a || b;
            let z = a || { x = x + 1; b };
            assert(y == z);
            assert((x == 1) == !a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_short_circuit1 code! {
        fn f3(a: bool, b: bool) {
            #[spec] let mut x: u64 = 0;
            #[spec] let y: bool = imply(a, b);
            #[spec] let z: bool = imply(a, { x = x + 1; b });
            assert(y == z);
            assert((x == 1) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_short_circuit2 verus_code! {
        fn f1(a: bool, b: bool) {
            let mut x: u64 = 0;
            let y = a && b;
            let z = a && { x = x + 1; b };
            assert(y == z);
            assert(x == 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_short_circuit3 verus_code! {
        fn f1(a: bool, b: bool) {
            let mut x: u64 = 0;
            let y = a && b;
            let z = a && { x = x + 1; b };
            assert(y == z);
            assert(x == 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_paren verus_code! {
        fn test_paren() {
            {{{{if true {} else {}}}}}
            ((((if true {} else {}))))
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fail_assign_non_mut verus_code! {
        fn test1() {
            let x: u64 = 10;
            x = 20;
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_fail_return_value_parameter_same_name verus_code! {
        fn foo(x: u64) -> (x: bool)
            ensures x || !x
        {
            x > 10
        }
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test_ensures_type_inference verus_code! {
        struct Foo {
            pub b: bool,
        }

        spec fn get_b(foo: Foo) -> bool {
            foo.b
        }

        fn test1() -> (b: Foo)
            ensures get_b(b)
        {
            Foo { b: true }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_decl_init_let_pass verus_code! {
        fn test1() {
            let x: u64;
            x = 23;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_decl_init_let_fail verus_code! {
        fn test1() {
            let x: u64;
            assert(x == 23); // FAILS
            x = 23;
        }

        fn test2(a: bool) {
            let x: u64;
            if a {
                x = 1;
            } else {
                x = 2;
            }
            assert(a ==> (x == 1));
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] bool_xor verus_code! {
        fn test1() {
            assert((true ^ true) == false);
            assert((false ^ true) == true);
            assert((true ^ false) == true);
            assert((false ^ false) == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] bool_xor_fails verus_code! {
        fn test1() {
            assert((true ^ true) == true); // FAILS
        }
        fn test2() {
            assert((false ^ true) == false); // FAILS
        }
        fn test3() {
            assert((true ^ false) == false); // FAILS
        }
        fn test4() {
            assert((false ^ false) == true); // FAILS
        }
    } => Err(e) => assert_fails(e, 4)
}

test_verify_one_file! {
    #[test] test_init_spec_param_fail_1 code! {
        fn test1(#[spec] x: u64) {
            x = 5;
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_init_spec_param_fail_2 verus_code! {
        spec fn test1(x: u64) {
            x = 5;
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    // TODO restore this test when erasure is overhauled
    #[ignore] #[test] equal_regression_148 code! {
        #[proof]
        fn f() {
            equal(1 as nat, 1);
        }
    } => Ok(())
}
