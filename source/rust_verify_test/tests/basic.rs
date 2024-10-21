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
            proof {
                reveal(f2);
            }
            assert(f1(a, b));

            proof {
                reveal(f3);
            }
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
    #[test] test_short_circuit1 verus_code! {
        proof fn f3(a: bool, b: bool) {
            let mut x: u64 = 0;
            let y: bool = imply(a, b);
            let z: bool = imply(a, { x = add(x, 1); b });
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
    } => Err(err) => assert_rust_error_msg(err, "cannot assign twice to immutable variable")
}

test_verify_one_file! {
    #[test] test_fail_return_value_parameter_same_name verus_code! {
        fn foo(x: u64) -> (x: bool)
            ensures x || !x
        {
            x > 10
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter name cannot be the same as the return value name")
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
            #[allow(unused_assignments)]
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
    #[test] test_init_spec_param_fail_1 verus_code! {
        proof fn test1(x: u64) {
            x = 5;
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot assign to non-mut parameter")
}

test_verify_one_file! {
    #[test] test_init_spec_param_fail_2 verus_code! {
        spec fn test1(x: u64) {
            x = 5;
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot assign to non-mut parameter")
}

test_verify_one_file! {
    // TODO restore this test when erasure is overhauled
    #[ignore] #[test] equal_regression_148 code! {
        #[verifier::proof]
        fn f() {
            equal(1 as nat, 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_big_and verus_code! {
        proof fn test() {
            assert({ &&& true &&& true });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_big_and_fail verus_code! {
        proof fn test() {
            assert({ &&& true &&& false }); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_big_or verus_code! {
        proof fn test() {
            assert({ ||| true ||| false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_big_or_fail verus_code! {
        proof fn test() {
            assert({ ||| fails ||| false }); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_big_and_syntax_vs_forall verus_code! {
        spec fn test() -> bool {
            &&& forall|i: int| true
            &&& i == 0
        }
    } => Err(e) => assert_rust_error_msg(e, "cannot find value `i`")
}

test_verify_one_file! {
    #[test] test_compound_assign verus_code! {
        fn test1(y: &mut u32) {
            let mut x: i32 = 1;
            x += 2;
            assert({ x == 3 as i32 });
            *y /= 2;
            assert({ *y == *old(y)/2 });
        }

        proof fn test2a() {
            let mut x: u8 = 200;
            x = (x + 100u8) as u8;
            assert(x < 256);
        }

        proof fn test2b() {
            let mut x: u8 = 200;
            x += 100u8;
            assert(x < 256);
        }

        fn test3a() {
            let mut x: u8 = 200;
            x = x / (x + 1);
            assert(x < 256);
        }

        fn test3b() {
            let mut x: u8 = 200;
            x /= (x + 1);
            assert(x < 256);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_compound_assign_fail verus_code! {
        fn test1(x: &mut u32, y: u32) {
            *x /= y; // FAILS
        }

        fn test2(x: i8) {
            let mut x = x;
            x += 1; // FAILS
        }

        fn test3a() {
            let mut x: u8 = 200;
            x = x + 100u8; // FAILS
            assert(x < 256);
        }

        fn test3b() {
            let mut x: u8 = 200;
            x += 100u8; // FAILS
            assert(x < 256);
        }

    } => Err(err) => assert_fails(err, 4)
}

fn assert_spec_eq_type_err(err: TestErr, typ1: &str, typ2: &str) {
    assert_eq!(err.errors.len(), 1);
    let err0 = &err.errors[0];
    assert!(err0.code.is_none());
    assert!(err0.message.contains("mismatched types; types must be compatible to use == or !="));
    assert!(err0.spans.len() == 2 || err0.spans.len() == 3);
    assert_spans_contain(err0, typ1);
    assert_spans_contain(err0, typ2);
}

test_verify_one_file! {
    #[test] test_spec_eq_type_error_1 verus_code! {
        fn test(a: u64, b: Option<u64>)
            requires a == b { }
    } => Err(err) => assert_spec_eq_type_err(err, "u64", "::Option<u64>")
}

test_verify_one_file! {
    #[test] test_spec_eq_type_error_2 verus_code! {
        fn test(a: u64, b: std::sync::Arc<Option<u64>>)
            requires a == b { }
    } => Err(err) => assert_spec_eq_type_err(err, "u64", "::Option<u64>")
}

test_verify_one_file! {
    #[test] test_spec_eq_type_error_3 verus_code! {
        fn test(a: u64, b: spec_fn(u64)->nat)
            requires a == b { }
    } => Err(err) => assert_spec_eq_type_err(err, "u64", "spec_fn(u64) -> nat")
}

test_verify_one_file! {
    #[test] test_spec_eq_type_error_4 verus_code! {
        trait A {
            type AT;
        }

        fn test<X: A>(a: (u64, nat), b: <X as A>::AT)
            requires a == b { }
    } => Err(err) => assert_spec_eq_type_err(err, "(u64, nat)", "<X as crate::A>::AT")
}

test_verify_one_file! {
    #[test] test_spec_eq_type_error_5 verus_code! {
        fn test() {
            let a = |x: i32| x + 3;
            assert(a == 5);
        }
    } => Err(err) => assert_spec_eq_type_err(err, "nat", "AnonymousClosure(i32) -> i32")
}

test_verify_one_file! {
    #[test] test_mut_param verus_code! {
        fn test1(mut x: u32)
            requires
                x < 10,
            ensures
                // mut params are always evaluated to their original
                // value in postconditions
                x < 10,
        {
            assert(x < 20);
            x = 100;
            assert(x == 100);
        }

        fn test2(mut x: u32)
            requires
                x < 10;
            ensures
                x == 100, // FAILS
        {
            assert(x < 20);
            x = 100;
            assert(x == 100);
        }

        proof fn test3(mut x: int) {
            x += 1;
        }

        struct T {
            x: i32,
            y: u64,
        }

        fn test4(mut t: T) {
            let y = t.y;
            t.x = 100;
            assert(t.x == 100);
            assert(t.y == y);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_mut_param_spec_fail verus_code! {
        spec fn f(mut x: i32) -> i32;
    } => Err(err) => assert_vir_error_msg(err, "mut argument not allowed for spec functions")
}

test_verify_one_file! {
    #[test] test_mut_self_disallowed verus_code! {
        struct T{}

        impl T {
            fn test(mut self) {
                self = T{};
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: mut self")
}

test_verify_one_file! {
    #[test] test_rlimit_20 verus_code! {
        #[verifier::rlimit(20)]
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
    #[test] test_rlimit_inf verus_code! {
        #[verifier::rlimit(infinity)]
        fn test1() {
            assert(true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_bodyless_fn verus_code! {
        // We allow a final comma in the ensures
        // list for a bodyless function
        trait Marshalable {
            spec fn is_marshalable(&self) -> bool;
            exec fn _is_marshalable(&self) -> (res: bool)
                ensures res == self.is_marshalable(),
            ;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_is_core ["--is-core", "no-auto-import-builtin"] => code! {
        #![allow(unused_parens)]
        #![allow(unused_imports)]
        #![allow(dead_code)]
        #![allow(unused_attributes)]
        #![allow(unused_variables)]

        #![feature(strict_provenance)]
        #![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
        #![cfg_attr(verus_keep_ghost, feature(allocator_api))]
        #![cfg_attr(verus_keep_ghost, feature(step_trait))]
        #![cfg_attr(verus_keep_ghost, feature(ptr_metadata))]
        #![cfg_attr(verus_keep_ghost, feature(strict_provenance_atomic_ptr))]
        #![cfg_attr(
            verus_keep_ghost,
            feature(fn_traits),
        )]

        #[verifier::external]
        #[path="../../../../builtin/src/lib.rs"]
        mod builtin;

        #[path="../../../../vstd/vstd.rs"]
        mod vstd;

        mod test {
            use crate::vstd::set::*;
            use crate::vstd::seq::*;
            use crate::vstd::multiset::*;
            use crate::vstd::prelude::*;

            verus!{

            proof fn test_seqs(a: Seq<int>, b: Seq<int>)
                requires a == b,
            {
                crate::vstd::seq_lib::assert_seqs_equal!(a, b);
                crate::vstd::seq_lib::assert_seqs_equal!(a == b);
            }

            proof fn test_sets(a: Set<int>, b: Set<int>)
                requires a == b,
            {
                crate::vstd::set_lib::assert_sets_equal!(a, b);
                crate::vstd::set_lib::assert_sets_equal!(a == b);
            }

            proof fn test_multisets(a: Multiset<int>, b: Multiset<int>)
                requires a == b,
            {
                crate::vstd::multiset::assert_multisets_equal!(a, b);
                crate::vstd::multiset::assert_multisets_equal!(a == b);
            }

            fn test_slice_index(x: &[u8]) -> u8
                requires x@.len() > 0
            {
                x[0]
            }

            fn test_ptr_stuff(a: *mut u8, b: *mut [u8; 2]) {
                let t = a as *mut u16;
                let s = b as *mut [u8];
            }

            }
        }

        fn main() { }
    } => Ok(())
}
