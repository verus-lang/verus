#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON_TRAIT_AND_TYPE: &str = verus_code_str! {
    trait Tr {
        spec fn afunction(&self) -> bool;
    }

    struct A { }

    impl Tr for A {
        spec fn afunction(&self) -> bool { true }
    }
};

test_verify_one_file! {
    #[test] trait_fn_free_fn_nogeneric COMMON_TRAIT_AND_TYPE.to_string() + verus_code_str! {
        fn some_fn_nogeneric(a: A) {
            hide(<A as Tr>::afunction);
            reveal(<A as Tr>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_nogeneric COMMON_TRAIT_AND_TYPE.to_string() + verus_code_str! {
        impl A {
            fn some_fn_nogeneric(&self) {
                hide(<A as Tr>::afunction);
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_self_nogeneric COMMON_TRAIT_AND_TYPE.to_string() + verus_code_str! {
        impl A {
            fn some_fn_nogeneric(&self) {
                reveal(<Self as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Self is not supported in reveal/hide")
}

test_verify_one_file! {
    #[test] trait_fn_trait_fn_nogeneric verus_code! {
        trait Tr {
            spec fn afunction(&self) -> bool;
            proof fn aproof(&self);
        }

        struct A { }

        impl Tr for A {
            #[verifier::opaque]
            spec fn afunction(&self) -> bool { true }

            proof fn aproof(&self) {
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

const COMMON_TRAIT_AND_TYPE_WITH_GENERIC: &str = verus_code_str! {
    trait Tr<T> {
        spec fn afunction(&self) -> bool;
    }

    struct A<T> {
        t: T,
    }

    impl<T> Tr<T> for A<T> {
        spec fn afunction(&self) -> bool { true }
    }
};

test_verify_one_file! {
    #[test] trait_fn_free_fn_generic_1 COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        fn some_fn_generic<T>(a: A<T>) {
            hide(<A<_> as Tr<_>>::afunction);
            reveal(<A<_> as Tr<_>>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_free_fn_generic_2 COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        fn some_fn_generic<T>(a: A<T>) {
            hide(<A as Tr>::afunction);
            reveal(<A as Tr>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_generic COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        impl<T> A<T> {
            fn some_fn_generic(&self) {
                hide(<A as Tr>::afunction);
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_self_generic COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        impl<T> A<T> {
            fn some_fn_generic(&self) {
                reveal(<Self as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Self is not supported in reveal/hide")
}

test_verify_one_file! {
    #[test] trait_fn_trait_fn_generic verus_code! {
        trait Tr {
            spec fn afunction(&self) -> bool;
            proof fn aproof(&self);
        }

        struct A { }

        impl Tr for A {
            #[verifier::opaque]
            spec fn afunction(&self) -> bool { true }

            proof fn aproof(&self) {
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_free_fn_expanded_invalid_1 COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + code_str! {
        #[verus::internal(verus_macro)]
        fn some_fn_generic<T>(a: A<T>) {
            #[verifier::proof_block]
            {
                ::verus_builtin::reveal_hide_({
                        #[verus::internal(reveal_fn)]
                        fn __VERUS_REVEAL_INTERNAL__() {
                            let a = ();

                            ::verus_builtin::reveal_hide_internal_path_(<A<_> as Tr<_>>::afunction)
                        }
                        __VERUS_REVEAL_INTERNAL__
                    }, 1)
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "invalid reveal/hide")
}

const STRUCT_AND_INHERENT_FN: &str = verus_code_str! {
    struct A<T> {
        t: T,
    }

    impl<T> A<T> {
        #[verifier::opaque]
        spec fn afunction(&self) -> bool { true }
    }
};

test_verify_one_file! {
    #[test] struct_fn_free_fn_1 STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::<_>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_fn_free_fn_2 STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_fn_free_fn_3_incorrect_type STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::<usize>::afunction); // produces a warning
            assert(a.afunction());
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().find(|x| x.message.contains("in hide/reveal, type arguments are ignored")).is_some());
    }
}

test_verify_one_file! {
    #[test] mod_invalid_1 verus_code! {
        mod m1 {}

        fn aproof(a: nat) {
            reveal(m1);
        }
    } => Err(err) => assert_rust_error_msg(err, "expected value, found module")
}

test_verify_one_file! {
    #[test] struct_fn_free_fn_4_not_found STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::wrong);
            assert(a.afunction());
        }
    } => Err(err) => assert_vir_error_msg(err, "`wrong` not found")
}

test_verify_one_file! {
    #[test] across_modules_and_use verus_code! {
        mod m1 {
            pub struct A<T> {
                t: T,
            }

            impl<T> A<T> {
                #[verifier::opaque]
                pub open spec fn afunction(&self) -> bool { true }
            }

            #[verifier::opaque]
            pub open spec fn bfunction() -> bool { true }
        }

        mod m2 {
            use crate::m1::*;
            fn aproof(a: A<u64>) {
                reveal(A::afunction);
                assert(a.afunction());

                reveal(bfunction);
                assert(bfunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] across_crates verus_code! {
        use vstd::seq::*;
        proof fn aproof(s: Seq<nat>)
            requires s == seq![1nat, 2nat],
        {
            reveal_with_fuel(Seq::filter, 3);
            assert(s.filter(|x| x == 1) =~= seq![1nat]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trailing_commas verus_code! {
        spec fn s(x:int) -> bool
            decreases x,
        {
            if x <= 0 { true}
            else {
                s(x - 1)
            }
        }

        // We treat hide/reveal like other Rust functions,
        // which allow trailing commas
        proof fn test() {
            hide(s,);
            reveal(s,);
            reveal_with_fuel(s,2,);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_704_impl_arg verus_code! {
        trait X {}
        impl X for int {}

        #[verifier::opaque]
        spec fn foo(x: impl X) -> bool {
            true
        }

        proof fn test() {
            reveal(foo);
            assert(foo(3int));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_907_reveal_u64_1 verus_code! {
        trait Tau {
            spec fn foo(&self)->bool;
            fn bar(&self);
        }
        struct T {}
        impl Tau for T {
            spec fn foo(&self)->bool {
                true
            }
            fn bar(&self){
                reveal(<T as Tau>::foo);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_907_reveal_u64_2 verus_code! {
        trait Tau {
            spec fn foo(&self)->bool;
            fn bar(&self);
        }
        impl Tau for u64 {
            spec fn foo(&self)->bool {
                true
            }
            fn bar(&self){
                reveal(<u64 as Tau>::foo);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] regression_925_reveal_loop_1 verus_code! {
        #[verifier::opaque]
        const X: usize = 1;

        fn foo() by (nonlinear_arith) {
            let mut i: usize = 0;
            reveal(X);
            while i < X
                ensures i >= 1
            {
                reveal(X);
                assume(false);
                break;
                reveal(X);
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] regression_925_reveal_loop_2 verus_code! {
        #[verifier::opaque]
        spec fn x_spec() -> usize { 1 }

        fn x() -> (r: usize)
            ensures r == x_spec()
        {
            reveal(x_spec);
            1
        }

        fn foo() {
            let mut i: usize = 0;
            reveal(x_spec);
            while i < x()
                ensures i >= 1
            {
                reveal(x_spec);
                i += 1;
                assert(i >= 1);
                break;
                reveal(x_spec);
                assert(i >= 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] no_broadcast_use_as_reveal_1 verus_code! {
        #[verifier::opaque]
        spec fn f() -> bool { true }

        proof fn foo() {
            broadcast use f;
        }
    } => Err(err) => assert_vir_error_msg(err, "`broadcast use` statements require a broadcast proof fn")
}

test_verify_one_file! {
    #[ignore] #[test] no_broadcast_use_as_reveal_2 verus_code! {
        mod m1 {
            #[verifier::opaque]
            pub open spec fn f() -> bool { true }
        }

        mod m2 {
            use vstd::prelude::*;
            use crate::m1::*;

            broadcast use f;

            proof fn foo() {
                assert(f());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "test_crate::m1::f is not a broadcast proof fn")
}

test_verify_one_file! {
    #[test] reveal_closed_error verus_code! {
        mod m {
            use super::*;

            pub closed spec fn foo(u: u64) -> u64
                decreases u
            {
                if u == 0 { 0 } else { foo((u-1) as u64) }
            }
        }

        proof fn q() {
            reveal(m::foo);
            assert(m::foo(0) == 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal/fuel statement is not allowed here because the function `test_crate::m::foo` is marked 'closed' and thus its body is not visible here")
}

test_verify_one_file! {
    #[test] reveal_closed_not_error verus_code! {
        mod m {
            use super::*;

            pub closed spec fn foo(u: u64) -> u64
                decreases u
            {
                if u == 0 { 0 } else { foo((u-1) as u64) }
            }

            proof fn q() {
                reveal(foo);
                assert(foo(0) == 0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_function_that_isnt_recursive_but_has_decreases_issue644 verus_code! {
        pub open spec fn pow(b: int, e: nat) -> int
            decreases e
        {
            if e == 0 {
                1
            } else {
                b * pow(b, (e - 1) as nat)
            }
        }

        spec fn pow2(e: nat) -> nat
            decreases e
        {
            pow(2 as int, e) as nat
        }

        proof fn lemma2_5()
        {
            assert(pow2(1) == 0x2) by {
                reveal_with_fuel(pow2, 3);
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "this function is not recursive (nor mutually recursive), so fuel cannot be set to more than 1")
}

test_verify_one_file! {
    #[test] reveal_visible_inside_isolated_loop verus_code! {
        #[verifier::opaque]
        spec fn pred() -> bool { true }

        spec fn open_pred() -> bool { true }

        fn revealed_before_loop() {
            reveal(pred);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(pred());
                i = i + 1;
            }
        }

        fn open_spec_needs_no_reveal() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(open_pred());
                i = i + 1;
            }
        }

        fn hide_then_reveal() {
            hide(open_pred);
            reveal(open_pred);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(open_pred());
                i = i + 1;
            }
        }

        fn reveal_in_boundary_and_before_nested() {
            reveal(pred);
            let mut i: u64 = 0;
            #[verus::internal(loop_isolation_boundary)]
            {
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    let mut j: u64 = 0;
                    while j < 1
                        invariant j <= 1,
                        decreases 1 - j,
                    {
                        assert(pred());
                        j = j + 1;
                    }
                    i = i + 1;
                }
            }
        }

        fn reveal_inside_branch_loop(b: bool) {
            if b {
                reveal(pred);
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(pred());
                    i = i + 1;
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_with_fuel_bound_survives_loop verus_code! {
        #[verifier::opaque]
        spec fn down(i: nat) -> nat
            decreases i,
        {
            if i == 0 {
                0
            } else {
                1 + down((i - 1) as nat)
            }
        }

        fn enough_fuel() {
            reveal_with_fuel(down, 2);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(down(1) == 1);
                i = i + 1;
            }
        }

        fn nested_gets_outer_and_inner_fuel() {
            reveal_with_fuel(down, 2);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                reveal_with_fuel(down, 3);
                let mut j: u64 = 0;
                while j < 1
                    invariant j <= 1,
                    decreases 1 - j,
                {
                    assert(down(2) == 2);
                    j = j + 1;
                }
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_fuel_does_not_leak_or_deepen verus_code! {
        #[verifier::opaque]
        spec fn pred() -> bool { true }

        spec fn open_pred() -> bool { true }

        #[verifier::opaque]
        spec fn down(i: nat) -> nat
            decreases i,
        {
            if i == 0 {
                0
            } else {
                1 + down((i - 1) as nat)
            }
        }

        fn opaque_without_reveal() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(pred()); // FAILS
                i = i + 1;
            }
        }

        fn hide_suppresses_default_inside_loop() {
            hide(open_pred);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(open_pred()); // FAILS
                i = i + 1;
            }
        }

        fn reveal_after_loop() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(pred()); // FAILS
                i = i + 1;
            }
            reveal(pred);
        }

        fn sibling_branch(b: bool) {
            if b {
                reveal(pred);
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(pred());
                    i = i + 1;
                }
            } else {
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(pred()); // FAILS
                    i = i + 1;
                }
            }
        }

        fn only_inside_completed_loop() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                reveal(pred);
                assert(pred());
                i = i + 1;
            }
            let mut j: u64 = 0;
            while j < 1
                invariant j <= 1,
                decreases 1 - j,
            {
                assert(pred()); // FAILS
                j = j + 1;
            }
        }

        fn fuel_too_small() {
            reveal_with_fuel(down, 1);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(down(1) == 1); // FAILS
                i = i + 1;
            }
        }

        fn deeper_fuel_in_sibling_does_not_leak(b: bool) {
            if b {
                reveal_with_fuel(down, 3);
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(down(2) == 2);
                    i = i + 1;
                }
            } else {
                reveal_with_fuel(down, 2);
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(down(2) == 2); // FAILS
                    i = i + 1;
                }
            }
        }

        fn deeper_fuel_inside_loop_does_not_escape() {
            reveal_with_fuel(down, 2);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                reveal_with_fuel(down, 3);
                assert(down(2) == 2);
                i = i + 1;
            }
            let mut j: u64 = 0;
            while j < 1
                invariant j <= 1,
                decreases 1 - j,
            {
                assert(down(2) == 2); // FAILS
                j = j + 1;
            }
        }

        // An ordinary fact is still isolated when a reveal is in scope.
        fn precondition_stays_isolated(x: u64)
            requires x == 5,
        {
            reveal(pred);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(pred());
                assert(x == 5); // FAILS
                i = i + 1;
            }
        }
    } => Err(err) => assert_fails(err, 9)
}
