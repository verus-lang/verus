#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_const_eval1 verus_code!{
        #[repr(u8)]
        enum TestConst {
            Zero = 0,
            One = 1,
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_const_eval2 verus_code!{
        const S: usize = 10;
        struct TestConst {
            a: [u8; S],
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test1 verus_code! {
        spec fn f() -> int { 1 }
        const C: u64 = 3 + 5;
        spec const S: int = C as int + f();
        const fn e() -> (u: u64) ensures u == 1 { 1 }
        exec const E: u64 ensures E == 2 { 1 + e() }

        fn test1() {
            let x = C;
            assert(x == 8);
            assert(S == 9);
            let y = E;
            assert(y == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        spec fn f() -> int { 1 }
        const C: u64 = 3 + 5;
        spec const S: int = C + f();

        fn test1() {
            let x = C;
            assert(x == 8);
            assert(S == 10); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        const C: u64 = S;
        const S: u64 = C;
    } => Err(err) => assert_rust_error_msg(err, "cycle detected when checking if `C` is a trivial const")
}

test_verify_one_file! {
    #[test] test1_fails_const_fn verus_code! {
        fn x() {
        }
        const fn y() {
            x()
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot call non-const function `x` in constant functions")
}

test_verify_one_file! {
    #[test] test1_fails3 verus_code! {
        spec const C: u64 = S;
        spec const S: u64 = C;
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test1_fails4 verus_code! {
        spec const C: u64 = add(3, 5);
        const S: int = C + 1;
    } => Err(err) => assert_rust_error_msg_all(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test1_fails5 verus_code! {
        const fn f() -> u64 { 1 }
        const S: u64 = 1 + f();
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::f` with mode exec")
}

test_verify_one_file! {
    #[test] test1_fails6 verus_code! {
        const fn e() -> (u: u64) ensures u >= 1 { 1 }
        exec const E: u64 = 1 + e(); // FAILS
    } => Err(e) => assert_vir_error_msg(e, "possible arithmetic underflow/overflow")
}

test_verify_one_file! {
    #[test] test1_fails7 verus_code! {
        exec const E: u64 ensures true { 1 }
        fn test1() {
            proof { let x = E; }
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot read const with mode exec")
}

test_verify_one_file! {
    #[test] test1_fails8 verus_code! {
        exec const E: u64 ensures true { 1 }
        proof fn test1() {
            let x = E;
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot read const with mode exec")
}

test_verify_one_file! {
    #[test] test1_fails9 verus_code! {
        spec const S: u64 = 1;
        fn test1() {
            let x = S;
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] test_used_as_spec verus_code! {
        spec const SPEC_E: u64 = 7;
        #[verifier::when_used_as_spec(SPEC_E)]
        exec const E: u64 ensures E == SPEC_E { 7 }

        fn test1() {
            let y = E;
            assert(y == E);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_use_const_twice verus_code! {
        // This behavior is important if X represents a Cell, for example

        #[verifier::external_body]
        struct X { }

        #[verifier::external_body]
        const fn x() -> X { X{} }

        exec const E: X = x();

        fn test1() {
            // think of 'E' as equivalent to 'x()'. Different calls might
            // return different values. (At least if x contains ghost content)
            let a = E;
            let b = E;
            assert(a == b); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] static_mut_unsupported verus_code! {
        static mut x: u64 = 0;
    } => Err(e) => assert_vir_error_msg(e, "Verus does not support 'static mut'")
}

test_verify_one_file! {
    #[test] test_use_static_twice verus_code! {
        #[verifier::external_body]
        struct X { }

        #[verifier::external_body]
        const fn x() -> X { X{} }

        exec static E: X = x();

        fn test1() {
            // These are 'the same' E
            let a = &E;
            let b = &E;
            assert(a == b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] spec_dual_mode_unsupported verus_code! {
        static E: u64 = 0;
    } => Err(e) => assert_vir_error_msg(e, "explicitly mark the static as `exec`")
}

test_verify_one_file! {
    #[test] reference_static_from_proof_unsupported verus_code! {
        exec static E: u64 = 0;

        proof fn stuff() {
            let x = E;
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot read static with mode exec")
}

test_verify_one_file! {
    #[test] reference_static_from_spec_unsupported verus_code! {
        exec static E: u64 = 0;

        // It might be feasible to support this, because although the value of `E`
        // is the result of an exec computation, it *is* fixed.
        // However, it would require us to be careful about cyclicity checking.

        spec fn stuff() -> u64 {
            E
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot read static with mode exec")
}

test_verify_one_file! {
    #[test] reference_static_from_dual_mode_const_unsupported verus_code! {
        exec static E: u64 = 0;

        const s: u64 = E;
    } => Err(e) => assert_vir_error_msg(e, "cannot read static with mode exec")
}

test_verify_one_file! {
    #[test] reference_static_from_proof_block_double_move verus_code! {
        struct X { }

        exec static E: X = X{};

        fn stuff() {
            proof {
                let tracked x = E;
                let tracked y = E;
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot read static with mode exec")
}

test_verify_one_file! {
    #[test] statics_get_type_invariants verus_code! {
        exec static E: u64 = 0;

        fn stuff() {
            let j = E;
            assert(j >= 0);
            assert(j <= 0xffff_ffff_ffff_ffff);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] statics_recurse2 verus_code! {
        exec static E: u64 ensures false {
            proof { let x = F; }
            0
        }
        exec static F: u64 ensures false {
            proof { let x = E; }
            0
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot read static with mode exec")
}

test_verify_one_file! {
    #[test] const_recurse2 verus_code! {
        exec const D: u64 = 1;
        exec const E: u64 ensures false {
            proof { let x = D; }
            0
        }
        exec const F: u64 ensures false {
            proof { let x = E; }
            0
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode exec")
}

test_verify_one_file! {
    #[test] return_static_lifetime verus_code! {
        exec static x: u8 = 0;

        fn stuff() -> &'static u8 {
            &x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pub_exec_const verus_code! {
        // https://github.com/verus-lang/verus/issues/858
        const fn foo() -> u64 {
            0
        }

        pub exec const FOO: u64 = foo();
    } => Ok(())
}

test_verify_one_file! {
    #[test] statics_atomics verus_code! {
        use vstd::*;

        pub fn heap_init() {
            increment_thread_count();
        }

        exec static THREAD_COUNT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

        #[inline]
        fn increment_thread_count() {
            THREAD_COUNT.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        }

        #[inline]
        pub fn current_thread_count() -> usize {
            THREAD_COUNT.load(core::sync::atomic::Ordering::Relaxed)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] statics_ens_ordering verus_code! {
        pub fn test() {
            test2();
        }

        exec static X: u32 ensures 2 <= X <= 4 { 3 }

        #[inline]
        fn test2() {
            let y = X;
            assert(2 <= y <= 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] arrays verus_code! {
        use vstd::prelude::*;

        const MyArray: [u32; 3] = [1, 2, 3];

        proof fn test() {
            assert(MyArray[2] == 3);
        }

        fn exec_test() {
            let x = MyArray[1];
            assert(x == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] array_out_of_bounds verus_code! {
        use vstd::prelude::*;

        const MyArray: [u32; 3] = [1, 2, 3];

        proof fn test() {
            assert(MyArray[5] == 3);    // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] array_incorrect_value verus_code! {
        use vstd::prelude::*;

        const MyArray: [u32; 3] = [1, 2, 3];

        proof fn test() {
            assert(MyArray[1] == 42);    // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] exec_const_body_with_proof_assert verus_code! {
        spec fn f() -> int { 1 }
        const fn e() -> (u: u64) ensures u == 1 { 1 }
        exec const E: u64 ensures E == 2 {
            assert(f() == 1);
            1 + e()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_const_body_with_proof_call verus_code! {
        #[verifier::opaque]
        spec fn f() -> int { 1 }
        proof fn e() -> (u: u64)
            ensures
                u == f(),
                u == 1
        {
            reveal(f);
            1
        }
        exec const E: u64 ensures E == f() {
            proof {
                let x = e();
                assert(x == f());
                assert(x == 1);
            }
            assert(1 == f());
            1
        }
    } => Ok(())
}

// This test is now ignored since this example is no longer
// accepted by standard Rust either;
// See https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&gist=10785374b063ad324e94c239589d5ac2
test_verify_one_file! {
    #[ignore] #[test] allow_external_body_const_regression_1322 verus_code! {
        #[verifier(external_body)]
        const A: usize = unimplemented!();
    } => Err(err) => assert_rust_error_msg(err, "evaluation of constant value failed")
}

test_verify_one_file! {
    #[test] allow_external_body_const_regression_1322_1 verus_code! {
        #[verifier::external]
        const fn stuff() -> usize { 0 }

        #[verifier(external_body)]
        const A: usize = stuff();
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] allow_external_body_const_regression_1322_2 verus_code! {
        #[verifier::external]
        const fn stuff() -> usize { 0 }

        #[verifier(external_body)]
        const A: usize ensures 32 <= A <= 52 { stuff() }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_const verus_code! {
        verus!{
            struct A {}

            impl A {
                pub const X: usize = 3;
                pub const Y: usize = 1usize << A::X;
                exec const B: u8
                    ensures Self::B < 10
                {
                    7
                }
                exec const C: u8
                    ensures Self::C < 10 // FAILS
                {
                    77
                }
            }

            fn test() {
                let x = A::X;
                let y = A::Y;
                assert(x == 3);
                assert(A::X == 3);
                assert(A::Y == 1usize << 3);
                assert(y == 1usize << 3);
                let b = A::B;
                assert(b < 11);
                assert(b < 9); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] assoc_const_fn verus_code! {
        struct A {
            u: u64,
        }

        impl A {
            const fn get_a(&self) -> (ret: u64)
                ensures ret == self.u
            {
                self.u
            }

            exec const R: u64 = Self::get_a(&A { u: 5 });

            fn test(&self) {
                let r = Self::get_a(&A { u: 5 });
                assert(r == 5);
            }

            const fn get_a_fail(&self) -> (ret: u64)
                ensures ret != self.u
            {
                return self.u; // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] assoc_const_struct verus_code! {
        pub struct Foo {
        }

        impl Foo {
            pub const BAR: Self = Self { };

            pub fn get_bar(&self) -> Foo {
                Foo::BAR
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] static_cross_modules_issue1810 verus_code! {
        mod mod_a {

            use vstd::prelude::*;

            pub exec static FOO: u64 ensures true
            {
                1
            }

        }

        use mod_a::FOO;
        use vstd::prelude::*;

        fn main() {
            if FOO == 1 {}
        }
    } => Ok(())
}
