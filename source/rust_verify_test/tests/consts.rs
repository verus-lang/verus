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
    } => Err(err) => assert_rust_error_msg(err, "cycle detected when simplifying constant for the type system `C`")
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
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a `decreases` clause")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::f` with mode exec")
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
    #[test] dual_mode_const_branch_on_spec_const_issue3211 verus_code! {
        pub spec const S: bool = true;
        const C: u8 = if S { 1 } else { 2 };
    } => Err(e) => assert_vir_error_msg(e, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] exec_static_branch_on_spec_const_issue3211 verus_code! {
        pub spec const S: bool = true;
        exec static X: u8 = if S { 1 } else { 2 };
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
    } => Err(e) => assert_vir_error_msg(e, "Verus does not currently support static mut")
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
    } => Err(e) => assert_vir_error_msg(e, "explicitly mark the `static` item as `exec`")
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
    } => Err(err) => assert_vir_error_msgs(err, &[
        "cannot read static with mode exec",
        "cannot read static with mode exec",
    ])
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
    } => Err(err) => assert_vir_error_msgs(err, &[
        "cannot read const with mode exec",
        "cannot read const with mode exec",
    ])
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

test_verify_one_file_with_options! {
    #[test] arrays_reference [] => verus_code! {
        use vstd::prelude::*;

        const MyArray: &'static [u32; 3] = &[1, 2, 3];

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

test_verify_one_file! {
    #[test] const_with_ensures_issue2175 code! {
        #[verus_spec(ensures true)]
        pub const C: char = 'x';
    } => Ok(())
}

test_verify_one_file! {
    #[test] const_with_ensures_in_verus_macro_issue2175 verus_code! {
        #[verus_spec(ensures true)]
        pub const C: char = 'x';
    } => Err(err) => {
        assert!(err.warnings.len() == 1);
        assert!(err.errors.len() == 1);
        assert!(err.warnings[0].message.contains("#[verus_spec] is likely used inside a verus! block"));
        assert_vir_error_msg(err, "const is marked `exec` mode but also has an internal `open` attribute (note: this can happen if `#[verus_spec(...)]` is used inside the `verus!` macro)");
    }
}

test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/2659
    // A type parameter from the surrounding `impl` block should be usable in an
    // associated const's type.
    #[test] assoc_const_impl_type_param_issue2659 verus_code! {
        enum Maybe<T> { Nothing, Just(T) }

        struct WrappedU64<T> {
            val: u64,
            t: Maybe<T>,
        }

        struct MyStruct<T> { t: T }

        impl<T> MyStruct<T> {
            const X: WrappedU64<T> = WrappedU64 {
                val: 42,
                t: Maybe::Nothing,
            };
        }

        fn test() {
            let w = MyStruct::<bool>::X;
            assert(w.val == 42);
        }
    } => Ok(())
}

test_verify_one_file! {
    // Referencing the value of a generic associated const should still verify facts
    // about the value, so a false assertion must fail.
    #[test] assoc_const_impl_type_param_fails_issue2659 verus_code! {
        enum Maybe<T> { Nothing, Just(T) }

        struct WrappedU64<T> {
            val: u64,
            t: Maybe<T>,
        }

        struct MyStruct<T> { t: T }

        impl<T> MyStruct<T> {
            const X: WrappedU64<T> = WrappedU64 {
                val: 42,
                t: Maybe::Nothing,
            };
        }

        fn test() {
            let w = MyStruct::<bool>::X;
            assert(w.val == 43); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // A generic associated const whose type does not mention the type parameter,
    // used from a generic function with a trait bound.
    #[test] assoc_const_impl_type_param_bounded_issue2659 verus_code! {
        trait Tr { spec fn v() -> u64; }

        struct S<T> { t: T }

        impl<T: Tr> S<T> {
            const C: u64 = 7;
        }

        fn test<T: Tr>() {
            let c = S::<T>::C;
            assert(c == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    // A generic associated const whose type refers to an associated type of a trait
    // bound on the impl's type parameter (`T::Assoc` where `T: Tr`).
    #[test] assoc_const_impl_type_param_assoc_type_issue2659 verus_code! {
        trait Tr {
            type Assoc;
        }

        enum Wrapper<A> { Empty, Full(A) }

        struct MyStruct<T> { t: T }

        impl<T: Tr> MyStruct<T> {
            const X: Wrapper<T::Assoc> = Wrapper::Empty;
        }

        fn test<T: Tr>() {
            let w = MyStruct::<T>::X;
            assert(w is Empty);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_attr_spec_const_issue3147 verus_code! {
        #[verifier::exec]
        spec const C: bool = true;
    } => Err(err) => assert_vir_error_msg(err, "conflicting mode attributes: `exec` and `spec`")
}

test_verify_one_file! {
    #[test] conflicting_const_attrs_without_verus_issue3147 code! {
        #[verifier::exec]
        #[verifier::spec]
        const C: u64 = 5;
    } => Err(err) => assert_vir_error_msg(err, "conflicting mode attributes: `exec` and `spec`")
}

// Rust's const evaluator must not observe items changed by ghost erasure.
test_verify_one_file! {
    #[test] array_length_ghost_const verus_code! {
        use vstd::prelude::*;
        spec const N: usize = 5;
        fn f() -> (r: usize) ensures r == 8 {
            let a = [0u8; core::mem::size_of_val(&N)];
            a.len()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] const_generic_ghost_const verus_code! {
        use vstd::prelude::*;
        spec const N: usize = 5;
        struct S<const K: usize> { a: [u8; K] }
        fn f() { let s = S::<{ core::mem::size_of_val(&N) }> { a: [0; 8] }; }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] const_default_ghost_const verus_code! {
        use vstd::prelude::*;
        spec const N: usize = 5;
        struct S<const K: usize = { core::mem::size_of_val(&N) }> { a: [u8; K] }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] discriminant_ghost_const verus_code! {
        use vstd::prelude::*;
        spec const N: usize = 5;
        #[repr(usize)]
        enum E { A = core::mem::size_of_val(&N) }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] array_length_ghost_proof verus_code! {
        use vstd::prelude::*;
        const proof fn p() {}
        fn f() { let a = [0u8; { p(); 8 }]; }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::p` with mode proof")
}

test_verify_one_file! {
    #[test] array_length_ghost_associated_const verus_code! {
        use vstd::prelude::*;
        struct S;
        trait T { const N: usize; }
        impl T for S { const N: usize = 7; }
        impl S { spec const N: usize = 0; }
        fn f() -> (r: usize) ensures r == 0 {
            let a = [0u8; S::N];
            a.len()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] array_length_external_exec_const code! {
        use vstd::prelude::*;
        const C: usize = 5;
        const fn c() -> usize { C }
        verus! {
            assume_specification[C] -> usize returns 5usize;
            assume_specification[c]() -> usize returns 5usize;

            fn f() -> (r: usize) ensures r == 5 {
                let a: [u8; C] = [0u8; c()];
                a.len()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] array_length_ghost_const_in_exec_const verus_code! {
        use vstd::prelude::*;
        spec const N: usize = 5;
        exec const C: usize = {
            let a = [0u8; core::mem::size_of_val(&N)];
            a.len()
        };
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

// Rust's const evaluator checks arithmetic in anonymous constants; Verus does not verify it.
test_verify_one_file! {
    #[test] array_length_arithmetic_not_verified code! {
        use vstd::prelude::*;
        const K: usize = 3;
        verus! {
            assume_specification[K] -> usize;

            fn f() {
                let a = [0u8; (1 << K) - 1];
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] array_length_external_body_signature verus_code! {
        use vstd::prelude::*;
        spec const N: usize = 5;
        #[verifier::external_body]
        fn make() -> [u8; core::mem::size_of_val(&N)] {
            Default::default()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

// In the tests below, the array type `A` has the length that const evaluation computes
// during type checking, and `observed` returns it. The compiled program uses the same values,
// which the tests that run the binary print.

// `verus!` stubs only the syntactic `spec const`, so the compiled program evaluates consts and
// const fns with a hand-written `#[verifier::spec]`, and so does const evaluation
const ATTRIBUTE_SPEC_CONST: &str = code_str! {
    use vstd::prelude::*;
    verus! {
        #[verifier::spec]
        pub const N: usize = 5;
        pub struct S;
        impl S {
            #[verifier::spec]
            pub const N: usize = 6;
        }
        #[verifier::spec]
        pub const fn n() -> usize { 7 }
    }
    type A = [u8; N + S::N + n()];
    verus! {
        fn observed(a: A) -> (r: usize) ensures r == 18 { a.len() }
    }
    fn main() { println!("{} {} {} {}", N, S::N, n(), observed([0u8; 18])); }
};

#[test]
fn attribute_spec_const_is_evaluated() {
    assert_eq!(verify_compile_and_run(ATTRIBUTE_SPEC_CONST, &[]), "5 6 7 18\n");
}

const SYNTACTIC_SPEC_CONST: &str = code_str! {
    use vstd::prelude::*;
    verus! {
        pub spec const N: usize = 5usize;
    }
    type A = [u8; N];
    verus! {
        fn observed(a: A) -> (r: usize) ensures r == 0 { a.len() }
    }
    fn main() { println!("{}", observed([0u8; N])); }
};

#[test]
fn syntactic_spec_const_is_stubbed() {
    assert_eq!(verify_compile_and_run(SYNTACTIC_SPEC_CONST, &[]), "0\n");
}

test_verify_one_file! {
    #[test] hand_written_ghost_attributes_are_evaluated code! {
        use vstd::prelude::*;
        verus! {
            // In exec code, verification ignores these attributes on expressions
            // other than blocks, and so does const evaluation
            pub const fn f1() -> (r: usize)
                ensures r == 1
            {
                let mut x: usize = 0;
                #[verifier::proof_block] x = 1;
                x
            }
            pub const fn f2() -> (r: usize)
                ensures r == 2
            {
                let mut x: usize = 0;
                #[verifier::spec] x = 2;
                x
            }
        }
        // Unverified code under ghost attributes is evaluated as exec code
        pub const fn f3() -> usize {
            let mut x: usize = 0;
            #[verifier::proof_block] { x = 3; }
            x
        }
        pub const fn f4() -> usize {
            let mut x: usize = 0;
            #[verifier::spec] let _y = { x = 4; 0usize };
            x
        }
        pub const fn f5() -> usize {
            let mut x: usize = 0;
            let _g = verus_builtin::ghost_exec({ x = 5; 0u8 });
            x
        }
        pub const SUM: usize = f1() + f2() + f3() + f4() + f5();
        type A = [u8; SUM];
        verus! {
            fn observed(a: A) -> (r: usize) ensures r == 15 { a.len() }
        }
    } => Ok(())
}

// `verus_exec_expr_keep_ghost!` and `verus_exec_expr_erase_ghost!` remove their ghost code in
// the compiled program, and so does const evaluation
const EXEC_EXPR_MACROS: &str = code_str! {
    use vstd::prelude::*;
    pub const M2: usize = 7;
    pub const K1: usize =
        verus_exec_expr_keep_ghost!({ let mut x: usize = 1; proof { x = M2; } x });
    pub const K2: usize =
        verus_exec_expr_erase_ghost!({ let mut x: usize = 1; proof { x = M2; } x });
    type A = [u8; K1 + K2];
    verus! {
        fn observed(a: A) -> (r: usize) ensures r == 2 { a.len() }
    }
    fn main() { println!("{} {} {}", K1, K2, observed([0u8; K1 + K2])); }
};

#[test]
fn exec_expr_macros_ghost_code_is_erased() {
    assert_eq!(verify_compile_and_run(EXEC_EXPR_MACROS, &[]), "1 1 2\n");
}

// The compiled program keeps the body of a proof const without its ghost `let`s, and const
// evaluation evaluates the same code
const PROOF_CONST: &str = code_str! {
    use vstd::prelude::*;
    verus! {
        pub proof const P: u8 = { let ghost g: u8 = 1u8; u8::MAX };
    }
    type A = [u8; P as usize];
    verus! {
        fn observed(a: A) -> (r: usize) ensures r == 255 { a.len() }
    }
    fn main() { println!("{} {}", P, observed([0u8; 255])); }
};

#[test]
fn proof_const_is_evaluated() {
    assert_eq!(verify_compile_and_run(PROOF_CONST, &[]), "255 255\n");
}

// The compiled program leaves out a proof const that is not `pub`, and const evaluation skips its
// body too (`lemma` is not a const fn)
test_verify_one_file! {
    #[test] private_proof_const_is_skipped verus_code! {
        proof fn lemma() {}
        proof const P: u8 = { lemma(); 7 };
    } => Ok(())
}

// Ghost code from the attribute macros and `proof!`/`proof_decl!` in a verified const fn
const ATTRIBUTE_MACROS_GHOST_CODE: &str = code_str! {
    use vstd::prelude::*;
    verus! {
        pub proof fn seven() -> (r: u64) ensures r == 7 { 7 }
    }
    #[verus_verify]
    #[verus_spec(r =>
        requires n < 10
        ensures r == n + 1
    )]
    pub const fn f(n: u8) -> u8 {
        let mut x: u8 = n;
        proof_decl! {
            let ghost g: int = x as int;
        }
        proof! { let s = seven(); assert(g == n && s == 7); }
        x = x + 1;
        x
    }
    pub const K: u8 = f(3);
    type A = [u8; K as usize];
    verus! {
        fn observed(a: A) -> (r: usize) ensures r == 4 { a.len() }
    }
    fn main() { println!("{} {}", K, observed([0u8; 4])); }
};

#[test]
fn attribute_macros_ghost_code_is_erased() {
    assert_eq!(verify_compile_and_run(ATTRIBUTE_MACROS_GHOST_CODE, &[]), "4 4\n");
}

// Without vstd, the markers of the `verus_builtin_macros` crate count: `N` is stubbed during
// verification as in the compiled program, so the assertion holds in both
const NO_VSTD_SPEC_CONST: &str = code_str! {
    verus! {
        pub spec const N: usize = 5usize;
    }
    const _: () = assert!(N == 0);
    type A = [u8; N];
    fn main() { println!("{}", core::mem::size_of::<A>()); }
};

#[test]
fn no_vstd_spec_const_is_stubbed() {
    let args = ["--no-vstd", "--cfg", "verus_no_vstd"];
    assert_eq!(verify_compile_and_run(NO_VSTD_SPEC_CONST, &args), "0\n");
}
