#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_ref_0 verus_code! {
        fn test_ref_0(p: int)
            requires p == 12
        {
            let b: &int = &p;
            assert(*b == 12);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ref_1 verus_code! {
        fn test_ref_1(p: &u64)
            requires *p == 12
        {
            let b: &u64 = p;
            assert(*b == 12);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_ref_0 verus_code! {
        fn return_ref(p: &u64) -> (r: &u64)
            ensures r == p
        {
            p
        }

        fn test_ret() {
            let a = 2;
            let b = return_ref(&a);
            assert(*b == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_ref_named_lifetime verus_code! {
        fn return_ref<'a>(p: &'a u64) -> (r: &'a u64)
            ensures r == p
        {
            p
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_exec verus_code! {
        fn add1(a: &mut u64)
            requires *old(a) < 10
            ensures *a == *old(a) + 1
        {
            *a = *a + 1;
        }

        fn caller() {
            let mut a = 2;
            add1(&mut a);
            assert(a == 3);
        }
    } => Ok(())
}

const MUT_REF_PROOF_COMMON: &str = verus_code_str! {
    fn add1(Tracked(a): Tracked<&mut int>)
        requires old(a) < 10,
        ensures a == old(a) + 1,
    {
        proof {
            *a = *a + 1;
        }
    }
};

test_verify_one_file! {
    #[test] test_mut_ref_arg_proof_fail MUT_REF_PROOF_COMMON.to_string() + verus_code_str! {
        fn caller() {
            let mut a = 2;
            add1(&mut a);
            assert(a == 3);
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    // TODO(main_new) is this supposed to work?
    #[ignore] #[test] test_mut_ref_arg_proof_pass MUT_REF_PROOF_COMMON.to_string() + verus_code_str! {
        fn caller() {
            let tracked mut a = 2;
            add1(Tracked(&mut a));
            assert(a == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_invalid_spec verus_code! {
        fn add1(a: &mut u64)
            requires *a < 10
        {
            *a = *a + 1;
        }
    } => Err(err) => assert_vir_error_msg(err, "in requires, use `old(a)` to refer to the pre-state of an &mut variable") // error: in requires, use `old(a)` to refer to the pre-state of an &mut variable
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_invalid_spec_decreases verus_code! {
        proof fn add1(a: &mut u64)
            decreases (*a as int),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "in decreases clause, use `old(a)` to refer to the pre-state of an &mut variable")
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_spec verus_code! {
        spec fn add1(a: &mut u64) {
            *a = add(*a, 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "&mut parameter not allowed for spec functions")
}

test_verify_one_file! {
    // TODO(utaal) better/safer error check for this
    #[ignore] #[test] test_mut_ref_unsupported_1 verus_code! {
        fn test0() {
            let a = 3;
            let b = &mut a;
        }
    } => Err(err) => assert_vir_error_msg(err, "ignored test")
}

const MUT_REF_ARG_SELF_COMMON: &str = verus_code_str! {
    pub struct Value {
        pub v: u64,
    }

    impl Value {
        pub fn add1(&mut self)
            requires old(self).v < 10
            ensures self.v == old(self).v + 1
        {
            let Value { v } = *self;
            *self = Value { v: v + 1 };
        }
    }
};

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_pass_1 MUT_REF_ARG_SELF_COMMON.to_string() + verus_code_str! {
        fn caller() {
            let mut v = Value { v: 2 };
            v.add1();
            assert(v.v == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_pass_2 MUT_REF_ARG_SELF_COMMON.to_string() + verus_code_str! {
        fn caller() {
            let mut v = Value { v: 2 };
            v.add1();
            v.add1();
            assert(v.v == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_fail_1 MUT_REF_ARG_SELF_COMMON.to_string() + verus_code_str! {
        fn caller_fail() {
            let mut v = Value { v: 2 };
            v.add1();
            v.add1();
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_fail_2 MUT_REF_ARG_SELF_COMMON.to_string() + verus_code_str! {
        fn caller1() {
            let mut v = Value { v: 2 };
            v.add1();
            assert(v.v == 4); // FAILS
        }

        fn caller2() {
            let mut v = Value { v: 12 };
            v.add1(); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_complex_pass MUT_REF_ARG_SELF_COMMON.to_string() + verus_code_str! {
        pub struct Wrap {
            pub w: Value,
        }

        impl Wrap {
            fn outer(&mut self)
                requires old(self).w.v == 2
            {
                self.w.add1();
                assert(self.w.v == 3);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_spec verus_code! {
        #[verifier::spec]
        pub struct Value {
            pub v: u64,
        }

        impl Value {
            pub closed spec fn add1(&mut self) {
                let Value { v } = *self;
                *self = Value { v: add(v, 1) };
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "&mut parameter not allowed for spec functions")
}

test_verify_one_file! {
    #[test] test_mut_ref_generic_1 verus_code! {
        fn add1<A>(a: &mut A)
            ensures equal(*old(a), *a)
        {
        }

        fn caller() {
            let mut a = 2;
            add1(&mut a);
            assert(a == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_old_shadow verus_code! {
        fn add1(a: &mut u64)
            ensures equal(*old(a), *a)
        {
            let a = true;
            assert(old(a) == true);
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test_mut_ref_typing_invariant verus_code! {
        fn add1(a: &mut u64) {
            assert(*a >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_forward verus_code! {
        fn div2(a: &mut u64)
            ensures *a == *old(a) / 2
        {
            *a = *a / 2;
        }

        fn test(b: &mut u64)
            ensures *b == *old(b) / 2
        {
            div2(b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_trigger_0 verus_code! {
        #[verifier::external_body]
        struct A {
            _p: std::marker::PhantomData<()>,
        }

        impl A {
            #[verifier::external_body]
            spec fn index(&self, i: nat) -> nat { unimplemented!() }
        }

        exec fn add1(a: &mut A, i: usize)
            ensures
                forall|j: nat| a.index(j) == old(a).index(j) + 1
        {
            assume(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_old_trigger verus_code! {
        use vstd::prelude::*;

        fn add1(v: &mut Vec<u64>)
            requires
                forall|i: int| 0 <= i < old(v).len() ==> old(v)[i] < 10,
        {
        }

        fn test(v: Vec<u64>)
            requires
                forall|i: int| 0 <= i < v.len() ==> v[i] < 5,
        {
            let mut v1 = v;
            add1(&mut v1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_shadow verus_code! {
        fn foo(x: &mut u32)
            ensures equal(*x, *old(x))
        {
        }

        fn main() {
            let h = 5;

            let mut h = 6;
            foo(&mut h);

            assert(h == 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_regression_115_mut_ref_pattern_case_1 code! {
        #[verifier::proof]
        #[verifier::external_body] /* vattr */
        #[verifier::returns(proof)] /* vattr */
        fn foo(#[verifier::proof] x: &mut int) -> (int, int)
        {
            ensures(|ret: (int, int)|
                { let (a, b) = ret;
                    a + b == (*x)
                });

            unimplemented!();
        }

        fn bar(#[verifier::proof] x: int) {
            #[verifier::proof] let mut x = x;
            #[verifier::proof] let (a, b) = foo(&mut x);
            builtin::assert_(a + b == x); // THIS LINE FAILS
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_regression_115_mut_ref_pattern_case_2 ["--no-external-by-default"] => code! {
        fn foo(x: &mut bool) -> (u8, u8) {
            ensures(|ret: (u8, u8)| (*x) == ! *old(x));

            *x = ! *x;
            (0, 0)
        }

        fn bar(#[verifier::proof] x: int) {
            let mut x = true;
            let (a, b) = foo(&mut x);
            builtin::assert_(x == true); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_regression_115_mut_ref_eval_order verus_code! {
        struct Foo {
            pub a: u64,
            pub b: bool,
            pub c: bool,
        }

        fn do_mut(x: &mut u64) -> (b: u64)
            ensures *x == 1 && b == 1
        {
            *x = 1;
            1
        }

        fn same_foo(foo: Foo) -> (res: Foo)
            ensures equal(res, foo)
        {
            foo
        }

        fn test() {
            let foo = Foo { a: 0, b: false, c: false };
            let mut x = 5;
            let bar = Foo {
                a: (do_mut(&mut x) + (x * 2)), // should evaluate to 1 + 1 * 2 = 3
                ..same_foo(foo)
            };
            assert(bar.a == 3);
            assert(bar.a == 11); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_mut_ref_field_pass_1 verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        struct S {
            a: u32,
            b: i32,
            c: bool,
        }

        fn add1(a: &mut u32, b: &mut i32)
            requires
                *old(a) < 10,
                *old(b) < 10,
            ensures
                *a == *old(a) + 1,
                *b == *old(b) + 1,
        {
            *a = *a + 1;
            *b = *b + 1;
        }

        fn main() {
            let mut s = S { a: 5, b: -5, c: false };
            add1(&mut s.a, &mut s.b);
            assert(s == S { a: 6, b: -4i32, c: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_field_pass_2 verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        struct S<A> {
            a: A,
            b: bool,
        }

        fn add1(a: &mut u32)
            requires *old(a) < 10
            ensures *a == *old(a) + 1
        {
            *a = *a + 1;
        }

        fn main() {
            let mut s = S { a: 5, b: false };
            add1(&mut s.a);
            assert(s == S { a: 6u32, b: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_field_and_update_pass verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        struct S<A> {
            a: A,
            b: bool,
        }

        fn add1(a: &mut u32) -> (ret: u32)
            requires
                *old(a) < 10
            ensures
                *a == *old(a) + 1,
                ret == *old(a)
        {
            *a = *a + 1;
            *a - 1
        }

        fn main() {
            let mut s = S { a: 5, b: false };
            s.a = add1(&mut s.a);
            assert(s == S { a: 5u32, b: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] deref_allowed_but_must_be_declared verus_code! {
        struct X { a: u8 }

        #[verifier::external]
        impl core::ops::Deref for X {
            type Target = u8;
            fn deref(&self) -> &Self::Target {
                &self.a
            }
        }

        fn test(a: &X)
        {
            let t: &u8 = &a;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `crate::X::deref`")
}

test_verify_one_file! {
    #[test] deref_vec_ok verus_code! {
        use vstd::prelude::*;
        use std::ops::Deref;
        fn test1(v: Vec<u8>) {
            let s0: &[u8] = v.as_slice();
            let s1: &[u8] = v.deref();
            let s2: &[u8] = &v;
            assert(s0@ == s1@);
            assert(s0@ == s2@);
            let i2 = v.iter();
        }
        fn test2(v: &Vec<u8>) {
            let s0: &[u8] = v.as_slice();
            let s1: &[u8] = v.deref();
            let s2: &[u8] = &v;
            assert(s0@ == s1@);
            assert(s0@ == s2@);
            let i2 = v.iter();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] deref_vec_fails verus_code! {
        use vstd::prelude::*;
        use std::ops::Deref;
        fn test1(v: Vec<u8>) {
            let s0: &[u8] = v.as_slice();
            let s1: &[u8] = v.deref();
            let s2: &[u8] = &v;
            let i2 = v.iter();
            assert(s0@ == s1@);
            assert(s0@ != s2@); // FAILS
        }
        fn test2(v: &Vec<u8>) {
            let s0: &[u8] = v.as_slice();
            let s1: &[u8] = v.deref();
            let s2: &[u8] = &v;
            let i2 = v.iter();
            assert(s0@ == s1@);
            assert(s0@ != s2@); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] deref_vec_alone1 verus_code! {
        use vstd::prelude::*;
        fn test1(v: Vec<u8>) {
            let s2: &[u8] = &v;
        }
        fn test2(v: &Vec<u8>) {
            let s2: &[u8] = &v;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] deref_vec_alone2 verus_code! {
        use vstd::prelude::*;
        fn test1(v: Vec<u8>) {
            let i2 = v.iter();
        }
        fn test2(v: &Vec<u8>) {
            let i2 = v.iter();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutref_arg_ref_unsupported verus_code! {
        fn stuff(x: &mut &u8) { }

        fn test() {
            let mut y: u8 = 0;
            stuff(&mut &y); // this does NOT modify y
        }
    } => Err(err) => assert_vir_error_msg(err, "complex arguments to &mut parameters are currently unsupported")
}

test_verify_one_file! {
    #[test] mut_ref_coerce_to_ref_with_old_issue671 verus_code! {
        spec fn check_inc(a: &u32, b: &u32) -> bool {
            &&& *a == *b + 1
        }

        fn add1(a: &mut u32)
            requires
                *old(a) < 10,
            ensures
                //*a == *old(a) + 1,
                check_inc(a, old(a)),
        {
            *a = *a + 1;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_overloaded_deref verus_code! {
        use core::ops::Deref;

        pub struct X {
            pub inner: usize,
        }

        #[verifier::external_trait_specification]
        pub trait ExDeref {
            type ExternalTraitSpecificationFor: core::ops::Deref;

            type Target: ?Sized;

            fn deref(&self) -> &Self::Target;
        }

        pub open spec fn x_deref_spec(x: &X) -> (ret: &usize) {
            &x.inner
        }

        impl Deref for X {
            type Target = usize;

            #[verifier::when_used_as_spec(x_deref_spec)]
            fn deref(&self) -> (ret: &usize)
                ensures
                    ret == self.inner,
            {
                &self.inner
            }
        }

        fn do_exec_deref(x: &X)
            requires 100 <= x.inner < 102
        {
            // Explicit call.
            let u: &usize = &((*x).deref());
            assert(100 <= *u < 102);
            // Implicit call.
            let v: &usize = &**x;
            assert(100 <= *v < 102);
        }

        spec fn do_explicit_spec_deref(x: &X) -> &usize {
            &((*x).deref())
        }

        spec fn do_implicit_spec_deref(x: &X) -> &usize {
            &**x
        }
    } => Ok(())
}
