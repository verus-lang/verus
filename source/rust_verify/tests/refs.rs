#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_ref_0 code! {
        fn test_ref_0(p: int) {
            requires(p == 12);
            let b: &int = &p;
            assert(*b == 12);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ref_1 code! {
        fn test_ref_1(p: &u64) {
            requires(*p == 12);
            let b: &u64 = p;
            assert(*b == 12);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_ref_0 code! {
        fn return_ref(p: &u64) -> &u64 {
            ensures(|r: &u64| r == p);
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
    #[test] test_return_ref_named_lifetime code! {
        fn return_ref<'a>(p: &'a u64) -> &'a u64 {
            ensures(|r: &u64| r == p);
            p
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_exec code! {
        fn add1(a: &mut u64) {
            requires(*old(a) < 10);
            ensures(*a == *old(a) + 1);
            *a = *a + 1;
        }

        fn caller() {
            let mut a = 2;
            add1(&mut a);
            assert(a == 3);
        }
    } => Ok(())
}

const MUT_REF_PROOF_COMMON: &str = code_str! {
    fn add1(#[proof] a: &mut u64) {
        requires(*old(a) < 10);
        ensures(*a == *old(a) + 1);
        *a = *a + 1;
    }
};

test_verify_one_file! {
    #[test] test_mut_ref_arg_proof_fail MUT_REF_PROOF_COMMON.to_string() + code_str! {
        fn caller() {
            let mut a = 2;
            add1(&mut a);
            assert(a == 3);
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_proof_pass MUT_REF_PROOF_COMMON.to_string() + code_str! {
        fn caller() {
            #[proof] let mut a = 2;
            add1(&mut a);
            assert(a == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_invalid_spec code! {
        fn add1(a: &mut u64) {
            requires(*a < 10);
            *a = *a + 1;
        }
    } => Err(e) => assert_vir_error(e) // error: in requires, use `old(a)` to refer to the pre-state of an &mut variable
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_spec code! {
        #[spec]
        fn add1(a: &mut u64) {
            *a = *a + 1;
        }
    } => Err(e) => assert_vir_error(e) // error: &mut argument not allowed for #[spec] functions
}

test_verify_one_file! {
    // TODO(utaal) better/safer error check for this
    #[ignore] #[test] test_mut_ref_unsupported_1 code! {
        fn test0() {
            let a = 3;
            let b = &mut a;
        }
    } => Err(e) => assert_vir_error(e)
}

const MUT_REF_ARG_SELF_COMMON: &str = code_str! {
    pub struct Value {
        pub v: u64,
    }

    impl Value {
        pub fn add1(&mut self) {
            requires(old(self).v < 10);
            ensures(self.v == old(self).v + 1);
            let Value { v } = *self;
            *self = Value { v: v + 1 };
        }
    }
};

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_pass_1 MUT_REF_ARG_SELF_COMMON.to_string() + code_str! {
        fn caller() {
            let mut v = Value { v: 2 };
            v.add1();
            assert(v.v == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_pass_2 MUT_REF_ARG_SELF_COMMON.to_string() + code_str! {
        fn caller() {
            let mut v = Value { v: 2 };
            v.add1();
            v.add1();
            assert(v.v == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_fail_1 MUT_REF_ARG_SELF_COMMON.to_string() + code_str! {
        fn caller_fail() {
            let mut v = Value { v: 2 };
            v.add1();
            v.add1();
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_fail_2 MUT_REF_ARG_SELF_COMMON.to_string() + code_str! {
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
    #[test] test_mut_ref_arg_self_complex_pass MUT_REF_ARG_SELF_COMMON.to_string() + code_str! {
        pub struct Wrap {
            pub w: Value,
        }

        impl Wrap {
            fn outer(&mut self) {
                requires(old(self).w.v == 2);
                self.w.add1();
                assert(self.w.v == 3);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_arg_self_spec code! {
        #[spec]
        pub struct Value {
            pub v: u64,
        }

        impl Value {
            #[spec]
            pub fn add1(&mut self) {
                let Value { v } = *self;
                *self = Value { v: v + 1 };
            }
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_mut_ref_generic_1 code! {
        fn add1<A>(a: &mut A) {
            ensures(equal(*old(a), *a));
        }

        fn caller() {
            let mut a = 2;
            add1(&mut a);
            assert(a == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_old_shadow code! {
        fn add1(a: &mut u64) {
            ensures(equal(*old(a), *a));
            let a = true;
            assert(old(a) == true);
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_mut_ref_typing_invariant code! {
        fn add1(a: &mut u64) {
            assert(*a >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_forward code! {
        fn div2(a: &mut u64) {
            ensures(*a == *old(a) / 2);
            *a = *a / 2;
        }

        fn test(b: &mut u64) {
            ensures(*b == *old(b) / 2);
            div2(b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_trigger_0 code! {
        #[verifier(external_body)]
        struct A {
            _p: std::marker::PhantomData<()>,
        }

        impl A {
            #[spec]
            #[verifier(external_body)]
            fn index(&self, i: nat) -> nat { unimplemented!() }
        }

        #[exec]
        fn add1(a: &mut A, i: usize) {
            ensures(forall(|j: nat| a.index(j) == old(a).index(j) + 1));
            assume(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_old_trigger code! {
        use crate::pervasive::vec::*;

        fn add1(v: &mut Vec<u64>) {
            requires(forall(|i: nat| i < old(v).len() >>= old(v).index(i) < 10));
        }

        fn test(v: Vec<u64>) {
            requires(forall(|i: nat| i < v.len() >>= v.index(i) < 5));
            let mut v1 = v;
            add1(&mut v1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_shadow code! {
        fn foo(x: &mut u32) {
            ensures(equal(*x, *old(x)));
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
        #[proof]
        #[verifier(external_body)]
        #[verifier(returns(proof))]
        fn foo(#[proof] x: &mut int) -> (int, int)
        {
            ensures(|ret: (int, int)|
                { let (a, b) = ret;
                    a + b == (*x)
                });

            unimplemented!();
        }

        fn bar(#[proof] x: int) {
            #[proof] let mut x = x;
            #[proof] let (a, b) = foo(&mut x);
            assert(a + b == x); // THIS LINE FAILS
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_regression_115_mut_ref_pattern_case_2 code! {
        fn foo(x: &mut bool) -> (u8, u8) {
            ensures(|ret: (u8, u8)| (*x) == ! *old(x));

            *x = ! *x;
            (0, 0)
        }

        fn bar(#[proof] x: int) {
            let mut x = true;
            let (a, b) = foo(&mut x);
            assert(x == true); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_regression_115_mut_ref_eval_order code! {
        struct Foo {
            pub a: u64,
            pub b: bool,
            pub c: bool,
        }

        fn do_mut(x: &mut u64) -> u64 {
            ensures(|b: u64| *x == 1 && b == 1);
            *x = 1;
            1
        }

        fn same_foo(foo: Foo) -> Foo {
            ensures(|res: Foo| equal(res, foo));
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
    #[test] test_mut_ref_field_pass_1 code! {
        #[derive(PartialEq, Eq, Structural)]
        struct S {
            a: u32,
            b: i32,
            c: bool,
        }

        fn add1(a: &mut u32, b: &mut i32) {
            requires([
                *old(a) < 10,
                *old(b) < 10,
            ]);
            ensures([
                *a == *old(a) + 1,
                *b == *old(b) + 1,
            ]);
            *a = *a + 1;
            *b = *b + 1;
        }

        fn main() {
            let mut s = S { a: 5, b: -5, c: false };
            add1(&mut s.a, &mut s.b);
            assert(s == S { a: 6, b: -4, c: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_field_pass_2 code! {
        #[derive(PartialEq, Eq, Structural)]
        struct S<A> {
            a: A,
            b: bool,
        }

        fn add1(a: &mut u32) {
            requires(*old(a) < 10);
            ensures(*a == *old(a) + 1);
            *a = *a + 1;
        }

        fn main() {
            let mut s = S { a: 5, b: false };
            add1(&mut s.a);
            assert(s == S { a: 6, b: false });
        }
    } => Ok(())
}
