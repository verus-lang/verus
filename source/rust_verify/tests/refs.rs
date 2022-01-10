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

test_verify_one_file! {
    #[test] test_mut_ref_arg_proof code! {
        fn add1(#[proof] a: &mut u64) {
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
    #[test] test_mut_ref_arg_self_fail MUT_REF_ARG_SELF_COMMON.to_string() + code_str! {
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
    #[test] test_mut_ref_arg_self_fail_complex MUT_REF_ARG_SELF_COMMON.to_string() + code_str! {
        pub struct Wrap {
            pub w: Value,
        }

        impl Wrap {
            fn outer(&mut self) {
                requires(old(self).w.v < 10);
                // currently disallowing this
                self.w.add1();
                assert(self.w.v == 3);
            }
        }
    } => Err(e) => assert_vir_error(e)
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

