#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Adapted from auto_spec tests in syntax_attr.rs
test_verify_one_file! {
    #[test] test_auto_spec verus_code! {
        #[vstd::contrib::auto_spec]
        pub fn f(x: u32, y: u32) -> u32
            requires
                x < 100,
                y < 100,
        {
            proof {
                assert(true);
            }
            x + y
        }

        #[vstd::contrib::auto_spec]
        pub fn f2(x: u32) -> u32
            requires
                x < 100,
        {
            f(x, 1)
        }

        struct S;

        impl S {
            #[vstd::contrib::auto_spec]
            fn foo(&self, x: u32) -> u32 {
                x / 2
            }
        }

        proof fn lemma_f(x: u32, y: u32)
            requires
                x < 100,
            ensures
                y == 1 ==> f(x, y) == f2(x),
                f(x, y) == f(y, x),
                f2(x) == f2(x),
                f(x, y) == (x + y) as u32,
                f2(x) == x + 1,
        {}

        mod inner {
            use super::*;
            proof fn lemma_f(x: u32)
                requires
                    x < 100,
                ensures
                    f2(x) == (x + 1),
            {}
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_auto_spec_missing_use  ["no-auto-import-verus_builtin"] => verus_code! {
        // fails if we don't say "use vstd::contrib::auto_spec;"
        #[auto_spec]
        fn foo(x: u32) -> u32 {
            x / 2
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot find attribute `auto_spec` in this scope")
}

test_verify_one_file! {
    #[test] test_auto_spec_unsupported_body verus_code! {
        use vstd::contrib::auto_spec;
        #[auto_spec]
        fn f(x: &mut u32, y: u32) -> u32
            requires
                *x < 100,
                y < 100,
        {
            *x = *x + y;
            *x
        }
    } => Err(e) => assert_vir_error_msg(e, "allow_in_spec not supported for function with &mut param")
}
