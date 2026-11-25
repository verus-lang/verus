#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Code emitted by the Verus macros must not refer to items that the user's crate can shadow
// (https://github.com/verus-lang/verus/issues/3156)

test_verify_one_file_with_options! {
    #[test] global_layout_user_panic ["vstd", "--compile"] => code! {
        use vstd::prelude::*;

        macro_rules! panic {
            ($($t:tt)*) => { () };
        }

        verus! {

        #[repr(C)]
        struct S { v: u64, z: u64 }

        global layout S is size == 8, align == 8;

        } // verus!
    } => Err(err) => {
        assert_rust_error_msg(err.clone(), "evaluation panicked");
        assert!(err.errors[0].rendered.contains("does not have the expected size"));
    }
}

test_verify_one_file! {
    #[test] extern_crate_self_as_core code! {
        extern crate self as core;

        use vstd::prelude::*;

        #[macro_export]
        macro_rules! cfg {
            ($($t:tt)*) => { false };
        }

        verus! {

        proof fn bad()
            ensures false,
        {
        }

        } // verus!
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support renaming a crate to `core`")
}

test_verify_one_file_with_options! {
    #[test] extern_crate_self_as_core_is_core ["--is-core", "no-auto-import-verus_builtin"] => code! {
        #![cfg_attr(verus_keep_ghost, feature(fn_traits))]

        #[verifier::external]
        #[path="../../../../builtin/src/lib.rs"]
        mod verus_builtin;

        // At the crate root, this would make the builtin module's `core::` paths refer to this crate
        mod m {
            extern crate self as core;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] extern_crate_self_as_vstd_is_core ["--is-core", "no-auto-import-verus_builtin"] => code! {
        #![cfg_attr(verus_keep_ghost, feature(fn_traits))]

        extern crate self as vstd;

        #[verifier::external]
        #[path="../../../../builtin/src/lib.rs"]
        mod verus_builtin;
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support renaming a crate to `vstd`")
}

test_verify_one_file! {
    #[test] extern_crate_self_as_vstd code! {
        extern crate self as vstd;

        verus! {
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support renaming a crate to `vstd`")
}
