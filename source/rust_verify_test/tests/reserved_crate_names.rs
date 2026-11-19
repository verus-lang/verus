#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// A user crate named `alloc`, `core`, or `vstd` must not be treated
// as the actual alloc/core/vstd crate (https://github.com/verus-lang/verus/issues/3212)

const ALLOC_VEC_LEN_COLLISION: &str = code_str! {
    #![feature(allocator_api)]
    use vstd::prelude::*;
    pub mod vec {
        use std::alloc::Allocator;
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNT: AtomicUsize = AtomicUsize::new(0);
        pub trait Tr { fn len(&self) -> usize; }
        impl Tr for u8 { fn len(&self) -> usize { 0 } }
        // Same VIR path (vec::impl&%1::len) as std's Vec::len in alloc
        impl<T, A: Allocator> Tr for std::vec::Vec<T, A> {
            fn len(&self) -> usize { COUNT.fetch_add(1, Ordering::SeqCst) }
        }
    }
    use vec::Tr;
    verus! {
    fn two(v: &std::vec::Vec<u8>) -> (r: (usize, usize))
        ensures r.0 == r.1,
    {
        let a = Tr::len(v);
        let b = Tr::len(v);
        (a, b)
    }
    }
};

test_verify_one_file_with_options! {
    #[test] test_crate_named_alloc_no_vstd_specs ["--crate-name=alloc", "no-auto-import-verus_builtin"] =>
        FEATURE_PRELUDE.to_string() + ALLOC_VEC_LEN_COLLISION
    => Err(err) => assert_vir_error_msg(err, "cannot use function `alloc::vec::Vec::len` which is ignored")
}

test_verify_one_file_with_options! {
    #[test] test_crate_named_vstd_no_cheating ["--crate-name=vstd", "--no-cheating"] => verus_code! {
        pub trait Area {
            fn bogus(&self) -> (r: u8)
                ensures r == 7 && r == 8;
        }
        pub struct W(pub u8);
        impl Area for W {
            #[verifier::external_body]
            fn bogus(&self) -> (r: u8)
                ensures r == 7 && r == 8,
            { 0 }
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_body`/`assume_specification` not allowed with `--no-cheating`")
}

// A crate cannot claim to be core/alloc/vstd by redefining the items used to identify them;
// rustc rejects duplicate lang items and duplicate diagnostic items.

test_verify_one_file_with_options! {
    #[test] test_crate_named_core_cannot_redefine_sized_lang_item
        ["--crate-name=core", "no-auto-import-verus_builtin"] =>
        FEATURE_PRELUDE.to_string() + code_str! {
            #![feature(lang_items)]
            use vstd::prelude::*;
            #[lang = "sized"]
            pub trait MySized {}
        }
    => Err(err) => assert_rust_error_msg(err, "found duplicate lang item `sized`")
}

test_verify_one_file_with_options! {
    #[test] test_crate_named_alloc_cannot_redefine_owned_box_lang_item
        ["--crate-name=alloc", "no-auto-import-verus_builtin"] =>
        FEATURE_PRELUDE.to_string() + code_str! {
            #![feature(lang_items)]
            use vstd::prelude::*;
            #[lang = "owned_box"]
            pub struct MyBox<T: ?Sized>(*mut T);
        }
    => Err(err) => assert_rust_error_msg(err, "found duplicate lang item `owned_box`")
}

// -Cmetadata makes the crate distinguishable from the real vstd, avoiding an earlier E0519
// error, so that this test exercises the duplicate diagnostic item check
test_verify_one_file_with_options! {
    #[test] test_crate_named_vstd_cannot_redefine_vstd_diagnostic_item
        ["--crate-name=vstd", "-Cmetadata=not_vstd", "--no-cheating", "no-auto-import-verus_builtin"] =>
        FEATURE_PRELUDE.to_string() + code_str! {
            #![feature(rustc_attrs)]
            use vstd::prelude::*;
            #[rustc_diagnostic_item = "verus::vstd::invariant::open_invariant_end"]
            pub fn fake() {}
        }
    => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains(
            "duplicate diagnostic item in crate `vstd`: `verus::vstd::invariant::open_invariant_end`"
        ));
    }
}

test_verify_one_file_with_options! {
    #[test] test_crate_named_alloc_rc_not_treated_as_std_rc ["--crate-name=alloc"] => verus_code! {
        // Has the same path as alloc::rc::Rc, but should not be treated as std's Rc
        pub mod rc {
            pub struct Rc<T>(pub T);
        }
        fn f(x: rc::Rc<u8>) -> (r: u8)
            ensures r == x.0,
        {
            x.0
        }
    } => Ok(())
}

// Defining lang items is not allowed outside of the standard library.
// (Use no_std so that the real alloc crate isn't present, and there is no duplicate lang item.)
test_verify_one_file_with_options! {
    #[test] test_no_std_crate_named_alloc_cannot_define_owned_box_lang_item
        ["--crate-name=alloc", "no-auto-import-verus_builtin"] =>
        code! {
            #![no_std]
            #![feature(lang_items)]
            use verus_builtin::*;
            use verus_builtin_macros::*;
            pub mod boxed {
                #[lang = "owned_box"]
                pub struct Box<T: ?Sized>(*mut T);
            }
            verus! {
                fn f() {}
            }
        }
    => Err(err) => assert_vir_error_msg(err, "Verus does not support defining lang items (found `owned_box`)")
}
