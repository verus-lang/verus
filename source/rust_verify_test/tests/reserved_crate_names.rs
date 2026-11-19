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
