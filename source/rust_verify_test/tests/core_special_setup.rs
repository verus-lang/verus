#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_is_core ["--is-core", "no-auto-import-verus_builtin"] => code! {
        #![allow(unused_parens)]
        #![allow(unused_imports)]
        #![allow(dead_code)]
        #![allow(unused_attributes)]
        #![allow(unused_variables)]

        #![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
        #![cfg_attr(verus_keep_ghost, feature(allocator_api))]
        #![cfg_attr(verus_keep_ghost, feature(step_trait))]
        #![cfg_attr(verus_keep_ghost, feature(ptr_metadata))]
        #![cfg_attr(verus_keep_ghost, feature(strict_provenance_atomic_ptr))]
        #![cfg_attr(verus_keep_ghost, feature(derive_clone_copy))]
        #![cfg_attr(verus_keep_ghost, feature(freeze))]
        #![cfg_attr(
            verus_keep_ghost,
            feature(fn_traits),
        )]
        #![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]

        #[verifier::external]
        #[path="../../../../builtin/src/lib.rs"]
        mod verus_builtin;

        #[path="../../../../vstd/vstd.rs"]
        mod vstd;

        mod test {
            use crate::vstd::set::*;
            use crate::vstd::seq::*;
            use crate::vstd::multiset::*;
            use crate::vstd::prelude::*;

            verus!{

            proof fn test_seqs(a: Seq<int>, b: Seq<int>)
                requires a == b,
            {
                crate::vstd::seq_lib::assert_seqs_equal!(a, b);
                crate::vstd::seq_lib::assert_seqs_equal!(a == b);
            }

            proof fn test_sets(a: Set<int>, b: Set<int>)
                requires a == b,
            {
                crate::vstd::set_lib::assert_sets_equal!(a, b);
                crate::vstd::set_lib::assert_sets_equal!(a == b);
            }

            proof fn test_multisets(a: Multiset<int>, b: Multiset<int>)
                requires a == b,
            {
                crate::vstd::multiset::assert_multisets_equal!(a, b);
                crate::vstd::multiset::assert_multisets_equal!(a == b);
            }

            fn test_slice_index(x: &[u8]) -> u8
                requires x@.len() > 0
            {
                x[0]
            }

            fn test_ptr_stuff(a: *mut u8, b: *mut [u8; 2]) {
                let t = a as *mut u16;
                let s = b as *mut [u8];
            }

            }
        }

        fn main() { }
    } => Ok(())
}
