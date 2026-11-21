#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

#[test]
fn test_import_spec_impl_from_is_core() {
    let dir = tempfile::tempdir().unwrap();
    let builtin = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../builtin/src/lib.rs");
    let library = dir.path().join("embedded.rs");
    let consumer = dir.path().join("consumer.rs");
    let rlib = dir.path().join("libembedded.rlib");
    let vir = dir.path().join("embedded.vir");
    std::fs::write(
        &library,
        format!(
            "#![feature(fn_traits)]\n#[verifier::external]\n#[path = {:?}]\npub mod verus_builtin;\n{}",
            builtin.to_str().unwrap(),
            code_str! {
                use verus_builtin_macros::verus;
                verus! {
                    #[verifier::external]
                    pub trait T { fn f() -> bool; }

                    #[verifier::external]
                    impl T for u8 { fn f() -> bool { true } }

                    #[verifier::external_trait_specification]
                    #[verifier::external_trait_extension(TSpec via TSpecImpl)]
                    pub trait Ex {
                        type ExternalTraitSpecificationFor: T;
                        fn f() -> (r: bool) ensures r == Self::s();
                        spec fn s() -> bool;
                    }

                    // --is-core permits trusted specs without an assumption marker.
                    impl TSpecImpl for u8 { open spec fn s() -> bool { true } }
                }
            },
        ),
    )
    .unwrap();
    let run = run_verus_with_crate_args(
        &["--is-core", "--crate-name=embedded"],
        dir.path(),
        &library,
        true,
        false,
        &CrateArgs { deps: vec![], export: Some((rlib.clone(), vir.clone())) },
    );
    assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stderr));

    std::fs::write(
        &consumer,
        code_str! {
            use embedded::T;
            // Avoid macro paths into the real core: this test embeds builtin in a
            // regular library to exercise stdlib verification without rebuilding core.
            #[verus::internal(verus_macro)]
            fn test() -> bool { <u8 as T>::f() }
        },
    )
    .unwrap();
    let run = run_verus_with_crate_args(
        &["--is-stdlib-outside-of-core"],
        dir.path(),
        &consumer,
        true,
        false,
        &CrateArgs { deps: vec![("embedded".to_string(), rlib, vir)], export: None },
    );
    assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stderr));
}

test_verify_one_file_with_options! {
    #[test] test_is_core ["--is-core", "no-auto-import-verus_builtin"] => code! {
        #![allow(unused_parens)]
        #![allow(unused_imports)]
        #![allow(dead_code)]
        #![allow(unused_attributes)]
        #![allow(unused_variables)]

        #![cfg_attr(verus_keep_ghost, feature(atomic_internals))]
        #![cfg_attr(verus_keep_ghost, feature(generic_atomic))]
        #![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
        #![cfg_attr(verus_keep_ghost, feature(allocator_ext))]
        #![cfg_attr(verus_keep_ghost, feature(step_trait))]
        #![cfg_attr(verus_keep_ghost, feature(ptr_metadata))]

        #![cfg_attr(verus_keep_ghost, feature(derive_clone_copy_internals))]
        #![cfg_attr(verus_keep_ghost, feature(slice_index_methods))]
        #![cfg_attr(verus_keep_ghost, feature(freeze))]
        #![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]
        #![cfg_attr(verus_keep_ghost, feature(const_destruct))]
        #![cfg_attr(verus_keep_ghost, feature(derive_eq_internals))]
        #![cfg_attr(verus_keep_ghost, feature(nonzero_internals))]
        #![cfg_attr(verus_keep_ghost, feature(try_trait_v2_residual))]
        #![feature(hint_must_use)]
        #![cfg_attr(verus_keep_ghost, feature(fmt_internals))]
        #![cfg_attr(verus_keep_ghost, feature(fmt_arguments_from_str))]
        #![cfg_attr(verus_keep_ghost, feature(panic_internals))]
        #![cfg_attr(verus_keep_ghost, feature(maybe_uninit_array_assume_init))]
        #![cfg_attr(verus_keep_ghost, feature(trivial_clone))]
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

            broadcast use crate::vstd::slice::group_slice_axioms;

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
