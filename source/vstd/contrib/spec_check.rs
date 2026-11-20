//! Bridge between vstd and [verus-spec-check](https://github.com/verus-lang/verus-spec-check),
//! for vstd's own `cargo test --features spec-check`. See `source/vstd_spec_check/README.md`.
//!
//! With the `spec-check` feature, `verus!` hands each labeled item list in vstd to
//! [`vcheck_preprocess!`] instead of stripping the labels. In the unit-test build (the only
//! build with the verus-spec-check dev-dependencies) that is the engine's preprocessing pass;
//! everywhere else it hands the items straight back to `verus!`, which strips the labels.
//!
//! The generated harnesses refer to `::verus_spec_check_vstd_ext`, which a standalone
//! verus-spec-check project depends on. vstd can't, so `vstd_spec_check` points those paths
//! here, and this module provides the same items over vstd's own `contrib::exec_spec`.
//! Its `resource` module (harnesses over tracked permissions) is not provided yet.
#![allow(unused_imports)]

pub use super::exec_spec::*;

pub fn exec_mem_contents_from_option<T>(o: Option<T>) -> ExecMemContents<T> {
    match o {
        Some(t) => ExecMemContents::Init(t),
        None => ExecMemContents::Uninit,
    }
}

#[cfg(test)]
pub use vstd_spec_check::{
    vcheck_preprocess, verus_spec_check_unverified, verus_spec_check_verified,
};

/// Without the verus-spec-check dev-dependencies (any build but `cargo test`), labeled item
/// lists go straight back to `verus!`, which strips the labels.
#[cfg(not(test))]
macro_rules! vcheck_preprocess_without_engine {
    ($($items:tt)*) => {
        ::verus_builtin_macros::verus_spec_check_resume! { $($items)* }
    };
}

#[cfg(not(test))]
pub(crate) use vcheck_preprocess_without_engine as vcheck_preprocess;
