//! The same syntax visitor used by `verus_builtin_macros`, compiled without a
//! proc-macro entry point so tools can use it on source files.
#![allow(dead_code)]
#![cfg_attr(
    verus_keep_ghost,
    feature(proc_macro_tracked_env, proc_macro_expand, proc_macro_diagnostic)
)]

extern crate proc_macro;

#[macro_use]
mod syntax;
mod config;
mod contrib;
mod enum_synthesize;
mod rustdoc;
mod source_erase;
mod syntax_trait;
mod unerased_proxies;

use config::{EraseGhost, VstdKind, cfg_erase, vstd_kind};
pub use source_erase::{Erasure, ErasureKind};

/// Locate proof artifacts without expanding or reprinting executable code.
///
/// Spans refer to the original input, including tokens inside `verus!`.
/// Named returns and executable `Ghost`/`Tracked` types and values are retained.
pub fn source_erasures(source: &str) -> verus_syn::Result<Vec<Erasure>> {
    match syn::parse_file(source) {
        Ok(file) => syntax::source_erasure_rust(&file),
        // Also accept unwrapped Verus source (in particular named returns in
        // previously generated snapshots) so stripping remains idempotent.
        Err(_) => syntax::source_erasure(&mut verus_syn::parse_file(source)?),
    }
}
