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
mod atomic_ghost;
mod config;
mod contrib;
mod enum_synthesize;
mod exec_expand;
mod rustdoc;
mod source_erase;
mod struct_decl_inv;
mod syntax_trait;
mod topological_sort;
mod unerased_proxies;

use config::{EraseGhost, VstdKind};
pub use source_erase::{Erasure, ErasureKind};

// This entry point always requests ordinary Rust output, independently of the
// flags used to build the tool. Compiler cfg expansion requires a proc-macro
// context and cannot be consulted by an ordinary library.
fn cfg_erase() -> EraseGhost {
    EraseGhost::EraseAll
}

fn vstd_kind() -> VstdKind {
    VstdKind::Imported
}

pub use exec_expand::{erase_generated, expand_atomic, expand_struct};

/// Locate proof artifacts without expanding or reprinting executable code.
///
/// Spans refer to the original input, including tokens inside `verus!`.
/// Named return bindings are removed. Executable `Ghost`/`Tracked` types are
/// retained; constructors and supported patterns use the compiler's lowering.
pub fn source_erasures(source: &str) -> verus_syn::Result<Vec<Erasure>> {
    match syn::parse_file(source) {
        Ok(file) => syntax::source_erasure_rust(&file),
        // Also accept unwrapped Verus source.
        Err(_) => syntax::source_erasure(&mut verus_syn::parse_file(source)?),
    }
}
