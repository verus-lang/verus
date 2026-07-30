//! Opt-in preprocessing hooks for `contrib`.
//!
//! This module is a *stable seam* that lets out-of-tree tooling observe and
//! rewrite the `verus_syn` item lists that flow through `contrib` before
//! `verus!` processes them. It exists such that projects layered on top of Verus
//! have a stable upstream source to patch into that persists over updates to
//! `verus_builtin_macros`.
//!
//! Everything is gated behind the `contrib-hooks` cargo feature, which is
//! **off by default**.
//!
//! Note: a downstream project still ships a full `[patch.crates-io]` copy of this
//! crate - whole-crate substitution is the only way to give it a dependency
//! on the provider's code. The seam just makes that copy a verbatim mirror of
//! upstream (synced by a file copy) instead of a hand-patched fork.
//!
//! # Enabling hooks
//!
//! Build `verus_builtin_macros` (or a fork/patch of it) with
//! `--features contrib-hooks` and point the `VERUS_CONTRIB_HOOKS_FILE`
//! environment variable at an absolute path to a Rust source file (the
//! "provider"). That file is `include!`d into the private `external` module
//! below and is compiled as part of this crate, so it has access to
//! `verus_syn` and to any dependency the surrounding crate declares. The
//! provider must define two functions:
//!
//! ```ignore
//! pub(super) fn preprocess_items(items: &mut Vec<verus_syn::Item>) { /* ... */ }
//! pub(super) fn preprocess_impl_items(items: &mut Vec<verus_syn::ImplItem>) { /* ... */ }
//! ```
//!
//! A provider is free to fan out to any number of independent hooks, so this
//! seam is not tied to any particular downstream or feature.
//!
//! # Example
//!
//! Setting up hooks requires configuring both the provider, and the end-user
//! downstream project.
//!
//! First, the provider crate must specify the location of the hooks in its `build.rs`:
//!
//! ```ignore
//! // build.rs
//! fn main() {
//!     let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("hooks_provider.rs");
//!     println!("cargo:rustc-env=VERUS_CONTRIB_HOOKS_FILE={}", p.display());
//!     println!("cargo:rerun-if-changed=hooks_provider.rs");
//! }
//! ```
//!
//! `hooks_provider.rs` lists the hooks (one env var, one file, N hooks):
//!
//! ```ignore
//! const ITEM_HOOKS: &[fn(&mut Vec<Item>)] = &[pbt::run, trace::run];
//!
//! pub(super) fn preprocess_items(items: &mut Vec<Item>) {
//!     for h in ITEM_HOOKS { h(items); }
//! }
//! pub(super) fn preprocess_impl_items(_items: &mut Vec<ImplItem>) {}
//!
//! mod pbt   { use super::Item; pub fn run(items: &mut Vec<Item>) { some_engine::fold(items); } }
//! mod trace { use super::Item; pub fn run(_items: &mut Vec<Item>) { /* ... */ } }
//! ```
//!
//! Then, the end-user project opts in per-project (the feature is off by default in
//! upstream Verus) and patches the source:
//!
//! ```toml
//! [dependencies]
//! verus_builtin_macros = { version = "=<ver>", features = ["contrib-hooks"] }
//!
//! [patch.crates-io]
//! verus_builtin_macros = { git = "...", tag = "..." }
//! ```

use verus_syn::{ImplItem, Item};

/// A hook that runs over the full list of top-level items.
pub type ItemsHook = fn(&mut Vec<Item>);

/// A hook that runs over the full list of impl items.
pub type ImplItemsHook = fn(&mut Vec<ImplItem>);

/// Registry of hooks over top-level item lists.
///
/// This is a slice so that multiple independent hooks can be registered; add
/// entries here to extend preprocessing.
#[cfg(feature = "contrib-hooks")]
const ITEMS_HOOKS: &[ItemsHook] = &[external::preprocess_items];
#[cfg(not(feature = "contrib-hooks"))]
const ITEMS_HOOKS: &[ItemsHook] = &[];

/// Registry of hooks over impl item lists.
#[cfg(feature = "contrib-hooks")]
const IMPL_ITEMS_HOOKS: &[ImplItemsHook] = &[external::preprocess_impl_items];
#[cfg(not(feature = "contrib-hooks"))]
const IMPL_ITEMS_HOOKS: &[ImplItemsHook] = &[];

/// Run every registered top-level item hook, in registration order.
///
/// Called at the start of `contrib::contrib_preprocess_items`. With no
/// hooks registered (the default) this is an empty loop and compiles away.
pub(crate) fn preprocess_items(items: &mut Vec<Item>) {
    for hook in ITEMS_HOOKS {
        hook(items);
    }
}

/// Run every registered impl-item hook, in registration order.
///
/// Called at the start of `contrib::contrib_preprocess_impl_items`. With no
/// hooks registered (the default) this is an empty loop and compiles away.
pub(crate) fn preprocess_impl_items(items: &mut Vec<ImplItem>) {
    for hook in IMPL_ITEMS_HOOKS {
        hook(items);
    }
}

// The external provider is only compiled when the feature is enabled. Its
// path is resolved at compile time from `VERUS_CONTRIB_HOOKS_FILE`; if the
// feature is on but the variable is unset, compilation fails with the
// message below rather than silently doing nothing.
#[cfg(feature = "contrib-hooks")]
mod external {
    #[allow(unused_imports)]
    use verus_syn::{ImplItem, Item};

    include!(env!(
        "VERUS_CONTRIB_HOOKS_FILE",
        "the `contrib-hooks` feature is enabled, but the \
         VERUS_CONTRIB_HOOKS_FILE environment variable (an absolute path to \
         the contrib hooks provider `.rs` file) is not set"
    ));
}
