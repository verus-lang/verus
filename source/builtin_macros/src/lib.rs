#![cfg_attr(
    verus_keep_ghost,
    feature(proc_macro_span),
    feature(proc_macro_tracked_env),
    feature(proc_macro_quote),
    feature(proc_macro_expand),
    feature(proc_macro_diagnostic)
)]

use std::sync::OnceLock;
use synstructure::{decl_attribute, decl_derive};

#[macro_use]
mod syntax;
mod atomic_ghost;
mod attr_block_trait;
mod attr_rewrite;
mod calc_macro;
mod contrib;
mod enum_synthesize;
mod fndecl;
mod is_variant;
mod rustdoc;
mod struct_decl_inv;
mod structural;
mod syntax_trait;
mod topological_sort;
mod unerased_proxies;

decl_derive!([Structural] => structural::derive_structural);
decl_derive!([StructuralEq] => structural::derive_structural_eq);

decl_attribute! {
    [is_variant] =>
    /// Add `is_<VARIANT>` and `get_<VARIANT>` functions to an enum
    is_variant::attribute_is_variant
}
decl_attribute! {
    [is_variant_no_deprecation_warning] =>
    /// Add `is_<VARIANT>` and `get_<VARIANT>` functions to an enum
    is_variant::attribute_is_variant_no_deprecation_warning
}

#[proc_macro_attribute]
pub fn verus_enum_synthesize(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    enum_synthesize::attribute_verus_enum_synthesize(&cfg_erase(), attr, input)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EraseGhost {
    /// keep all ghost code
    Keep,
    /// erase ghost code, but leave ghost stubs
    Erase,
    /// erase all ghost code
    EraseAll,
}

impl EraseGhost {
    fn keep(&self) -> bool {
        match self {
            EraseGhost::Keep => true,
            EraseGhost::Erase | EraseGhost::EraseAll => false,
        }
    }

    fn erase(&self) -> bool {
        match self {
            EraseGhost::Keep => false,
            EraseGhost::Erase | EraseGhost::EraseAll => true,
        }
    }

    fn erase_all(&self) -> bool {
        match self {
            EraseGhost::Keep | EraseGhost::Erase => false,
            EraseGhost::EraseAll => true,
        }
    }
}

// Proc macros must reside at the root of the crate
#[proc_macro]
pub fn fndecl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::from(fndecl::fndecl(proc_macro2::TokenStream::from(input)))
}

#[proc_macro]
pub fn verus_keep_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, EraseGhost::Keep, true)
}

#[proc_macro]
pub fn verus_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, EraseGhost::Erase, true)
}

#[proc_macro]
pub fn verus(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, cfg_erase(), true)
}

/// Like verus!, but for use inside a (non-trait) impl
#[proc_macro]
pub fn verus_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_impl_items(input, cfg_erase(), true, false)
}

/// Like verus!, but for use inside a trait impl
#[proc_macro]
pub fn verus_trait_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_impl_items(input, cfg_erase(), true, true)
}

#[proc_macro]
pub fn verus_proof_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(EraseGhost::Keep, true, input)
}

#[proc_macro]
pub fn verus_exec_expr_keep_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(EraseGhost::Keep, false, input)
}

#[proc_macro]
pub fn verus_exec_expr_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(EraseGhost::Keep, false, input)
}

#[proc_macro]
pub fn verus_exec_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(cfg_erase(), false, input)
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_erase() -> EraseGhost {
    let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_keep_ghost_body) }.into();
    let ts_stubs: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_keep_ghost) }.into();
    let (bool_ts, bool_ts_stubs) = match (ts.expand_expr(), ts_stubs.expand_expr()) {
        (Ok(name), Ok(name_stubs)) => (name.to_string(), name_stubs.to_string()),
        _ => {
            panic!("cfg_erase call failed")
        }
    };
    match (bool_ts.as_str(), bool_ts_stubs.as_str()) {
        ("true", "true" | "false") => EraseGhost::Keep,
        ("false", "true") => EraseGhost::Erase,
        ("false", "false") => EraseGhost::EraseAll,
        _ => {
            panic!("cfg_erase call failed")
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_erase() -> EraseGhost {
    EraseGhost::EraseAll
}

#[derive(Clone, Copy)]
enum VstdKind {
    /// The current crate is vstd.
    IsVstd,
    /// There is no vstd (only verus_builtin). Really only used for testing.
    NoVstd,
    /// Imports the vstd crate like usual.
    Imported,
    /// Embed vstd and verus_builtin as modules, necessary for verifying the `core` library.
    IsCore,
    /// For other crates in stdlib verification that import core
    ImportedViaCore,
}

fn vstd_kind() -> VstdKind {
    static VSTD_KIND: OnceLock<VstdKind> = OnceLock::new();
    *VSTD_KIND.get_or_init(|| {
        match std::env::var("VSTD_KIND") {
            Ok(s) => {
                if &s == "IsVstd" {
                    return VstdKind::IsVstd;
                } else if &s == "NoVstd" {
                    return VstdKind::NoVstd;
                } else if &s == "Imported" {
                    return VstdKind::Imported;
                } else if &s == "IsCore" {
                    return VstdKind::IsCore;
                } else if &s == "ImportsCore" {
                    return VstdKind::ImportedViaCore;
                } else {
                    panic!("The environment variable VSTD_KIND was set but its value is invalid. Allowed values are 'IsVstd', 'NoVstd', 'Imported', 'IsCore', and 'ImportsCore'");
                }
            }
            _ => { }
        }

        // When building vstd normally through cargo, we won't get a VSTD_KIND env var,
        // but we can use CARGO_PGK_NAME instead.
        let is_vstd = std::env::var("CARGO_PKG_NAME").map_or(false, |s| s == "vstd");
        if is_vstd {
            return VstdKind::IsVstd;
        }

        // For tests, which don't go through the verus binary, we infer the mode from
        // these cfg options
        if cfg_verify_core() {
            return VstdKind::IsCore;
        }
        if cfg_no_vstd() {
            return VstdKind::NoVstd;
        }

        // If none of the above, we assume a normal build
        return VstdKind::Imported;
    })
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_verify_core() -> bool {
    static CFG_VERIFY_CORE: OnceLock<bool> = OnceLock::new();
    *CFG_VERIFY_CORE.get_or_init(|| {
        let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_verify_core) }.into();
        let bool_ts = match ts.expand_expr() {
            Ok(name) => name.to_string(),
            _ => {
                panic!("cfg_verify_core call failed")
            }
        };
        match bool_ts.as_str() {
            "true" => true,
            "false" => false,
            _ => {
                panic!("cfg_verify_core call failed")
            }
        }
    })
}

// Because 'expand_expr' is unstable, we need a different impl when `not(verus_keep_ghost)`.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_verify_core() -> bool {
    false
}

#[cfg(verus_keep_ghost)]
fn cfg_no_vstd() -> bool {
    static CFG_VERIFY_CORE: OnceLock<bool> = OnceLock::new();
    *CFG_VERIFY_CORE.get_or_init(|| {
        let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_no_vstd) }.into();
        let bool_ts = match ts.expand_expr() {
            Ok(name) => name.to_string(),
            _ => {
                panic!("cfg_no_vstd call failed")
            }
        };
        match bool_ts.as_str() {
            "true" => true,
            "false" => false,
            _ => {
                panic!("cfg_no_vstd call failed")
            }
        }
    })
}

// Because 'expand_expr' is unstable, we need a different impl when `not(verus_keep_ghost)`.
#[cfg(not(verus_keep_ghost))]
fn cfg_no_vstd() -> bool {
    false
}

/// verus_proof_macro_exprs!(f!(exprs)) applies verus syntax to transform exprs into exprs',
/// then returns f!(exprs'),
/// where exprs is a sequence of expressions separated by ",", ";", and/or "=>".
#[proc_macro]
pub fn verus_proof_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(EraseGhost::Keep, true, input)
}

#[proc_macro]
pub fn verus_exec_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(cfg_erase(), false, input)
}

// This is for expanding the body of an open_*_invariant in exec mode
#[proc_macro]
pub fn verus_exec_inv_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // We pass `treat_elements_as_ghost: false` to treat all elements besides
    // the third ($eexpr) as ghost.
    syntax::inv_macro_exprs(cfg_erase(), false, input)
}

// This is for expanding the body of an open_*_invariant in `proof` mode
#[proc_macro]
pub fn verus_ghost_inv_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // We pass `treat_elements_as_ghost: true` to treat all elements as ghost.
    syntax::inv_macro_exprs(cfg_erase(), true, input)
}

/// `verus_proof_macro_explicit_exprs!(f!(tts))` applies verus syntax to transform `tts` into
/// `tts'`, then returns `f!(tts')`, only applying the transform to any of the exprs within it that
/// are explicitly prefixed with `@@`, leaving the rest as-is. Contrast this to
/// [`verus_proof_macro_exprs`] which is likely what you want to try first to see if it satisfies
/// your needs.
#[proc_macro]
pub fn verus_proof_macro_explicit_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_explicit_exprs(EraseGhost::Keep, true, input)
}

#[proc_macro]
pub fn struct_with_invariants(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    struct_decl_inv::struct_decl_inv(input)
}

#[proc_macro]
pub fn atomic_with_ghost_helper(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    atomic_ghost::atomic_ghost(input)
}

#[proc_macro]
pub fn calc_proc_macro(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    calc_macro::calc_macro(input)
}

/*** Verus small macro definition for executable items ***/

// If no #[verus_verify] on the item, it is verifier::external by default.
// When compiling code with verus:
// #[verus_verify] annotates the item with verifier::verify
// #[verus_verify(external_body)] annotates the item with verifier::external_body
// When compiling code with standard rust tool, the item has no verifier annotation.
#[proc_macro_attribute]
pub fn verus_verify(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    attr_rewrite::rewrite_verus_attribute(&cfg_erase(), args, input)
}

#[proc_macro_attribute]
pub fn verus_spec(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    attr_rewrite::rewrite_verus_spec(cfg_erase(), attr.into(), input.into()).into()
}

/// proof_with add ghost input/output to the next function call.
/// In stable rust, we cannot add attribute-based macro to expr/statement.
/// Using proof_with! to tell #[verus_spec] to add ghost input/output.
/// Using proof_with outside of #[verus_spec] does not have any side effects.
#[proc_macro]
pub fn proof_with(_: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::new()
}

/// Add a verus proof block.
#[proc_macro]
pub fn proof(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    attr_rewrite::proof_rewrite(cfg_erase(), input.into()).into()
}

/// proof_decl add extra stmts that are used only
/// for verification.
/// For example, declare a ghost/tracked variable.
/// To avoid confusion, let stmts without ghost/tracked is not supported.
/// Non-local stmts inside proof_decl! are treated similar to those in proof!
#[proc_macro]
pub fn proof_decl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let erase = cfg_erase();
    if erase.keep() {
        syntax::rewrite_proof_decl(erase, input.into())
    } else {
        proc_macro::TokenStream::new()
    }
}

/*** End of verus small macro definition for executable items ***/

/*** Start of contrib proc macros
(unfortunately, proc macros must reside at the root of the crate)

To add a contrib proc macro, complete the following steps:
- Add a file in builtin_macros/src/contrib/ that contains the bulk of the macro implementation
  (example: builtin_macros/src/contrib/auto_spec.rs)
- Declare the file as a submodule of builtin_macros::contrib by adding "pub mod ..." to the top of
  builtin_macros/src/contrib/mod.rs (example: `pub mod auto_spec;`)
- Add a short macro declaration below, calling into your file in builtin_macros/src/contrib
  for any complex work (i.e. the macro declaration below should have a body of at most a few lines)
- Add a "pub use" to vstd/contrib/mod.rs (example: `pub use verus_builtin_macros::auto_spec;`)

If your macro needs to manipulate function signatures or function bodies,
it's generally cleaner to write this manipulation on the verus_syn representation of the function
before it is transformed by `verus!`, rather than trying to manipulate the more complicated output
of `verus!`.  To work with the verus_syn representation, complete this additional step:
- In builtin_macros/src/contrib/mod.rs,
  edit contrib_preprocess_item and/or contrib_preprocess_impl_item to match on your macro name and
  call into your code that processes the verus_syn item or impl_item.  Example:
  `"auto_spec" => auto_spec::auto_spec_item(item, tokens, new_items),`.
  Your code can then edit the item/impl_item in place.
  It can also optionally emit new items/impl_items by adding them to new_items.
***/

/// This copies the body of an exec function into a "returns" clause,
/// so that the exec function will be also usable as a spec function.
/// For example,
///   `#[vstd::contrib::auto_spec] fn f(u: u8) -> u8 { u / 2 }`
/// becomes:
///   `#[verifier::allow_in_spec] fn f(u: u8) -> u8 returns (u / 2) { u / 2 }`
/// The macro performs some limited fixups, such as removing proof blocks
/// and turning +, -, and * into add, sub, mul.
/// However, only a few such fixups are currently implemented and not all exec bodies
/// will be usable as return clauses, so this macro will not work on all exec functions.
#[proc_macro_attribute]
pub fn auto_spec(
    _args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    // All the work is done in the preprocesssing; this just double-checks name resolution
    input
}

/*** End of contrib macros ***/
