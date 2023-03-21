#![feature(box_patterns)]
#![feature(proc_macro_span)]
#![feature(proc_macro_tracked_env)]
#![feature(proc_macro_quote)]
#![feature(proc_macro_expand)]

use synstructure::{decl_attribute, decl_derive};
mod atomic_ghost;
mod fndecl;
mod is_variant;
mod rustdoc;
mod struct_decl_inv;
mod structural;
mod syntax;
mod topological_sort;

decl_derive!([Structural] => structural::derive_structural);

decl_attribute!([is_variant] => is_variant::attribute_is_variant);

// Proc macros must reside at the root of the crate
#[proc_macro]
pub fn fndecl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::from(fndecl::fndecl(proc_macro2::TokenStream::from(input)))
}

#[proc_macro]
pub fn verus_keep_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, false, true, true)
}

#[proc_macro]
pub fn verus_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, true, true, true)
}

#[proc_macro]
pub fn verus(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, cfg_erase(), true, true)
}

#[proc_macro]
pub fn verus_old_todo_no_ghost_blocks(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, false, true, false)
}

#[proc_macro]
pub fn verus_proof_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(false, true, input)
}

#[proc_macro]
pub fn verus_exec_expr_keep_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(false, false, input)
}

#[proc_macro]
pub fn verus_exec_expr_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(true, false, input)
}

#[proc_macro]
pub fn verus_exec_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(cfg_erase(), false, input)
}

pub(crate) fn cfg_erase() -> bool {
    let ts: proc_macro::TokenStream =
        quote::quote! { ::core::cfg!(verus_macro_erase_ghost) }.into();
    let bool_ts = ts.expand_expr();
    let bool_ts = match bool_ts {
        Ok(name) => name,
        Err(_) => {
            panic!("cfg_erase call failed");
        }
    };
    let bool_ts = bool_ts.to_string();
    assert!(bool_ts == "true" || bool_ts == "false");
    bool_ts == "true"
}

/// verus_proof_macro_exprs!(f!(exprs)) applies verus syntax to transform exprs into exprs',
/// then returns f!(exprs'),
/// where exprs is a sequence of expressions separated by ",", ";", and/or "=>".
#[proc_macro]
pub fn verus_proof_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(false, true, input)
}

#[proc_macro]
pub fn verus_exec_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(cfg_erase(), false, input)
}

#[proc_macro]
pub fn verus_inv_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Reads the first expression as proof; the second as exec
    syntax::inv_macro_exprs(cfg_erase(), input)
}

/// `verus_proof_macro_explicit_exprs!(f!(tts))` applies verus syntax to transform `tts` into
/// `tts'`, then returns `f!(tts')`, only applying the transform to any of the exprs within it that
/// are explicitly prefixed with `@@`, leaving the rest as-is. Contrast this to
/// [`verus_proof_macro_exprs`] which is likely what you want to try first to see if it satisfies
/// your needs.
#[proc_macro]
pub fn verus_proof_macro_explicit_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_explicit_exprs(false, true, input)
}

#[proc_macro]
pub fn struct_with_invariants(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    struct_decl_inv::struct_decl_inv(input)
}

#[proc_macro]
pub fn atomic_with_ghost_helper(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    atomic_ghost::atomic_ghost(input)
}
