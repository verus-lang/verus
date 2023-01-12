#![feature(box_patterns)]
#![feature(proc_macro_span)]
#![feature(proc_macro_tracked_env)]

use synstructure::{decl_attribute, decl_derive};
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
pub fn verus(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, true)
}

#[proc_macro]
pub fn verus_old_todo_replace_this(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, false)
}

#[proc_macro]
pub fn verus_proof_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(true, input)
}

#[proc_macro]
pub fn verus_exec_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(false, input)
}

/// verus_proof_macro_exprs!(f!(exprs)) applies verus syntax to transform exprs into exprs',
/// then returns f!(exprs'),
/// where exprs is a sequence of expressions separated by ",", ";", and/or "=>".
#[proc_macro]
pub fn verus_proof_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(true, input)
}

#[proc_macro]
pub fn verus_exec_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(false, input)
}

#[proc_macro]
pub fn struct_with_invariants(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    struct_decl_inv::struct_decl_inv(input)
}
