#![feature(box_patterns)]
#![feature(proc_macro_span)]
#![feature(proc_macro_tracked_env)]
#![feature(proc_macro_quote)]

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
    syntax::rewrite_items(input, false, true, true, false)
}

#[proc_macro]
pub fn verus_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, true, true, true, false)
}

#[proc_macro]
pub fn verus_keep_ghost_old(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, false, true, true, true)
}

#[proc_macro]
pub fn verus_erase_ghost_old(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, true, true, true, true)
}

#[proc_macro]
pub fn verus(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::quote! {
        #[cfg(all(not(verus_macro_erase_ghost), vstd_todo))]
        verus_keep_ghost! { $input }
        #[cfg(all(verus_macro_erase_ghost, vstd_todo))]
        verus_erase_ghost! { $input }
        #[cfg(all(not(verus_macro_erase_ghost), not(vstd_todo)))]
        verus_keep_ghost_old! { $input }
        #[cfg(all(verus_macro_erase_ghost, not(vstd_todo)))]
        verus_erase_ghost_old! { $input }
    }
}

#[proc_macro]
pub fn verus_old_todo_replace_this(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, false, false, true, true)
}

#[proc_macro]
pub fn verus_old_todo_no_ghost_blocks(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, false, true, false, true)
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
    // To implement this, we use let-expressions because Rust doesn't allow us
    // to erase expressions using cfg-attributes.

    // hygeine: We bind the variable _tmp, immediately use it, then it goes out of scope.
    // Therefore the name can't interfere with anything else.

    proc_macro::quote! {
      {
        #[cfg(not(verus_macro_erase_ghost))]
        let _tmp = verus_exec_expr_keep_ghost!($input);

        #[cfg(verus_macro_erase_ghost)]
        let _tmp = verus_exec_expr_erase_ghost!($input);

        _tmp
      }
    }
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
    syntax::proof_macro_exprs(false, false, input)
}

#[proc_macro]
pub fn struct_with_invariants(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    struct_decl_inv::struct_decl_inv(input)
}

#[proc_macro]
pub fn atomic_with_ghost_helper(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    atomic_ghost::atomic_ghost(input)
}
