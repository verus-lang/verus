use synstructure::{decl_attribute, decl_derive};
mod fndef;
mod is_variant;
mod structural;

decl_derive!([Structural] => structural::derive_structural);

decl_attribute!([is_variant] => is_variant::attribute_is_variant);

// Proc macros must reside at the root of the crate
#[proc_macro]
pub fn fndef(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::from(fndef::fndef(proc_macro2::TokenStream::from(input)))
}
