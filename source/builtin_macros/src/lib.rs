use quote::quote;
use synstructure::decl_derive;

decl_derive!([Structural] => derive_structural);

fn derive_structural(s: synstructure::Structure) -> proc_macro2::TokenStream {
    s.gen_impl(quote! {
        gen impl ::builtin::Structural for @Self { }
    })
}
