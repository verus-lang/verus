use proc_macro::TokenStream;
use quote::quote;
use syn_verus::File;

#[proc_macro]
pub fn r#mod(input: TokenStream) -> TokenStream {
    let compile_error = syn_verus::parse::<File>(input)
        .map(|file| println!("{:#?}", file))
        .map_err(|err| err.to_compile_error())
        .err();

    TokenStream::from(quote! {
        #compile_error
        fn main() {}
    })
}
