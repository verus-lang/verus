use proc_macro2::TokenStream;

pub(crate) fn expand(input: TokenStream, concurrent: bool) -> verus_syn::Result<TokenStream> {
    let parsed = verus_syn::parse2::<crate::parse_token_stream::ParseResult>(input)?;
    let smir = crate::parse_token_stream::parse_result_to_smir(parsed, concurrent)?;
    crate::lemmas::check_lemmas(&smir)?;
    crate::to_token_stream::output_token_stream(smir, concurrent)
}
