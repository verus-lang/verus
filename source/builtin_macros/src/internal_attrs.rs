//! rust_verify only accepts `#[verus::internal(...)]` attributes whose path
//! comes from a Verus macro expansion, so `mark` re-resolves the paths a macro
//! generates at `Span::call_site()`, keeping their location. Paths copied from
//! the macro's input are unchanged.

use proc_macro::TokenStream;

/// Tokens of the path `verus::internal`
#[cfg(verus_keep_ghost)]
const INTERNAL_PATH: [&str; 4] = ["verus", ":", ":", "internal"];

/// If `tts` starts with `verus::internal`, return the tokens of that path
#[cfg(verus_keep_ghost)]
fn internal_path(tts: &[proc_macro::TokenTree]) -> Option<&[proc_macro::TokenTree]> {
    let path = tts.get(..INTERNAL_PATH.len())?;
    path.iter().zip(INTERNAL_PATH).all(|(tt, s)| tt.to_string() == s).then_some(path)
}

/// The span used to recognize a path; the `internal` token's span is distinct per occurrence
#[cfg(verus_keep_ghost)]
fn path_key(path: &[proc_macro::TokenTree]) -> proc_macro::Span {
    path.last().unwrap().span()
}

#[cfg(verus_keep_ghost)]
fn input_spans(stream: TokenStream, spans: &mut Vec<proc_macro::Span>) {
    use proc_macro::TokenTree;
    let tts: Vec<TokenTree> = stream.into_iter().collect();
    for (i, tt) in tts.iter().enumerate() {
        if let TokenTree::Group(group) = tt {
            input_spans(group.stream(), spans);
        } else if let Some(path) = internal_path(&tts[i..]) {
            spans.push(path_key(path));
        }
    }
}

#[cfg(verus_keep_ghost)]
fn mark_generated(stream: TokenStream, input_spans: &[proc_macro::Span]) -> TokenStream {
    use proc_macro::{Group, Span, TokenTree};
    let mut tts: Vec<TokenTree> = stream.into_iter().collect();
    let mut i = 0;
    while i < tts.len() {
        if let TokenTree::Group(group) = &tts[i] {
            let mut new_group =
                Group::new(group.delimiter(), mark_generated(group.stream(), input_spans));
            new_group.set_span(group.span());
            tts[i] = TokenTree::Group(new_group);
            i += 1;
        } else if let Some(path) = internal_path(&tts[i..]) {
            let key = path_key(path);
            let path = &mut tts[i..i + INTERNAL_PATH.len()];
            if !input_spans.iter().any(|s| s.eq(&key)) {
                for tt in path {
                    tt.set_span(tt.span().resolved_at(Span::call_site()));
                }
            }
            i += INTERNAL_PATH.len();
        } else {
            i += 1;
        }
    }
    tts.into_iter().collect()
}

/// Mark the `verus::internal` paths in a macro's `output` that are not in its `inputs`
#[cfg(verus_keep_ghost)]
pub(crate) fn mark(inputs: &[TokenStream], output: TokenStream) -> TokenStream {
    let mut spans = Vec::new();
    for input in inputs {
        input_spans(input.clone(), &mut spans);
    }
    mark_generated(output, &spans)
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn mark(_inputs: &[TokenStream], output: TokenStream) -> TokenStream {
    output
}

/// `mark(&[input], f(input))`
pub(crate) fn mark_with(
    input: TokenStream,
    f: impl FnOnce(TokenStream) -> TokenStream,
) -> TokenStream {
    let output = f(input.clone());
    mark(&[input], output)
}
