//! Runs the [Verus SpecCheck](https://github.com/verus-lang/verus-spec-check) engine over the
//! labeled items in vstd, for vstd's own `cargo test --features spec-check`
//!
//! A verus-spec-check project gets the engine by patching in a fork of
//! `verus_builtin_macros`. vstd can't do that, since it uses the in-tree macros crate, and the
//! in-tree macros crate can't depend on the engine without pulling it into every Verus build.
//! So with its `spec-check` feature, `verus!` hands each labeled item list in vstd to
//! [`vcheck_preprocess!`] (reached through `vstd::contrib::spec_check`) instead.
//!
//! The engine writes the paths a standalone verus-spec-check project would use. vstd can't
//! depend on `verus_spec_check_vstd_ext` (it depends on vstd), so this crate points those
//! paths into vstd itself:
//!
//! - `::verus_spec_check_vstd_ext` becomes `crate::contrib::spec_check`, which provides the
//!   same items over vstd's own `contrib::exec_spec`;
//! - the engine's macros `::verus_spec_check::verus_spec_check_{un,}verified` become this
//!   crate's [`verus_spec_check_unverified!`] / [`verus_spec_check_verified!`], again
//!   through `crate::contrib::spec_check`;
//! - everything else under `::verus_spec_check` is the verus-spec-check runtime crate, which
//!   vstd depends on under that name

use proc_macro2::{Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use quote::quote;
use verus_syn::parse::{Parse, ParseStream};

struct Items(Vec<verus_syn::Item>);

impl Parse for Items {
    fn parse(input: ParseStream) -> verus_syn::Result<Self> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(Items(items))
    }
}

/// Runs the engine's preprocessing pass (which folds `#[vcheck]`-labeled items into
/// `verus_spec_check_unverified!` blocks) over a `verus!` item list, then hands the result
/// back to `verus!` via `verus_spec_check_resume!`.
#[proc_macro]
pub fn vcheck_preprocess(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = verus_syn::rejoin_tokens(input.into());
    let mut items = match verus_syn::parse2::<Items>(input) {
        Ok(Items(items)) => items,
        Err(err) => return err.to_compile_error().into(),
    };
    verus_spec_check_engine::vcheck_provide_preprocess(&mut items);
    to_vstd_paths(quote! {
        ::verus_builtin_macros::verus_spec_check_resume! { #(#items)* }
    })
    .into()
}

/// The engine's `verus_spec_check_unverified!`, with its output pointed into vstd.
#[proc_macro]
pub fn verus_spec_check_unverified(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    to_vstd_paths(verus_spec_check_engine::expand_verus_spec_check(input.into(), false)).into()
}

/// The engine's `verus_spec_check_verified!`, with its output pointed into vstd.
#[proc_macro]
pub fn verus_spec_check_verified(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    to_vstd_paths(verus_spec_check_engine::expand_verus_spec_check(input.into(), true)).into()
}

const ENGINE_MACROS: &[&str] = &["verus_spec_check_unverified", "verus_spec_check_verified"];

/// Rewrites the engine's paths for use inside vstd (see the crate docs!)
fn to_vstd_paths(tokens: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = tokens.into_iter().collect();
    let mut out: Vec<TokenTree> = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        if let Some(root) = leading_path_root(&tokens, i, out.last()) {
            let replace = root == "verus_spec_check_vstd_ext"
                || (root == "verus_spec_check"
                    && path_root(&tokens, i + 3)
                        .is_some_and(|next| ENGINE_MACROS.iter().any(|m| next == *m)));
            if replace {
                out.extend(bridge_module(root.span()));
                i += 3;
                continue;
            }
        }
        out.push(match &tokens[i] {
            TokenTree::Group(g) => {
                let mut group = Group::new(g.delimiter(), to_vstd_paths(g.stream()));
                group.set_span(g.span());
                TokenTree::Group(group)
            }
            other => other.clone(),
        });
        i += 1;
    }
    out.into_iter().collect()
}

/// If `tokens[i..]` starts with `:: ident`, returns `ident`.
fn path_root(tokens: &[TokenTree], i: usize) -> Option<&Ident> {
    match (tokens.get(i), tokens.get(i + 1), tokens.get(i + 2)) {
        (Some(TokenTree::Punct(a)), Some(TokenTree::Punct(b)), Some(TokenTree::Ident(id)))
            if a.as_char() == ':' && a.spacing() == Spacing::Joint && b.as_char() == ':' =>
        {
            Some(id)
        }
        _ => None,
    }
}

/// Like [`path_root`], but only for a path that starts at `tokens[i]` (`::ident` after a
/// keyword, punctuation, or the start of a group), not one that continues `a::b` or `T<..>::b`.
fn leading_path_root<'a>(
    tokens: &'a [TokenTree],
    i: usize,
    prev: Option<&TokenTree>,
) -> Option<&'a Ident> {
    let continues_path = match prev {
        Some(TokenTree::Punct(p)) => p.as_char() == '>',
        Some(TokenTree::Ident(id)) => !is_keyword_before_path(&id.to_string()),
        _ => false,
    };
    if continues_path { None } else { path_root(tokens, i) }
}

/// Keywords that can directly precede a path with a leading `::`, as in `use ::x::y`.
fn is_keyword_before_path(word: &str) -> bool {
    matches!(
        word,
        "as" | "box"
            | "break"
            | "const"
            | "dyn"
            | "else"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "match"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "static"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "yield"
    )
}

/// `crate::contrib::spec_check`, vstd's stand-in for `verus_spec_check_vstd_ext`
fn bridge_module(span: Span) -> Vec<TokenTree> {
    let mut tokens = Vec::new();
    for (n, segment) in ["crate", "contrib", "spec_check"].into_iter().enumerate() {
        if n > 0 {
            tokens.push(punct(':', Spacing::Joint, span));
            tokens.push(punct(':', Spacing::Alone, span));
        }
        tokens.push(TokenTree::Ident(Ident::new(segment, span)));
    }
    tokens
}

fn punct(ch: char, spacing: Spacing, span: Span) -> TokenTree {
    let mut punct = Punct::new(ch, spacing);
    punct.set_span(span);
    TokenTree::Punct(punct)
}
