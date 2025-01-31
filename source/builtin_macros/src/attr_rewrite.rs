/// Macros defined in this module enables developers to annotate Rust code in
/// standard Rust code, eliminating the need to wrap exec code inside `verus!
/// {}`.
///
/// Usage:
/// - Items (struct, const) used for verification need to be annotated
///   with `#[verus_verify].
/// - Functions used for verification need to be annotated with `#[verus_spec ...]`
///   or `#[verus_spec pattern => ...]`
///   where ... is a block of requires, ensures, decreases, etc. in the verus! syntax
/// - To apply `ensures`, `invariant`, `decreases` in `exec`,
///   developers should call the corresponding macros at the beginning of the loop
/// - To use proof block, add proof!{...} inside function body.
///
/// Rationale:
/// - This approach avoids introducing new syntax into existing Rust executable
///   code, allowing verification and non-verification developers to collaborate
///   without affecting each other.
///   Thus, this module uses syn instead of syn_verus in most cases.
///   For developers who do not understand verification, they can easily ignore
///   verus code via feature/cfg selection and use standard rust tools like
///   `rustfmt` and `rust-analyzer`.
///
/// Limitations:
/// - #[verus_verify] does not support all `verus` syntax, particularly
///   those constructs not accepted by `rustc`.
/// - For defining complex `verus` specifications or proof functions, developers
///   should still use `verus! {}`.
/// - Use of tracked variable is possible but in a different style.
///
/// Example:
/// - Refer to `example/syntax_attr.rs`.
use core::convert::TryFrom;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse2, spanned::Spanned, Ident, Item};

use crate::{
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax,
    syntax::mk_verus_attr_syn,
    EraseGhost,
};

#[derive(Debug)]
pub enum SpecAttributeKind {
    Requires,
    Ensures,
    Decreases,
    Invariant,
    InvariantExceptBreak,
}

struct SpecAttributeApply {
    pub on_function: bool,
    pub on_loop: bool,
}

type SpecAttrWithArgs = (SpecAttributeKind, TokenStream);

impl SpecAttributeKind {
    fn applies_to(&self) -> SpecAttributeApply {
        let (on_function, on_loop) = match self {
            SpecAttributeKind::Requires => (true, false),
            SpecAttributeKind::Ensures => (true, true),
            SpecAttributeKind::Decreases => (true, true),
            SpecAttributeKind::Invariant => (false, true),
            SpecAttributeKind::InvariantExceptBreak => (false, true),
        };
        SpecAttributeApply { on_function, on_loop }
    }

    fn applies_to_function(&self) -> bool {
        self.applies_to().on_function
    }

    fn applies_to_loop(&self) -> bool {
        self.applies_to().on_loop
    }
}

impl TryFrom<String> for SpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(SpecAttributeKind::Requires),
            "ensures" => Ok(SpecAttributeKind::Ensures),
            "decreases" => Ok(SpecAttributeKind::Decreases),
            "invariant" => Ok(SpecAttributeKind::Invariant),
            _ => Err(name),
        }
    }
}

// Add brackets for requires, invariant.
// Add brackets for ensures if it could not be parsed as a syn_verus::Expr.
fn insert_brackets(attr_type: &SpecAttributeKind, tokens: TokenStream) -> TokenStream {
    // Parse the TokenStream into a Syn Expression
    match attr_type {
        SpecAttributeKind::Ensures => {
            // if the tokens are not valid verus expr, it might need a bracket.
            syn_verus::parse2::<syn_verus::Expr>(tokens.clone())
                .map_or(quote! {[#tokens]}, |e| quote! {#e})
        }
        SpecAttributeKind::Decreases => tokens,
        _ => {
            quote! {[#tokens]}
        }
    }
}

fn expand_verus_attribute(
    erase: EraseGhost,
    verus_attrs: Vec<SpecAttrWithArgs>,
    any_with_attr_block: &mut dyn AnyAttrBlock,
    function_or_loop: bool,
) {
    if !erase.keep() {
        return;
    }
    // rewrite based on different spec attributes
    for (attr_kind, attr_tokens) in verus_attrs {
        if function_or_loop {
            assert!(attr_kind.applies_to_function());
        }
        if !function_or_loop {
            assert!(attr_kind.applies_to_loop());
        }
        match attr_kind {
            SpecAttributeKind::Invariant => {
                insert_spec_call(any_with_attr_block, "invariant", attr_tokens)
            }
            SpecAttributeKind::Decreases => {
                insert_spec_call(any_with_attr_block, "decreases", attr_tokens)
            }
            SpecAttributeKind::Ensures => {
                insert_spec_call(any_with_attr_block, "ensures", attr_tokens)
            }
            SpecAttributeKind::Requires => {
                insert_spec_call(any_with_attr_block, "requires", attr_tokens)
            }
            SpecAttributeKind::InvariantExceptBreak => {
                insert_spec_call(any_with_attr_block, "invariant_except_break", attr_tokens)
            }
        }
    }
}

fn insert_spec_call(any_fn: &mut dyn AnyAttrBlock, call: &str, verus_expr: TokenStream) {
    let fname = Ident::new(call, verus_expr.span());
    let tokens: TokenStream =
        syntax::rewrite_expr(EraseGhost::Keep, true, verus_expr.into()).into();
    any_fn.block_mut().unwrap().stmts.insert(
        0,
        parse2(quote! { #[verus::internal(const_header_wrapper)]||{::builtin::#fname(#tokens);};})
            .unwrap(),
    );
}

pub fn rewrite_verus_attribute(
    erase: &EraseGhost,
    attr_args: Vec<syn::Ident>,
    input: TokenStream,
) -> TokenStream {
    if erase.keep() {
        let item: Item = parse2(input).expect("#[verus_verify] must be applied to an item");
        let mut attributes = Vec::new();
        const VERIFIER_ATTRS: [&str; 2] = ["external", "external_body"];
        for arg in attr_args {
            if VERIFIER_ATTRS.contains(&arg.to_string().as_str()) {
                attributes.push(mk_verus_attr_syn(arg.span(), quote! { #arg }));
            } else {
                let span = arg.span();
                return proc_macro2::TokenStream::from(quote_spanned!(span =>
                    compile_error!("unsupported parameters {:?} in #[verus_verify(...)]");
                ));
            }
        }
        if attributes.len() == 0 {
            attributes.push(mk_verus_attr_syn(item.span(), quote! { verus_macro }));
        }

        quote_spanned! {item.span()=>
            #(#attributes)*
            #item
        }
    } else {
        input
    }
}

pub fn rewrite_verus_spec(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let f = match syn::parse::<AnyFnOrLoop>(input) {
        Ok(f) => f,
        Err(err) => {
            // Make sure at least one error is reported, just in case Rust parses the function
            // successfully but syn fails to parse it.
            // (In the normal case, this results in a redundant extra error message after
            // the normal Rust syntax error, but it's a reasonable looking error message.)
            return proc_macro::TokenStream::from(
                quote_spanned!(err.span() => compile_error!("syntax error in function");),
            );
        }
    };
    let spec_attr =
        syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::SignatureSpecAttr);
    match f {
        AnyFnOrLoop::Fn(mut fun) => {
            // Note: trait default methods appear in this case,
            // since they look syntactically like non-trait functions
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &fun.sig);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let _ = fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            fun.attrs.push(mk_verus_attr_syn(fun.span(), quote! { verus_macro }));
            proc_macro::TokenStream::from(fun.to_token_stream())
        }
        AnyFnOrLoop::TraitMethod(mut method) => {
            // Note: default trait methods appear in the AnyFnOrLoop::Fn case, not here
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &method.sig);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let mut spec_fun_opt = syntax::split_trait_method_syn(&method, erase.erase());
            let spec_fun = spec_fun_opt.as_mut().unwrap_or(&mut method);
            let _ = spec_fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            method.attrs.push(mk_verus_attr_syn(method.span(), quote! { verus_macro }));
            let mut new_stream = TokenStream::new();
            spec_fun_opt.to_tokens(&mut new_stream);
            method.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        _ => {
            let span = spec_attr.span();
            proc_macro::TokenStream::from(
                quote_spanned!(span => compile_error!("'verus_spec' is not allowed here");),
            )
        }
    }
}

pub fn rewrite(
    erase: EraseGhost,
    outer_attr: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    input: TokenStream,
) -> Result<TokenStream, syn::Error> {
    let span = outer_attr_tokens.span();
    let outer_attr_tokens = insert_brackets(&outer_attr, outer_attr_tokens);
    let verus_attrs = vec![(outer_attr, outer_attr_tokens)];
    let f = parse2::<AnyFnOrLoop>(input)?;
    match f {
        AnyFnOrLoop::Loop(mut l) => {
            expand_verus_attribute(erase, verus_attrs, &mut l, false);
            Ok(quote_spanned! {l.span()=>#l})
        }
        AnyFnOrLoop::ForLoop(mut l) => {
            expand_verus_attribute(erase, verus_attrs, &mut l, false);
            Ok(quote_spanned! {l.span()=>#l})
        }
        AnyFnOrLoop::While(mut l) => {
            expand_verus_attribute(erase, verus_attrs, &mut l, false);
            Ok(quote_spanned! {l.span()=>#l})
        }
        AnyFnOrLoop::Fn(_) | AnyFnOrLoop::TraitMethod(_) => Ok(
            quote_spanned!(span => compile_error!("'verus_spec' attribute expected on function");),
        ),
    }
}

pub fn proof_rewrite(erase: EraseGhost, input: TokenStream) -> proc_macro::TokenStream {
    if erase.keep() {
        let block: TokenStream =
            syntax::proof_block(erase, quote_spanned!(input.span() => {#input}).into()).into();
        quote! {
            #[verifier::proof_block]
            {
                #[verus::internal(const_header_wrapper)]||#block;
            }
        }
        .into()
    } else {
        proc_macro::TokenStream::new()
    }
}
