/// Macros defined in this module enables developers to annotate Rust code in
/// standard Rust code, eliminating the need to wrap exec code inside `verus!
/// {}`.
///
/// Usage:
/// - Items (function, struct, const) used for verification need to be annotated
///   with `#[verus_verify].
/// - To apply `requires`, `ensures`, `invariant`, `decreases` in `exec`,
///   developers should call the corresponding macros at the beginning of the
///   function or loop.
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
/// - Refer to the `test_small_macros_verus_verify` in `example/syntax.rs`.
use core::convert::{TryFrom, TryInto};
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    parse2, parse_quote, spanned::Spanned, token, Attribute, AttributeArgs, Block, Expr, Ident,
    Item, Stmt, TraitItem, TraitItemMethod,
};

use crate::{
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax,
    syntax::VERUS_SPEC,
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

fn remove_verus_attributes(attrs: &mut Vec<Attribute>) -> Vec<SpecAttrWithArgs> {
    let mut verus_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in attrs.drain(0..) {
        if attr.path.segments.len() == 1 {
            if let Ok(attr_kind) = attr.path.segments[0].ident.to_string().try_into() {
                let args = insert_brackets(&attr_kind, attr.tokens);
                verus_attributes.push((attr_kind, args));
            } else {
                regular_attributes.push(attr);
            }
        } else {
            regular_attributes.push(attr);
        }
    }
    *attrs = regular_attributes;
    verus_attributes
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
    erase: &EraseGhost,
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

/// Add a default exec function with spec calls.
///   fn #[requires(x)]f(); //a trait method;
/// becomes
///   #[requires(true)]
///   fn VERUS_SPEC__f() {}
///   fn f();
/// and then rewrite_verus_fn_attribute:
///   fn VERUS_SPEC__f() { requires(x); ... }
///   fn f();
fn expand_verus_attribute_on_trait_method(
    erase: &EraseGhost,
    verus_attrs: Vec<SpecAttrWithArgs>,
    fun: &mut TraitItemMethod,
) -> Option<TraitItem> {
    if verus_attrs.is_empty() {
        return None;
    }

    // For trait methods, we must parse requires/ensures together since
    // we only insert a single new function. Thus, the first spec macro
    // will use remove_verus_attributes and then invoke the rewrite for
    // all followed verus attributes.
    let mut verus_attrs = verus_attrs;
    verus_attrs.extend(remove_verus_attributes(&mut fun.attrs));
    let mut spec_fun = fun.clone();
    let x = fun.sig.ident.clone();
    if fun.default.is_none() {
        spec_fun.sig.ident = Ident::new(&format!("{VERUS_SPEC}{x}"), spec_fun.sig.span());
        spec_fun.attrs.push(parse_quote!(#[doc(hidden)]));
        spec_fun.attrs.push(parse_quote!(#[allow(non_snake_case)]));
        let stmts = vec![Stmt::Expr(Expr::Verbatim(
            quote_spanned_builtin!(builtin, spec_fun.default.span() => #builtin::no_method_body()),
        ))];
        spec_fun.default =
            Some(Block { brace_token: token::Brace(spec_fun.default.span()), stmts });
        expand_verus_attribute(erase, verus_attrs, &mut spec_fun, true);
        Some(TraitItem::Method(spec_fun))
    } else {
        expand_verus_attribute(erase, verus_attrs, fun, true);
        None
    }
}

fn insert_spec_call(any_fn: &mut dyn AnyAttrBlock, call: &str, verus_expr: TokenStream) {
    let fname = Ident::new(call, verus_expr.span());
    let tokens: TokenStream =
        syntax::rewrite_expr(EraseGhost::Keep, true, verus_expr.into()).into();
    any_fn
        .block_mut()
        .unwrap()
        .stmts
        .insert(0, parse2(quote! { ::builtin::#fname(#tokens); }).unwrap());
}

pub fn rewrite_verus_attribute(
    erase: &EraseGhost,
    attr_args: AttributeArgs,
    input: TokenStream,
) -> TokenStream {
    if erase.keep() {
        let item: Item = parse2(input).expect("#[verus_verify] must on item");
        let mut attributes: Vec<TokenStream> = vec![];
        const VERIFIER_ATTRS: [&str; 2] = ["external", "external_body"];
        for arg in attr_args {
            if let syn::NestedMeta::Meta(m) = arg {
                if VERIFIER_ATTRS.contains(&m.to_token_stream().to_string().as_str()) {
                    attributes.push(quote_spanned!(m.span() => #[verifier::#m]));
                } else {
                    panic!(
                        "unsupported parameters {:?} in #[verus_verify(...)]",
                        m.to_token_stream().to_string()
                    );
                }
            }
        }
        if attributes.len() == 0 {
            attributes.push(quote_spanned!(item.span() => #[verifier::verify]));
        }

        quote_spanned! {item.span()=>
            #(#attributes)*
            #item
        }
    } else {
        input
    }
}

pub fn rewrite(
    erase: &EraseGhost,
    outer_attr: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    input: TokenStream,
) -> Result<TokenStream, syn::Error> {
    let outer_attr_tokens = insert_brackets(&outer_attr, outer_attr_tokens);
    let verus_attrs = vec![(outer_attr, outer_attr_tokens)];
    let f = parse2::<AnyFnOrLoop>(input)?;
    match f {
        AnyFnOrLoop::Fn(mut item_fn) => {
            expand_verus_attribute(erase, verus_attrs, &mut item_fn, true);
            Ok(quote_spanned! {item_fn.span()=>#item_fn})
        }
        AnyFnOrLoop::TraitMethod(mut trait_item_method) => {
            let spec_item =
                expand_verus_attribute_on_trait_method(erase, verus_attrs, &mut trait_item_method);
            match spec_item {
                Some(spec_method) => {
                    Ok(quote_spanned! {trait_item_method.span()=> #trait_item_method #spec_method})
                }
                _ => {
                    unreachable!()
                }
            }
        }
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
    }
}

pub fn proof_rewrite(erase: EraseGhost, input: TokenStream) -> proc_macro::TokenStream {
    if erase.keep() {
        let block: TokenStream =
            syntax::proof_block(erase, quote_spanned!(input.span() => {#input}).into()).into();
        quote! {
            #[verifier::proof_block]
            #block
        }
        .into()
    } else {
        proc_macro::TokenStream::new()
    }
}
