use core::convert::TryFrom;
use core::convert::TryInto;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
/// Macros defined in this module enables developers to annotate Rust code in
/// standard Rust code, eliminating the need to wrap exec code inside `verus!
/// {}`.
///
/// Usage:
/// - Items (function, struct, const) used for verification need to be annotated
///   with `#[verifier::verify].
/// - To apply `requires`, `ensures`, `invariant`, or `proof` in `exec`,
///   developers should call the corresponding macros at the beginning of the
///   function or loop.
///
/// Rationale:
/// - This approach avoids introducing new syntax into existing Rust executable
///   code, allowing verification and non-verification developers to collaborate
///   without affecting each other.
///   For developers who do not understand verification, they can easily ignore
///   verus code via feature selection and use standard rust tools like
///   `rustfmt` and `rust-analyzer`.
///
/// Limitations:
/// - #[verifier::verify] does not support all `verus` syntax, particularly
///   those constructs not accepted by `rustc`.
/// - For defining complex `verus` specifications or proof functions, developers
///   should still use `verus! {}`.
/// - Use of tracked variable is possible but in a different style.
///
/// Example:
/// - Refer to the `test_small_macros_verus_verify` in `example/syntax.rs`.
use syn::{parse_macro_input, parse_quote, Attribute, Stmt, Token};

use crate::{
    group_types::{AnyFnItem, AnyLoopItem},
    syntax, EraseGhost,
};
use syn::spanned::Spanned;

pub enum SpecAttributeKind {
    Requires,
    Ensures,
    Invariant,
    Proof,
    TraitVerify,
}

impl TryFrom<String> for SpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(SpecAttributeKind::Requires),
            "ensures" => Ok(SpecAttributeKind::Ensures),
            "invariant" => Ok(SpecAttributeKind::Invariant),
            "proof" => Ok(SpecAttributeKind::Proof),
            _ => Err(name),
        }
    }
}

fn extract_verus_attributes(attrs: &mut Vec<Attribute>) -> Vec<(SpecAttributeKind, TokenStream)> {
    let mut verus_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in attrs.drain(0..) {
        if attr.path.segments.len() == 1 {
            if let Ok(attr_kind) = attr.path.segments[0].ident.to_string().try_into() {
                verus_attributes.push((attr_kind, attr.tokens));
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

pub fn rewrite_verus_fn_attribute(
    erase: &EraseGhost,
    outer_attr_kind: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    tokens: TokenStream,
) -> TokenStream {
    let mut any_fn: AnyFnItem = syn::parse2(tokens).expect("not on function items");
    // Start with the outer attribute
    let mut verus_attrs = vec![(outer_attr_kind, outer_attr_tokens)];
    // remove verus attributes
    verus_attrs.extend(extract_verus_attributes(any_fn.attrs_mut()));

    if erase.keep() {
        // insert verifier::verify
        let verifier_attr: Attribute = parse_quote!(#[verifier::verify]);
        any_fn.attrs_mut().push(verifier_attr);
        // rewrite based on different spec attributes
        for (attr_kind, attr_tokens) in verus_attrs {
            match attr_kind {
                SpecAttributeKind::Requires => {
                    insert_requires(&mut any_fn, attr_tokens);
                }
                SpecAttributeKind::Ensures => {
                    insert_ensures(&mut any_fn, attr_tokens);
                }
                _ => {
                    unimplemented!()
                }
            }
        }
    }
    let ret = quote_spanned! {any_fn.span()=>
        #any_fn
    };
    println!("{}", ret);
    ret
}

fn insert_requires(any_fn: &mut AnyFnItem, outer_attr_tokens: TokenStream) {
    let tokens: TokenStream = syntax::proof_macro_exprs(
        EraseGhost::Keep,
        true,
        quote! {
                ::builtin::verus_proof_macro_exprs_args!([#outer_attr_tokens])
        }
        .into(),
    )
    .into();
    let requires = quote! { builtin::requires(#tokens); };
    any_fn.block_mut().unwrap().stmts.insert(0, syn::parse2(requires).unwrap());
}

fn insert_ensures(any_fn: &mut AnyFnItem, outer_attr_tokens: TokenStream) {
    let tokens: TokenStream = syntax::proof_macro_exprs(
        EraseGhost::Keep,
        true,
        quote! {
                ::builtin::verus_proof_macro_exprs_args!(#outer_attr_tokens)
        }
        .into(),
    )
    .into();
    let ensures = quote! { builtin::ensures(#tokens); };
    any_fn.block_mut().unwrap().stmts.insert(0, syn::parse2(ensures).unwrap());
}

pub fn rewrite_verus_loop_attribute(
    erase: &EraseGhost,
    outer_attr_kind: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    tokens: TokenStream,
) -> TokenStream {
    let mut any_loop: AnyLoopItem = syn::parse2(tokens).expect("not on loop expr");
}

fn insert_invariant(any_loop: &mut AnyLoopItem, outer_attr_tokens: TokenStream) {
    let tokens: TokenStream = syntax::proof_macro_exprs(
        EraseGhost::Keep,
        true,
        quote! {
                ::builtin::verus_proof_macro_exprs_args!(#outer_attr_tokens)
        }
        .into(),
    )
    .into();
    let ensures = quote! { builtin::invariant(#tokens); };
    any_loop.block_mut().unwrap().stmts.insert(0, syn::parse2(ensures).unwrap());
}
