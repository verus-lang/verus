//! Pure state-machine relations and checked mathematical next-state constructors.
//!
//! This emitter preserves the ordinary weak, strong, and enabling definitions.
//! It does not construct resources or derive strong enabling from weak enabling.
//! Constructors require strong enabling and use checked induction hooks. Source
//! assertion proof blocks are never emitted.
use crate::ast::TransitionKind;
use crate::lemmas::{check_lemmas, get_transition};
use crate::parse_token_stream::{ParseResult, SMBundle, parse_result_to_smir};
use crate::simplification::simplify_ops;
use crate::to_relation::{
    to_is_enabled_condition_strong, to_is_enabled_condition_weak, to_relation,
};
use crate::to_token_stream::{
    fix_attrs, generics_for_decl, get_generic_args, set_mode_proof, shardable_type_to_type,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use verus_syn::spanned::Spanned;
use verus_syn::{Error, FnArgKind, FnMode, ModeSpec, Open, Publish, token};

pub fn construct(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let result = verus_syn::parse::<ParseResult>(input).and_then(|parsed| {
        // Ordinary models need no sharding annotations. Annotated models use
        // the same parser and operation lowering as tokenized machines.
        let annotated = parsed.fields.as_ref().is_some_and(|fields| {
            fields.named.iter().any(|field| {
                field.attrs.iter().any(|attribute| attribute.meta.path().is_ident("sharding"))
            })
        });
        let bundle = parse_result_to_smir(parsed, annotated)?;
        check_lemmas(&bundle)?;
        output(bundle)
    });
    match result {
        Ok(output) => output.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

pub fn output(bundle: SMBundle) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    let steps = crate::verified_steps::output(sm)?;
    let take_step = crate::verified_take_step::output(&bundle)?;
    let name = &sm.name;
    let (generics, datatype_attrs) = crate::verified_tokens::datatype_generics(sm);
    let (declaration, where_clause) = generics_for_decl(&generics);
    let arguments = generics.as_ref().map(|generics| get_generic_args(&generics.params));
    let types = arguments.as_ref().map(|args| quote! {<#args>}).unwrap_or_default();
    let fields = sm.fields.iter().map(|field| {
        let name = &field.name;
        let ty = shardable_type_to_type(field.type_span, &field.stype);
        quote! {pub #name: #ty}
    });
    let mut definitions = Vec::new();
    for transition in &sm.transitions {
        // Match the ordinary generator: properties have no state relation.
        if transition.kind == TransitionKind::Property {
            continue;
        }
        let body = simplify_ops(sm, &transition.body, transition.kind);
        let relation = to_relation(&body, true);
        let strong_relation = to_relation(&body, false);
        let enabling = to_is_enabled_condition_weak(&body);
        let strong_enabling = to_is_enabled_condition_strong(&body);
        let name = &transition.name;
        let strong = format_ident!("{}_strong", name);
        let enabled = format_ident!("{}_enabled", name);
        let enabled_strong = format_ident!("{}_enabled_strong", name);
        let parameters: Vec<_> = transition
            .params
            .iter()
            .map(|parameter| {
                let name = &parameter.name;
                let ty = &parameter.ty;
                quote! {#name: #ty}
            })
            .collect();
        if transition.kind == TransitionKind::Init {
            definitions.push(quote! {
                pub open spec fn #name(post: Self, #(#parameters),*) -> bool { #relation }
                pub open spec fn #enabled(#(#parameters),*) -> bool { #enabling }
                pub open spec fn #enabled_strong(#(#parameters),*) -> bool { #strong_enabling }
            });
        } else {
            definitions.push(quote! {
                pub open spec fn #name(pre: Self, post: Self, #(#parameters),*) -> bool { #relation }
                pub open spec fn #strong(pre: Self, post: Self, #(#parameters),*) -> bool { #strong_relation }
                pub open spec fn #enabled(pre: Self, #(#parameters),*) -> bool { #enabling }
                pub open spec fn #enabled_strong(pre: Self, #(#parameters),*) -> bool { #strong_enabling }
            });
        }
    }
    let invariant_names: Vec<_> =
        bundle.extras.invariants.iter().map(|invariant| &invariant.func.sig.ident).collect();
    let invariant = quote! {true #(&& self.#invariant_names())*};
    let invariants: Vec<_> = bundle
        .extras
        .invariants
        .iter()
        .map(|invariant| {
            let mut function = invariant.func.clone();
            fix_attrs(&mut function.attrs);
            function.sig.mode =
                FnMode::Spec(ModeSpec { spec_token: token::Spec { span: function.span() } });
            function.sig.publish =
                Publish::Open(Open { token: token::Open { span: function.span() } });
            quote! {::vstd::prelude::verus_impl! {#function}}
        })
        .collect();
    let mut induction = Vec::new();
    for lemma in &bundle.extras.lemmas {
        let transition = get_transition(&sm.transitions, &lemma.purpose.transition.to_string())
            .expect("checked induction transition");
        let mut function = lemma.func.clone();
        let arguments: Vec<_> = function
            .sig
            .inputs
            .iter()
            .map(|argument| match &argument.kind {
                FnArgKind::Typed(argument) => Ok(argument.pat.clone()),
                FnArgKind::Receiver(_) => {
                    Err(Error::new(argument.span(), "induction hook cannot have self"))
                }
            })
            .collect::<Result<_, _>>()?;
        let transition_name = &transition.name;
        let condition = if transition.kind == TransitionKind::Init {
            quote! {Self::#transition_name(#(#arguments),*)}
        } else {
            let strong = format_ident!("{}_strong", transition_name);
            quote! {pre.invariant() && Self::#strong(#(#arguments),*)}
        };
        let body = &function.block;
        function.block = verus_syn::parse_quote! {{
            ::vstd::prelude::requires(#condition);
            ::vstd::prelude::ensures(post.invariant());
            #body
        }};
        let span = function.sig.span();
        set_mode_proof(&mut function.sig, span);
        fix_attrs(&mut function.attrs);
        induction.push(quote! {::vstd::prelude::verus_impl! {#function}});
    }
    let normal: Vec<_> = bundle
        .normal_fns
        .iter()
        .map(|function| {
            quote! {::vstd::prelude::verus_impl! {#function}}
        })
        .collect();
    Ok(quote! {
        pub mod #name {
            use super::*;
            ::vstd::prelude::verus! {
                #(#datatype_attrs)*
                #[verifier::ext_equal]
                pub struct State #declaration #where_clause { #(#fields),* }
                impl #declaration State #types #where_clause {
                    pub open spec fn invariant(&self) -> bool { #invariant }
                    #(#definitions)*
                }
                #steps
                #take_step
            }
            impl #declaration State #types #where_clause {
                #(#invariants)*
                #(#induction)*
                #(#normal)*
            }
        }
    })
}
