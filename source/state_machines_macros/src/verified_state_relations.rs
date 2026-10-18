//! Original pure weak relations alongside the checked backend's strong relations.
//!
//! These definitions grant no resource authority and do not change the existing
//! enabled predicates, safety proofs, executors, or protocol frame conditions.
use crate::ast::TransitionKind;
use crate::parse_token_stream::SMBundle;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::Error;

pub fn output(bundle: &SMBundle, state: &TokenStream) -> Result<Vec<TokenStream>, Error> {
    let sm = &bundle.sm;
    let mut methods: HashSet<String> = ["invariant", "__storage"]
        .iter()
        .map(|name| name.to_string())
        .collect();
    methods.extend(
        bundle
            .normal_fns
            .iter()
            .map(|function| function.sig.ident.to_string()),
    );
    methods.extend(
        bundle
            .extras
            .invariants
            .iter()
            .map(|invariant| invariant.func.sig.ident.to_string()),
    );
    methods.extend(
        bundle
            .extras
            .lemmas
            .iter()
            .map(|lemma| lemma.func.sig.ident.to_string()),
    );
    for transition in &sm.transitions {
        if transition.kind == TransitionKind::Init {
            methods.insert(transition.name.to_string());
        }
        for suffix in [
            "_strong",
            "_enabled",
            "_safety",
            "_execute",
            "_owners_enabled",
            "_deposited",
            "_guarded",
            "_declared_requires",
            "_local_deposited",
        ] {
            methods.insert(format!("{}{suffix}", transition.name));
        }
        for field in &sm.fields {
            methods.insert(format!("{}_{}_effect", transition.name, field.name));
            methods.insert(format!("{}_{}_effect_owned", transition.name, field.name));
        }
    }
    let mut definitions = Vec::new();
    for transition in &sm.transitions {
        if matches!(
            transition.kind,
            TransitionKind::Init | TransitionKind::Property
        ) {
            continue;
        }
        let name = &transition.name;
        let enabled_weak = format_ident!("{}_enabled_weak", name);
        for candidate in [name, &enabled_weak] {
            if !methods.insert(candidate.to_string()) {
                return Err(Error::new(
                    candidate.span(),
                    "pure weak State relation conflicts with an existing State method",
                ));
            }
        }
        let (simplified, _) = crate::simplification::inline_unassigned(
            sm,
            crate::simplification::simplify_ops(sm, &transition.body, transition.kind),
        );
        let relation = crate::to_relation::to_relation(&simplified, true);
        let enabling = crate::to_relation::to_is_enabled_condition_weak(&simplified);
        let parameters: Vec<_> = transition
            .params
            .iter()
            .map(|parameter| {
                let name = &parameter.name;
                let ty = &parameter.ty;
                quote! {#name: #ty}
            })
            .collect();
        definitions.push(quote! {
            pub open spec fn #name(pre: #state, post: #state, #(#parameters),*) -> bool {#relation}
            pub open spec fn #enabled_weak(pre: #state, #(#parameters),*) -> bool {#enabling}
        });
    }
    Ok(definitions)
}
