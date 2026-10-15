//! Checked aggregate relations and their introduction proofs.
//! These definitions classify existing relations; they neither allocate resources
//! nor turn a weak relation into an enabled or invariant-preserving transition.
use crate::ast::{TransitionKind, SM};
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident};

fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(name) => {
                names.insert(name.to_string().trim_start_matches("r#").to_string());
            }
            TokenTree::Group(group) => reserve(group.stream(), names),
            _ => {}
        }
    }
}

fn occupied(sm: &SM) -> HashSet<String> {
    let mut names = HashSet::new();
    let generics = &sm.generics;
    let fields = &sm.fields_named_ast;
    reserve(quote! {#generics #fields}, &mut names);
    for transition in &sm.transitions {
        let name = &transition.name;
        reserve(quote! {#name}, &mut names);
        for param in &transition.params {
            let name = &param.name;
            let ty = &param.ty;
            reserve(quote! {#name #ty}, &mut names);
        }
        crate::verified_field_storage_map_pair::reserve_stmt(&transition.body, &mut names);
    }
    names
}

fn fresh(names: &mut HashSet<String>, label: &str) -> Ident {
    let mut name = format!("__tsm_aggregate_{label}");
    while names.contains(&name) {
        name.push('_');
    }
    names.insert(name.clone());
    Ident::new(&name, Span::mixed_site())
}

pub fn output(sm: &SM) -> Result<TokenStream, Error> {
    let (generics, attributes) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let init_label = &sm.init_label;
    let transition_label = &sm.transition_label;
    let mut declarations = Vec::new();
    let mut methods = Vec::new();
    let mut proofs = Vec::new();
    let mut names = occupied(sm);

    for is_init in [true, false] {
        let datatype = if is_init {
            format_ident!("Config")
        } else {
            format_ident!("Step")
        };
        let label_type = if is_init {
            format_ident!("InitLabel")
        } else {
            format_ident!("Label")
        };
        let has_label = if is_init {
            init_label.is_some()
        } else {
            transition_label.is_some()
        };
        let label_args = sm
            .get_label_generics_opt(is_init)
            .filter(|g| !g.params.is_empty())
            .map(|g| get_generic_args(&g.params))
            .map(|a| quote! {<#a>})
            .unwrap_or_default();
        let transitions: Vec<_> = sm
            .transitions
            .iter()
            .filter(|tr| {
                if is_init {
                    tr.kind == TransitionKind::Init
                } else {
                    matches!(
                        tr.kind,
                        TransitionKind::Transition | TransitionKind::ReadonlyTransition
                    )
                }
            })
            .collect();
        if let Some(transition) = transitions
            .iter()
            .find(|tr| tr.name == "dummy_to_use_type_params")
        {
            return Err(Error::new(
                transition.name.span(),
                "transition conflicts with the original aggregate dummy variant",
            ));
        }
        let mut variants = Vec::new();
        let mut weak_arms = Vec::new();
        let mut strong_arms = Vec::new();
        let pre = fresh(&mut names, "pre");
        let post = fresh(&mut names, "post");
        let label = fresh(&mut names, "label");
        let step = fresh(&mut names, "step");
        for transition in transitions {
            let name = &transition.name;
            let strong = format_ident!("{name}_strong");
            let data_params = &transition.params[usize::from(has_label)..];
            let data_types: Vec<_> = data_params.iter().map(|p| &p.ty).collect();
            let data_names: Vec<_> = data_params
                .iter()
                .map(|_| fresh(&mut names, "argument"))
                .collect();
            variants.push(quote! {#name(#(#data_types),*)});
            let relation_args = if has_label {
                quote! {#label,#(#data_names),*}
            } else {
                quote! {#(#data_names),*}
            };
            let state_args = if is_init {
                quote! {#post,}
            } else {
                quote! {#pre,#post,}
            };
            weak_arms.push(quote! {#datatype::#name(#(#data_names),*)=>Self::#name(#state_args #relation_args)});
            if !is_init {
                strong_arms.push(quote! {#datatype::#name(#(#data_names),*)=>Self::#strong(#state_args #relation_args)});
            }
            let params: Vec<_> = transition
                .params
                .iter()
                .map(|p| {
                    let n = &p.name;
                    let t = &p.ty;
                    quote! {#n:#t}
                })
                .collect();
            let param_names: Vec<_> = transition.params.iter().map(|p| &p.name).collect();
            let stored_names: Vec<_> = data_params.iter().map(|p| &p.name).collect();
            let witness = fresh(&mut names, "witness");
            let aggregate = if is_init {
                format_ident!("init")
            } else {
                format_ident!("next")
            };
            let by = if is_init {
                format_ident!("init_by")
            } else {
                format_ident!("next_by")
            };
            let label_arg = if has_label {
                let n = &transition.params[0].name;
                quote! {#n,}
            } else {
                quote! {}
            };
            let state_params = if is_init {
                quote! {#post:State #types,}
            } else {
                quote! {#pre:State #types,#post:State #types,}
            };
            proofs.push(quote! {
                pub proof fn #name #decl (#state_params #(#params),*) #wc
                    requires State #expr::#name(#state_args #(#param_names),*),
                    ensures State #expr::#aggregate(#state_args #label_arg),
                {
                    reveal(State::#aggregate);
                    reveal(State::#by);
                    let #witness=#datatype #expr::#name(#(#stored_names),*);
                    assert(State #expr::#by(#state_args #label_arg #witness));
                }
            });
        }
        declarations.push(quote! {
            #(#attributes)*
            #[allow(non_camel_case_types)]
            #[is_variant]
            pub enum #datatype #decl #wc {
                #(#variants,)*
                dummy_to_use_type_params(State #types),
            }
        });
        let state_params = if is_init {
            quote! {#post:Self,}
        } else {
            quote! {#pre:Self,#post:Self,}
        };
        let state_args = if is_init {
            quote! {#post,}
        } else {
            quote! {#pre,#post,}
        };
        let label_param = if has_label {
            quote! {#label:#label_type #label_args,}
        } else {
            quote! {}
        };
        let label_arg = if has_label {
            quote! {#label,}
        } else {
            quote! {}
        };
        let aggregate = if is_init {
            format_ident!("init")
        } else {
            format_ident!("next")
        };
        let by = if is_init {
            format_ident!("init_by")
        } else {
            format_ident!("next_by")
        };
        methods.push(quote! {
            #[verifier::opaque]
            pub open spec fn #by(#state_params #label_param #step:#datatype #types)->bool {
                match #step {
                    #(#weak_arms,)*
                    #datatype::dummy_to_use_type_params(_)=>false,
                }
            }
            #[verifier::opaque]
            pub open spec fn #aggregate(#state_params #label_param)->bool {
                exists|#step:#datatype #types|Self::#by(#state_args #label_arg #step)
            }
        });
        if !is_init {
            methods.push(quote! {
                #[verifier::opaque]
                pub open spec fn next_strong_by(#state_params #label_param #step:Step #types)->bool {
                    match #step {
                        #(#strong_arms,)*
                        Step::dummy_to_use_type_params(_)=>false,
                    }
                }
                #[verifier::opaque]
                pub open spec fn next_strong(#state_params #label_param)->bool {
                    exists|#step:Step #types|Self::next_strong_by(#state_args #label_arg #step)
                }
            });
        }
    }
    Ok(quote! {
        #init_label
        #transition_label
        #(#declarations)*
        impl #decl State #types #wc { #(#methods)* }
        pub mod show {
            use super::*;
            #(#proofs)*
        }
    })
}
