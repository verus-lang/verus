//! Checked mathematical next-state construction.
//! Strong enabling supplies every requirement and assertion. This module never
//! emits the source assertion proof blocks, fabricates ownership, or derives
//! strong enabling from weak enabling.
use crate::ast::{SimplStmt, SplitKind, TransitionKind};
use crate::parse_token_stream::SMBundle;
use crate::simplification::{UPDATE_TMP_PREFIX, simplify_ops};
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident};

/// Adds every identifier in `tokens` to `names`; rejects raw `update_tmp_` identifiers.
fn reserve(tokens: TokenStream, names: &mut HashSet<String>) -> Result<(), Error> {
    for token in tokens {
        match token {
            TokenTree::Ident(id) => {
                if id.to_string().starts_with("r#update_tmp_") {
                    return Err(Error::new(
                        id.span(),
                        "raw identifiers starting with 'update_tmp_' are reserved in checked models",
                    ));
                }
                names.insert(id.to_string().trim_start_matches("r#").to_string());
            }
            TokenTree::Group(group) => reserve(group.stream(), names)?,
            _ => {}
        }
    }
    Ok(())
}

/// A fresh `__tsm_checked_take_step_<label>` name, reserved in `names`.
fn fresh(names: &mut HashSet<String>, label: &str) -> Ident {
    let mut name = format!("__tsm_checked_take_step_{label}");
    while names.contains(&name) {
        name.push('_');
    }
    names.insert(name.clone());
    Ident::new(&name, Span::mixed_site())
}

// The parser rejects the update_tmp_ prefix in caller identifiers (see
// ident_visitor.rs). This emitter also rejects raw spellings of that prefix,
// so simplification temporaries cannot capture source locals.
// Declare each field temporary once, outside its lexical scopes;
// original lets and match-arm binders remain inside their original scopes.
fn statements(body: &[SimplStmt]) -> Result<TokenStream, Error> {
    let mut output = TokenStream::new();
    for statement in body {
        output.extend(match statement {
            SimplStmt::Assign(_, name, _, expression, _) => quote! {#name = #expression;},
            SimplStmt::Require(_, expression) | SimplStmt::Assert(_, expression, _) => {
                quote! {assert(#expression);}
            }
            SimplStmt::PostCondition(..) => TokenStream::new(),
            SimplStmt::Let(_, pattern, ty, expression, children, _) => {
                let typed = ty.as_ref().map(|ty| quote! {: #ty}).unwrap_or_default();
                let children = statements(children)?;
                quote! {{let #pattern #typed = #expression; #children}}
            }
            SimplStmt::Split(span, kind, children, _) => match &**kind {
                SplitKind::If(condition) if children.len() == 2 => {
                    let left = statements(&children[0].1)?;
                    let right = statements(&children[1].1)?;
                    quote! {if #condition {#left} else {#right}}
                }
                SplitKind::Match(expression, arms) if arms.len() == children.len() => {
                    let arms = arms
                        .iter()
                        .zip(children)
                        .map(|(arm, child)| {
                            let pattern = &arm.pat;
                            let guard =
                                arm.guard.as_ref().map(|(_, expression)| quote! {if #expression});
                            let body = statements(&child.1)?;
                            Ok(quote! {#pattern #guard => {#body}})
                        })
                        .collect::<Result<Vec<_>, Error>>()?;
                    quote! {match #expression {#(#arms,)*}}
                }
                _ => return Err(Error::new(*span, "unsupported checked take_step scope")),
            },
        });
    }
    Ok(output)
}

/// `tokens` with every `Self` replaced by `state_type`.
fn replace_self(tokens: TokenStream, state_type: &TokenStream) -> TokenStream {
    let mut output = TokenStream::new();
    for token in tokens {
        match token {
            TokenTree::Ident(id) if id == "Self" => output.extend(state_type.clone()),
            TokenTree::Group(group) => {
                let mut replacement = proc_macro2::Group::new(
                    group.delimiter(),
                    replace_self(group.stream(), state_type),
                );
                replacement.set_span(group.span());
                output.extend([TokenTree::Group(replacement)]);
            }
            token => output.extend([token]),
        }
    }
    output
}

/// The checked next-state constructors of the transitions (as `State` methods) and their
/// `take_step` wrappers.
pub fn output(bundle: &SMBundle) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    let (generics, _) = crate::verified_tokens::datatype_generics(sm);
    let (declaration, where_clause) = generics_for_decl(&generics);
    let arguments = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = arguments.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = arguments.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let mut names = HashSet::new();
    let fields_ast = &sm.fields_named_ast;
    reserve(quote! {#generics #fields_ast}, &mut names)?;
    for transition in &sm.transitions {
        let name = &transition.name;
        reserve(quote! {#name}, &mut names)?;
        for parameter in &transition.params {
            let name = &parameter.name;
            let ty = &parameter.ty;
            reserve(quote! {#name #ty}, &mut names)?;
        }
        crate::verified_steps::reserve_stmt(&transition.body, &mut names);
    }
    for function in &bundle.normal_fns {
        reserve(quote! {#function}, &mut names)?;
    }
    for invariant in &bundle.extras.invariants {
        let function = &invariant.func;
        reserve(quote! {#function}, &mut names)?;
    }
    for lemma in &bundle.extras.lemmas {
        let function = &lemma.func;
        reserve(quote! {#function}, &mut names)?;
    }
    let mut constructors = Vec::new();
    let mut wrappers = Vec::new();
    for transition in &sm.transitions {
        if transition.kind == TransitionKind::Property {
            continue;
        }
        let name = &transition.name;
        let constructor = fresh(&mut names, &name.to_string());
        let enabled = format_ident!("{name}_enabled_strong");
        let strong = if transition.kind == TransitionKind::Init {
            name.clone()
        } else {
            format_ident!("{name}_strong")
        };
        let parameters: Vec<_> = transition
            .params
            .iter()
            .map(|p| {
                let name = &p.name;
                let ty = &p.ty;
                quote! {#name: #ty}
            })
            .collect();
        let parameter_names: Vec<_> = transition.params.iter().map(|p| &p.name).collect();
        let is_init = transition.kind == TransitionKind::Init;
        let input = if is_init {
            quote! {}
        } else {
            quote! {pre: Self,}
        };
        let wrapper_input = if is_init {
            quote! {}
        } else {
            quote! {pre: State #types,}
        };
        let input_arg = if is_init {
            quote! {}
        } else {
            quote! {pre,}
        };
        let relation_args = if is_init {
            quote! {post,}
        } else {
            quote! {pre, post,}
        };
        let pre_invariant = if is_init {
            quote! {true}
        } else {
            quote! {pre.invariant()}
        };
        let mut slots = Vec::new();
        let mut final_fields = Vec::new();
        for field in &sm.fields {
            let field_name = &field.name;
            let slot = format_ident!("{}{}", UPDATE_TMP_PREFIX, field_name);
            let ty = field.get_type();
            slots.push(quote! {let mut #slot: #ty = ::vstd::prelude::arbitrary();});
            final_fields.push(quote! {#field_name: #slot});
        }
        let body = statements(&simplify_ops(sm, &transition.body, transition.kind))?;
        // Inspect the complete emitted expression/pattern/type program, including
        // lowered special operands and subupdate indices, for raw reserved names.
        reserve(body.clone(), &mut names)?;
        let inductive = bundle
            .extras
            .lemmas
            .iter()
            .find(|l| l.purpose.transition == *name)
            .map(|lemma| {
                let lemma_name = &lemma.func.sig.ident;
                quote! {Self::#lemma_name(#relation_args #(#parameter_names),*);}
            })
            .unwrap_or_default();
        constructors.push(quote! {
            pub proof fn #constructor(#input #(#parameters),*) -> (post: Self)
                requires #pre_invariant, Self::#enabled(#input_arg #(#parameter_names),*),
                ensures Self::#strong(#relation_args #(#parameter_names),*), post.invariant(),
            {
                #(#slots)*
                #body
                let post = Self {#(#final_fields),*};
                assert(Self::#strong(#relation_args #(#parameter_names),*));
                #inductive
                post
            }
        });
        let outside_parameters: Vec<_> =
            parameters.into_iter().map(|p| replace_self(p, &quote! {State #types})).collect();
        wrappers.push(quote! {
            pub proof fn #name #declaration (#wrapper_input #(#outside_parameters),*)
                -> (post: State #types) #where_clause
                requires #pre_invariant, State #expr::#enabled(#input_arg #(#parameter_names),*),
                ensures State #expr::#strong(#relation_args #(#parameter_names),*), post.invariant(),
            {
                State #expr::#constructor(#input_arg #(#parameter_names),*)
            }
        });
    }
    Ok(quote! {
        impl #declaration State #types #where_clause {#(#constructors)*}
        pub mod take_step {
            use super::*;
            #(#wrappers)*
        }
    })
}
