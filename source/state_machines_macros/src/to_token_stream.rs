//! Primary module for outputting the generated code.
//! This includes: the primary struct, the transition definitions,
//! invariant predicates, lemmas that prove inductiveness, and lemmas
//! that prove safety conditions (as given by the 'assert' statements).
//!
//! Concurrent-state-machine-specific stuff is in concurrency_tokens.rs

use crate::ast::{Invariant, Lemma, ShardableType, TransitionKind, TransitionParam, SM};
use crate::concurrency_tokens::output_token_types_and_fns;
use crate::lemmas::get_transition;
use crate::parse_token_stream::SMBundle;
use crate::safety_conditions::{has_any_assert, safety_condition_body};
use crate::simplification::simplify_updates;
use crate::to_relation::to_relation;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use std::mem::swap;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Semi;
use syn::{
    Attribute, Block, Expr, ExprBlock, FieldsNamed, FnArg, GenericParam, Generics, Ident,
    ImplItemMethod, Meta, MetaList, Pat, Stmt, Type,
};

pub fn output_token_stream(bundle: SMBundle, concurrent: bool) -> syn::parse::Result<TokenStream> {
    let mut token_stream = TokenStream::new();
    let mut impl_token_stream = TokenStream::new();

    let self_ty = get_self_ty(&bundle.sm);

    output_primary_stuff(&mut token_stream, &mut impl_token_stream, &bundle.sm);

    if concurrent {
        output_token_types_and_fns(&mut token_stream, &bundle)?;
    }

    output_other_fns(
        &bundle,
        &mut impl_token_stream,
        &bundle.extras.invariants,
        &bundle.extras.lemmas,
        &bundle.normal_fns,
    );

    let impl_decl = impl_decl_stream(&self_ty, &bundle.sm.generics);

    let final_code = quote! {
        #token_stream

        #impl_decl {
            #impl_token_stream
        }
    };

    return Ok(final_code);
}

pub fn get_self_ty(sm: &SM) -> Type {
    name_with_type_args(&sm.name, sm)
}

pub fn get_self_ty_double_colon(sm: &SM) -> Type {
    name_with_type_args_double_colon(&sm.name, sm)
}

pub fn name_with_type_args(name: &Ident, sm: &SM) -> Type {
    Type::Verbatim(match &sm.generics {
        None => quote! { #name },
        Some(gen) => {
            if gen.params.len() > 0 {
                //let ids = gen.params.iter().map(|gp|
                let args = get_generic_args(&gen.params);
                quote! { #name<#args> }
            } else {
                quote! { #name }
            }
        }
    })
}

pub fn name_with_type_args_double_colon(name: &Ident, sm: &SM) -> Type {
    Type::Verbatim(match &sm.generics {
        None => quote! { #name },
        Some(gen) => {
            if gen.params.len() > 0 {
                //let ids = gen.params.iter().map(|gp|
                let args = get_generic_args(&gen.params);
                quote! { #name::<#args> }
            } else {
                quote! { #name }
            }
        }
    })
}

pub fn get_generic_args(params: &Punctuated<GenericParam, syn::token::Comma>) -> TokenStream {
    let args = params.iter().map(|gp| {
        match gp {
            GenericParam::Type(type_param) => type_param.ident.clone(),
            _ => {
                // should have been checked already
                panic!("unsupported generic param type");
            }
        }
    });
    quote! { #(#args),* }
}

pub fn impl_decl_stream(self_ty: &Type, generics: &Option<Generics>) -> TokenStream {
    match generics {
        None => quote! { impl #self_ty },
        Some(gen) => {
            if gen.params.len() > 0 {
                let params = &gen.params;
                let where_clause = &gen.where_clause;
                quote! { impl<#params> #self_ty #where_clause }
            } else {
                let where_clause = &gen.where_clause;
                quote! { impl #self_ty #where_clause }
            }
        }
    }
}

// We delete the special state machine attributes, since Rust/Verus won't recognize them.

pub fn should_delete_attr(attr: &Attribute) -> bool {
    match attr.parse_meta() {
        Ok(Meta::Path(path)) | Ok(Meta::List(MetaList { path, .. })) => {
            path.is_ident("invariant")
                || path.is_ident("inductive")
                || path.is_ident("safety")
                || path.is_ident("transition")
                || path.is_ident("readonly")
                || path.is_ident("init")
                || path.is_ident("sharding")
        }
        _ => false,
    }
}

pub fn fix_attrs(attrs: &mut Vec<Attribute>) {
    let mut old_attrs = Vec::new();
    swap(&mut old_attrs, attrs);

    for attr in old_attrs {
        if !should_delete_attr(&attr) {
            attrs.push(attr);
        }
    }
}

pub fn fields_named_fix_attrs(fields_named: &mut FieldsNamed) {
    for field in fields_named.named.iter_mut() {
        fix_attrs(&mut field.attrs);
    }
}

pub fn output_primary_stuff(
    token_stream: &mut TokenStream,
    impl_token_stream: &mut TokenStream,
    sm: &SM,
) {
    let name = &sm.name;
    //let fields: Vec<TokenStream> = sm.fields.iter().map(field_to_tokens).collect();

    let mut fields_named = sm.fields_named_ast.clone();
    fields_named_fix_attrs(&mut fields_named);

    let gen = match &sm.generics {
        Some(gen) => quote! { #gen },
        None => TokenStream::new(),
    };

    // Note: #fields_named will include the braces.
    let code: TokenStream = quote! {
        pub struct #name #gen #fields_named
    };
    token_stream.extend(code);

    let self_ty = get_self_ty(&sm);

    for trans in &sm.transitions {
        let simplified_body = simplify_updates(sm, &trans.body, true);

        // Output the 'weak' transition relation.
        // (or for the 'Init' case, a single-state predicate).
        if trans.kind != TransitionKind::Readonly {
            let f = to_relation(&simplified_body, true /* weak */);
            let name = &trans.name;
            let rel_fn;
            if trans.kind == TransitionKind::Init {
                let args = post_params(&trans.params);
                rel_fn = quote! {
                    #[spec]
                    pub fn #name (#args) -> bool {
                        #f
                    }
                };
            } else {
                let args = self_post_params(&trans.params);
                rel_fn = quote! {
                    #[spec]
                    pub fn #name (#args) -> bool {
                        #f
                    }
                };
            }
            impl_token_stream.extend(rel_fn);
        }

        // Output the 'strong' transition relation.
        // Note that 'init' routines don't allow asserts, so there is no need for an
        // additional 'strong' relation.
        if trans.kind == TransitionKind::Transition {
            let params = self_post_params(&trans.params);
            let name = Ident::new(&(trans.name.to_string() + "_strong"), trans.name.span());

            let f = to_relation(&simplified_body, false /* weak */);

            let rel_fn = quote! {
                #[spec]
                pub fn #name (#params) -> bool {
                    #f
                }
            };
            impl_token_stream.extend(rel_fn);
        }

        // If necessary, output a lemma with proof obligations for the safety conditions.
        let simplified_body_no_updates = simplify_updates(sm, &trans.body, false);
        if has_any_assert(&simplified_body_no_updates) {
            assert!(trans.kind != TransitionKind::Init);
            let b = safety_condition_body(&simplified_body_no_updates);
            let name = Ident::new(&(trans.name.to_string() + "_asserts"), trans.name.span());
            let params = self_assoc_params(&self_ty, &trans.params);
            let b = match b {
                Some(b) => quote! { #b },
                None => TokenStream::new(),
            };
            impl_token_stream.extend(quote! {
                #[proof]
                pub fn #name(#params) {
                    crate::pervasive::assume(self.invariant());
                    #b
                }
            });
        }
    }
}

/// self, post: Self, params...
fn self_post_params(params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|arg| {
            let ident = &arg.ident;
            let ty = &arg.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        self,
        post: Self,
        #(#params),*
    };
}

// self: X, params...
fn self_assoc_params(ty: &Type, params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|arg| {
            let ident = &arg.ident;
            let ty = &arg.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        self: #ty,
        #(#params),*
    };
}

// post: Self, params...
fn post_params(params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|arg| {
            let ident = &arg.ident;
            let ty = &arg.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        post: Self,
        #(#params),*
    };
}

pub fn shardable_type_to_type(stype: &ShardableType) -> Type {
    match stype {
        ShardableType::Variable(ty) => ty.clone(),
        ShardableType::Constant(ty) => ty.clone(),
        ShardableType::NotTokenized(ty) => ty.clone(),
        ShardableType::Multiset(ty) => {
            Type::Verbatim(quote! { crate::pervasive::multiset::Multiset<#ty> })
        }
        ShardableType::Optional(ty) => {
            Type::Verbatim(quote! { crate::pervasive::option::Option<#ty> })
        }
        ShardableType::StorageOptional(ty) => {
            Type::Verbatim(quote! { crate::pervasive::option::Option<#ty> })
        }
    }
}

fn output_other_fns(
    bundle: &SMBundle,
    impl_token_stream: &mut TokenStream,
    invariants: &Vec<Invariant>,
    lemmas: &Vec<Lemma>,
    normal_fns: &Vec<ImplItemMethod>,
) {
    let inv_names = invariants.iter().map(|i| &i.func.sig.ident);
    let conj = if inv_names.len() == 0 {
        quote! { true }
    } else {
        quote! { #(self.#inv_names())&&* }
    };
    impl_token_stream.extend(quote! {
        #[spec]
        pub fn invariant(&self) -> ::std::primitive::bool {
            #conj
        }
    });

    for inv in invariants {
        impl_token_stream.extend(quote! { #[spec] });
        let mut f = inv.func.clone();
        fix_attrs(&mut f.attrs);
        f.to_tokens(impl_token_stream);
    }

    for inv in invariants {
        let inv_ident = &inv.func.sig.ident;
        let inv_name = inv_ident.to_string();
        let error_msg = format!("could not show invariant `{:}` on the `post` state", inv_name);
        let lemma_msg_ident = Ident::new(&format!("lemma_msg_{:}", inv_name), inv_ident.span());
        let self_ty = get_self_ty(&bundle.sm);
        impl_token_stream.extend(quote! {
            #[proof]
            #[verifier(custom_req_err(#error_msg))]
            #[verifier(external_body)]
            fn #lemma_msg_ident(s: #self_ty) {
                requires(s.#inv_ident());
                ensures(s.#inv_ident());
            }
        });
    }

    for lemma in lemmas {
        impl_token_stream.extend(quote! { #[proof] });
        let mut f = lemma.func.clone();
        lemma_update_body(bundle, lemma, &mut f);
        fix_attrs(&mut f.attrs);
        f.to_tokens(impl_token_stream);
    }
    for iim in normal_fns {
        iim.to_tokens(impl_token_stream);
    }
}

fn left_of_colon<'a>(fn_arg: &'a FnArg) -> &'a Pat {
    match fn_arg {
        FnArg::Receiver(_) => panic!("should have been ruled out by lemma well-formedness"),
        FnArg::Typed(pat_type) => &pat_type.pat,
    }
}

/// Add pre-conditions and post-conditions to the inductiveness lemma.
///
/// For 'init' routines:
///   requires(initialized(post, ...));
///   ensures(post.invariant());
///
/// For normal transitions:
///   requires(self.invariant() && transition(self, post, ...));
///   ensures(post.invariant());
///
/// For 'readonly' transitions, there is no need to prove inductiveness.
/// We should have already ruled out the existence of such lemmas.

fn lemma_update_body(bundle: &SMBundle, l: &Lemma, func: &mut ImplItemMethod) {
    // TODO give a more helpful error if the body already has requires/ensures

    let trans = get_transition(&bundle.sm.transitions, &l.purpose.transition.to_string())
        .expect("transition");

    let precondition = if trans.kind == TransitionKind::Init {
        let trans_name =
            Ident::new(&(l.purpose.transition.to_string()), l.purpose.transition.span());
        let trans_args: Vec<&Pat> = l.func.sig.inputs.iter().map(|i| left_of_colon(i)).collect();
        quote! { Self::#trans_name(#(#trans_args),*) }
    } else {
        let trans_name_strong = Ident::new(
            &(l.purpose.transition.to_string() + "_strong"),
            l.purpose.transition.span(),
        );
        let trans_args: Vec<&Pat> =
            l.func.sig.inputs.iter().skip(1).map(|i| left_of_colon(i)).collect();
        quote! { self.invariant() && self.#trans_name_strong(#(#trans_args),*) }
    };

    let mut stmts = vec![
        Stmt::Semi(
            Expr::Verbatim(quote! {
                ::builtin::requires(
                    #precondition
                )
            }),
            Semi { spans: [l.func.span()] },
        ),
        Stmt::Semi(
            Expr::Verbatim(quote! {
                ::builtin::ensures(
                    post.invariant()
                )
            }),
            Semi { spans: [l.func.span()] },
        ),
        Stmt::Expr(Expr::Block(ExprBlock {
            attrs: vec![],
            label: None,
            block: func.block.clone(),
        })),
    ];
    for inv in &bundle.extras.invariants {
        let inv_ident = &inv.func.sig.ident;
        let inv_name = inv_ident.to_string();
        let lemma_msg_ident = Ident::new(&format!("lemma_msg_{:}", inv_name), inv_ident.span());
        let span = l.func.span();
        stmts.push(Stmt::Semi(
            Expr::Verbatim(quote_spanned! { span =>
                Self::#lemma_msg_ident(post)
            }),
            Semi { spans: [l.func.span()] },
        ));
    }

    let new_block = Block { brace_token: func.block.brace_token.clone(), stmts: stmts };
    func.block = new_block;
}
