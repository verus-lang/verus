//! Primary module for outputting the generated code.
//! This includes: the primary struct, the transition definitions,
//! invariant predicates, lemmas that prove inductiveness, and lemmas
//! that prove safety conditions (as given by the 'assert' statements).
//!
//! Concurrent-state-machine-specific stuff is in concurrency_tokens.rs

use crate::ast::{
    Invariant, Lemma, ShardableType, Transition, TransitionKind, TransitionParam, SM,
};
use crate::concurrency_tokens::output_token_types_and_fns;
use crate::lemmas::get_transition;
use crate::parse_token_stream::SMBundle;
use crate::safety_conditions::{has_any_assert_simpl_vec, safety_condition_body_simpl_vec};
use crate::simplification::simplify_ops;
use crate::to_relation::to_relation;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use std::collections::HashMap;
use std::mem::swap;
use syn_verus::parse;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::{
    AngleBracketedGenericArguments, Attribute, Block, Expr, ExprBlock, FnArg, FnArgKind, FnMode,
    GenericArgument, GenericParam, Generics, Ident, ImplItemMethod, Meta, MetaList, ModeProof,
    ModeSpec, Open, Pat, Path, PathArguments, PathSegment, Publish, Signature, Stmt, Type,
    TypePath,
};

pub fn output_token_stream(bundle: SMBundle, concurrent: bool) -> parse::Result<TokenStream> {
    let mut root_stream = TokenStream::new();
    let mut impl_stream = TokenStream::new();

    let self_ty = get_self_ty(&bundle.sm);

    let safety_condition_lemmas = output_primary_stuff(&mut root_stream, &mut impl_stream, &bundle);

    if concurrent {
        output_token_types_and_fns(&mut root_stream, &bundle, &safety_condition_lemmas)?;
    }

    output_other_fns(
        &bundle,
        &mut impl_stream,
        &bundle.extras.invariants,
        &bundle.extras.lemmas,
        &bundle.normal_fns,
    );

    let impl_decl = impl_decl_stream(&self_ty, &bundle.sm.generics);

    let sm_name = &bundle.sm.name;

    let final_code = quote! {
        #[allow(unused_parens)]
        pub mod #sm_name {
            use super::*;

            #root_stream

            #impl_decl {
                #impl_stream
            }
        }
    };

    return Ok(final_code);
}

pub fn get_self_ty(sm: &SM) -> Type {
    let name = Ident::new("State", sm.name.span());
    name_with_type_args(&name, sm)
}

fn get_step_ty(sm: &SM, is_init: bool) -> Type {
    let name = Ident::new(if is_init { "Config" } else { "Step" }, sm.name.span());
    name_with_type_args(&name, sm)
}

pub fn get_self_ty_turbofish(sm: &SM) -> Type {
    let name = Ident::new("State", sm.name.span());
    name_with_type_args_turbofish(&name, sm)
}

pub fn get_self_ty_turbofish_path(sm: &SM) -> Path {
    let name = Ident::new("State", sm.name.span());
    name_with_type_args_turbofish_path(&name, sm)
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

fn name_with_type_args_turbofish_path(name: &Ident, sm: &SM) -> Path {
    let span = name.span();
    let arguments = match &sm.generics {
        None => PathArguments::None,
        Some(gen) => {
            if gen.params.len() > 0 {
                let args = get_generic_args(&gen.params);
                PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                    colon2_token: Some(token::Colon2 { spans: [span, span] }),
                    lt_token: gen.lt_token.expect("expected lt token"),
                    args,
                    gt_token: gen.gt_token.expect("expected gt token"),
                })
            } else {
                PathArguments::None
            }
        }
    };

    let mut segments = Punctuated::<PathSegment, token::Colon2>::new();
    segments.push(PathSegment { ident: name.clone(), arguments });
    Path { leading_colon: None, segments }
}

pub fn name_with_type_args_turbofish(name: &Ident, sm: &SM) -> Type {
    let p = name_with_type_args_turbofish_path(name, sm);
    Type::Path(TypePath { qself: None, path: p })
}

pub fn get_generic_args(
    params: &Punctuated<GenericParam, token::Comma>,
) -> Punctuated<GenericArgument, token::Comma> {
    let mut args = Punctuated::<GenericArgument, token::Comma>::new();
    for gp in params.iter() {
        let id = match gp {
            GenericParam::Type(type_param) => type_param.ident.clone(),
            _ => {
                // should have been checked already
                panic!("unsupported generic param type");
            }
        };
        args.push(GenericArgument::Type(Type::Verbatim(quote! {#id})));
    }
    args
}

fn generic_components_for_fn(generics: &Option<Generics>) -> (TokenStream, TokenStream) {
    match generics {
        None => (TokenStream::new(), TokenStream::new()),
        Some(gen) => {
            if gen.params.len() > 0 {
                let params = &gen.params;
                let where_clause = &gen.where_clause;
                (quote! { <#params> }, quote! { #where_clause })
            } else {
                let where_clause = &gen.where_clause;
                (TokenStream::new(), quote! { #where_clause })
            }
        }
    }
}

pub fn impl_decl_stream(self_ty: &Type, generics: &Option<Generics>) -> TokenStream {
    match generics {
        None => {
            quote! { #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))] impl #self_ty }
        }
        Some(gen) => {
            if gen.params.len() > 0 {
                let params = &gen.params;
                let where_clause = &gen.where_clause;
                quote! { #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))] impl<#params> #self_ty #where_clause }
            } else {
                let where_clause = &gen.where_clause;
                quote! { #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))] impl #self_ty #where_clause }
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

pub fn set_mode_proof(sig: &mut Signature, span: Span) {
    match &sig.mode {
        FnMode::Proof(_mode_proof) => {
            return;
        }
        _ => {}
    }

    sig.mode = FnMode::Proof(ModeProof { proof_token: token::Proof { span } });
}

pub fn output_primary_stuff(
    root_stream: &mut TokenStream,
    impl_stream: &mut TokenStream,
    bundle: &SMBundle,
) -> HashMap<String, Ident> {
    let sm = &bundle.sm;
    let gen = match &sm.generics {
        Some(gen) => quote! { #gen },
        None => TokenStream::new(),
    };

    let fields: Vec<TokenStream> = sm
        .fields
        .iter()
        .map(|f| {
            let name = &f.name;
            let ty = shardable_type_to_type(f.type_span, &f.stype);
            quote_spanned! { f.name.span() =>
                pub #name: #ty
            }
        })
        .collect();

    let attrs = &bundle.sm.attrs;
    let code: TokenStream = quote_spanned! { sm.fields_named_ast.span() =>
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        #(#attrs)*
        pub struct State #gen {
            #(#fields),*
        }
    };
    root_stream.extend(code);

    let self_ty = get_self_ty(&sm);

    let mut safety_condition_lemmas = HashMap::new();

    for trans in &sm.transitions {
        // `simplify_ops` translates the transition by processing all the special ops
        // and turns them into the core transition primitives.
        // `to_relation` then takes that simplified transition and turns it into
        // a boolean predicate between `pre` and `post`.

        let simplified_body = simplify_ops(sm, &trans.body, trans.kind);

        // Output the 'weak' transition relation.
        // (or for the 'Init' case, a single-state predicate).

        if trans.kind != TransitionKind::Property {
            let f = to_relation(&simplified_body, true /* weak */);
            let name = &trans.name;
            let rel_fn;
            if trans.kind == TransitionKind::Init {
                let args = post_params(&trans.params);
                rel_fn = quote! {
                    #[cfg(verus_keep_ghost_body)]
                    #[verus::internal(verus_macro)]
                    #[verifier::spec]
                    #[verus::internal(open)] /* vattr */
                    pub fn #name (#args) -> ::core::primitive::bool {
                        ::builtin_macros::verus_proof_expr!({ #f })
                    }
                };
            } else {
                let args = pre_post_params(&trans.params);
                rel_fn = quote! {
                    #[cfg(verus_keep_ghost_body)]
                    #[verus::internal(verus_macro)]
                    #[verifier::spec]
                    #[verus::internal(open)] /* vattr */
                    pub fn #name (#args) -> ::core::primitive::bool {
                        ::builtin_macros::verus_proof_expr!({ #f })
                    }
                };
            }
            impl_stream.extend(rel_fn);
        }

        // Output the 'strong' transition relation.
        // Note that 'init' routines don't allow asserts, so there is no need for an
        // additional 'strong' relation.

        if trans.kind != TransitionKind::Init && trans.kind != TransitionKind::Property {
            let params = pre_post_params(&trans.params);
            let name = Ident::new(&(trans.name.to_string() + "_strong"), trans.name.span());

            let f = to_relation(&simplified_body, false /* weak */);

            let rel_fn = quote! {
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::spec]
                #[verus::internal(open)] /* vattr */
                pub fn #name (#params) -> ::core::primitive::bool {
                    ::builtin_macros::verus_proof_expr!({ #f })
                }
            };
            impl_stream.extend(rel_fn);
        }

        // Output the enabling condition (like 'weak' relation but without a 'post' argument)

        if trans.kind != TransitionKind::Init && trans.kind != TransitionKind::Property {
            let params = pre_params(&trans.params);
            let name = Ident::new(&(trans.name.to_string() + "_enabled"), trans.name.span());

            let f = crate::to_relation::to_is_enabled_condition_weak(&simplified_body);

            let rel_fn = quote! {
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::spec]
                #[verus::internal(open)] /* vattr */
                pub fn #name (#params) -> ::core::primitive::bool {
                    ::builtin_macros::verus_proof_expr!({ #f })
                }
            };
            impl_stream.extend(rel_fn);
        }
        if trans.kind == TransitionKind::Init {
            let params = just_params(&trans.params);
            let name = Ident::new(&(trans.name.to_string() + "_enabled"), trans.name.span());

            let f = crate::to_relation::to_is_enabled_condition_weak(&simplified_body);

            let rel_fn = quote! {
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::spec]
                #[verus::internal(open)] /* vattr */
                pub fn #name (#params) -> ::core::primitive::bool {
                    ::builtin_macros::verus_proof_expr!({ #f })
                }
            };
            impl_stream.extend(rel_fn);
        }

        // If necessary, output a lemma with proof obligations for the safety conditions.
        // Note that we specifically check for asserts on the _simplified_ transition AST,
        // not the original, because 'assert' statements may have been introduced in
        // simplificiation.

        if has_any_assert_simpl_vec(&simplified_body) {
            assert!(trans.kind != TransitionKind::Init);
            let b = safety_condition_body_simpl_vec(&simplified_body);
            let name = Ident::new(&(trans.name.to_string() + "_asserts"), trans.name.span());
            let params = pre_assoc_params(&self_ty, &trans.params);
            let b = match b {
                Some(b) => quote! { #b },
                None => TokenStream::new(),
            };
            impl_stream.extend(quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::proof]
                pub fn #name(#params) {
                    #vstd::prelude::assume_(pre.invariant());
                    ::builtin_macros::verus_proof_expr!({
                        #b
                    })
                }
            });

            safety_condition_lemmas.insert(trans.name.to_string(), name);
        }
    }

    let mut show_stream = TokenStream::new();
    output_step_datatype(root_stream, &mut show_stream, impl_stream, sm, false);
    output_step_datatype(root_stream, &mut show_stream, impl_stream, sm, true);
    if let Some(init_label) = &sm.init_label {
        root_stream.extend(quote! {
            ::builtin_macros::verus!{
                #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
                #init_label
            }
        });
        root_stream.extend(quote! {});
    }
    if let Some(transition_label) = &sm.transition_label {
        root_stream.extend(quote! {
            ::builtin_macros::verus!{
                #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
                #transition_label
            }
        });
    }
    root_stream.extend(quote! {
        pub mod show {
            use super::*;
            #show_stream
        }
    });

    let mut take_step_stream = TokenStream::new();
    output_take_step_fns(&mut take_step_stream, bundle, &safety_condition_lemmas);
    root_stream.extend(quote! {
        pub mod take_step {
            use super::*;
            #take_step_stream
        }
    });

    safety_condition_lemmas
}

fn output_take_step_fns(
    stream: &mut TokenStream,
    bundle: &SMBundle,
    safety_condition_lemmas: &HashMap<String, Ident>,
) {
    let sm = &bundle.sm;
    if sm.transition_label.is_some() {
        return; // TODO
    }

    for trans in &sm.transitions {
        if matches!(trans.kind, TransitionKind::Transition | TransitionKind::ReadonlyTransition) {
            let self_ty = get_self_ty(sm);
            let super_self_ty = Type::Verbatim(quote! { super::#self_ty });
            let params = pre_assoc_params(&super_self_ty, &trans.params);
            let args = pre_args(&trans.params);
            let args2 = pre_post_args(&trans.params);

            let (gen1, gen2) = generic_components_for_fn(&sm.generics);
            let tr_name = &trans.name;

            let tr_name_enabled =
                Ident::new(&(trans.name.to_string() + "_enabled"), trans.name.span());
            let tr_name_strong =
                Ident::new(&(trans.name.to_string() + "_strong"), trans.name.span());

            let extra_deps =
                crate::concurrency_tokens::get_extra_deps(bundle, trans, safety_condition_lemmas);

            //let step_args = just_args(&trans.params);
            stream.extend(quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::external_body] /* vattr */
                #[verifier::proof]
                pub fn #tr_name#gen1(#params) -> #super_self_ty #gen2 {
                    #vstd::prelude::requires(
                        super::State::#tr_name_enabled(#args) && pre.invariant()
                    );
                    #vstd::prelude::ensures(|post: #super_self_ty|
                        super::State::#tr_name_strong(#args2) && post.invariant()
                    );
                    #extra_deps
                    loop { }
                }

                // #[cfg(verus_macro_erase_ghost)]
                use bool as #tr_name;
            });
        }
        if matches!(trans.kind, TransitionKind::Init) {
            let self_ty = get_self_ty(sm);
            let super_self_ty = Type::Verbatim(quote! { super::#self_ty });

            let self_ty_turbo = get_self_ty_turbofish(sm);
            let super_self_ty_turbo = Type::Verbatim(quote! { super::#self_ty_turbo });

            let params = just_params(&trans.params);
            let args = just_args(&trans.params, false);
            let args2 = post_args(&trans.params);

            let (gen1, gen2) = generic_components_for_fn(&sm.generics);
            let tr_name = &trans.name;

            let tr_name_enabled =
                Ident::new(&(trans.name.to_string() + "_enabled"), trans.name.span());

            let extra_deps =
                crate::concurrency_tokens::get_extra_deps(bundle, trans, safety_condition_lemmas);

            stream.extend(quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::external_body] /* vattr */
                #[verifier::proof]
                pub fn #tr_name#gen1(#params) -> #super_self_ty #gen2 {
                    #vstd::prelude::requires(
                        #super_self_ty_turbo::#tr_name_enabled(#args)
                    );
                    #vstd::prelude::ensures(|post: #super_self_ty|
                        super::State::#tr_name(#args2) && post.invariant()
                    );
                    #extra_deps
                    loop { }
                }

                // #[cfg(verus_macro_erase_ghost)]
                use bool as #tr_name;
            });
        }
    }
}

fn output_step_datatype(
    root_stream: &mut TokenStream,
    show_stream: &mut TokenStream,
    impl_stream: &mut TokenStream,
    sm: &SM,
    is_init: bool,
) {
    let filter_fn = |t: &Transition| {
        if is_init {
            t.kind == TransitionKind::Init
        } else {
            t.kind == TransitionKind::Transition || t.kind == TransitionKind::ReadonlyTransition
        }
    };

    let type_name = if is_init { "Config" } else { "Step" };
    let type_ident = Ident::new(type_name, sm.name.span());

    let variants: Vec<TokenStream> = sm
        .transitions
        .iter()
        .filter(|t| filter_fn(t))
        .map(|t| {
            let p = step_params(sm, &t);
            let tr_name = &t.name;
            quote! { #tr_name(#p) }
        })
        .collect();

    let generics = &sm.generics;

    let self_ty = get_self_ty(sm);
    let step_ty = get_step_ty(sm, is_init);
    let attrs = &sm.attrs;

    root_stream.extend(quote! {
        #[allow(non_camel_case_types)]
        #[::builtin_macros::is_variant_no_deprecation_warning]
        #[::builtin_macros::verus_enum_synthesize]
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        #(#attrs)*
        pub enum #type_ident#generics {
            #(#variants,)*
            // We add this extra variant with the self_ty in order to avoid
            // 'unused type param' errors in the definition of Step or Config.
            dummy_to_use_type_params(#self_ty),
        }
    });

    let label_param;
    let label_arg;
    let use_label;
    let label_gen = sm.get_label_generics_opt(is_init);
    if is_init && sm.init_label.is_some() {
        label_param = quote! { init_label: InitLabel#label_gen, };
        label_arg = quote! { init_label, };
        use_label = true;
    } else if !is_init && sm.transition_label.is_some() {
        label_param = quote! { label: Label#label_gen, };
        label_arg = quote! { label, };
        use_label = true;
    } else {
        label_param = quote! {};
        label_arg = quote! {};
        use_label = false;
    }

    let arms: Vec<TokenStream> = sm
        .transitions
        .iter()
        .filter(|t| filter_fn(t))
        .map(|t| {
            let step_args = just_args(&t.params, use_label);
            let tr_args = if is_init {
                if use_label { post_label_args(&t.params) } else { post_args(&t.params) }
            } else {
                if use_label { pre_post_label_args(&t.params) } else { pre_post_args(&t.params) }
            };
            let tr_name = &t.name;
            quote! {
                #type_ident::#tr_name(#step_args) => Self::#tr_name(#tr_args),
            }
        })
        .collect();

    if is_init {
        impl_stream.extend(quote_vstd! { vstd =>
            #[cfg(verus_keep_ghost_body)]
            #[verifier::opaque] /* vattr */
            #[verus::internal(open)] /* vattr */
            #[verus::internal(verus_macro)]
            #[verifier::spec]
            pub fn init_by(post: #self_ty, #label_param step: #step_ty) -> ::core::primitive::bool {
                match step {
                    #(#arms)*
                    // The dummy step never corresponds to a valid transition.
                    #type_ident::dummy_to_use_type_params(_) => false,
                }
            }

            #[cfg(verus_keep_ghost_body)]
            #[verifier::opaque] /* vattr */
            #[verus::internal(open)] /* vattr */
            #[verus::internal(verus_macro)]
            #[verifier::spec]
            pub fn init(post: #self_ty, #label_param) -> ::core::primitive::bool {
                #vstd::prelude::exists(|step: #step_ty| Self::init_by(post, #label_arg step))
            }
        });
    } else {
        let arms_strong: Vec<TokenStream> = sm
            .transitions
            .iter()
            .filter(|t| filter_fn(t))
            .map(|t| {
                let step_args = just_args(&t.params, use_label);
                let tr_args = if use_label {
                    pre_post_label_args(&t.params)
                } else {
                    pre_post_args(&t.params)
                };

                let tr_name = &t.name;
                let tr_name_strong = Ident::new(&(tr_name.to_string() + "_strong"), tr_name.span());
                quote! {
                    #type_ident::#tr_name(#step_args) => Self::#tr_name_strong(#tr_args),
                }
            })
            .collect();

        impl_stream.extend(quote_vstd!{ vstd =>
            #[cfg(verus_keep_ghost_body)]
            #[verifier::opaque] /* vattr */
            #[verus::internal(open)] /* vattr */
            #[verus::internal(verus_macro)]
            #[verifier::spec]
            pub fn next_by(pre: #self_ty, post: #self_ty, #label_param step: #step_ty) -> ::core::primitive::bool {
                match step {
                    #(#arms)*
                    #type_ident::dummy_to_use_type_params(_) => false,
                }
            }

            #[cfg(verus_keep_ghost_body)]
            #[verifier::opaque] /* vattr */
            #[verus::internal(open)] /* vattr */
            #[verus::internal(verus_macro)]
            #[verifier::spec]
            pub fn next(pre: #self_ty, post: #self_ty, #label_param) -> ::core::primitive::bool {
                #vstd::prelude::exists(|step: #step_ty| Self::next_by(pre, post, #label_arg step))
            }

            #[cfg(verus_keep_ghost_body)]
            #[verifier::opaque] /* vattr */
            #[verus::internal(open)] /* vattr */
            #[verus::internal(verus_macro)]
            #[verifier::spec]
            pub fn next_strong_by(pre: #self_ty, post: #self_ty, #label_param step: #step_ty) -> ::core::primitive::bool {
                match step {
                    #(#arms_strong)*
                    #type_ident::dummy_to_use_type_params(_) => false,
                }
            }

            #[cfg(verus_keep_ghost_body)]
            #[verifier::opaque] /* vattr */
            #[verus::internal(open)] /* vattr */
            #[verus::internal(verus_macro)]
            #[verifier::spec]
            pub fn next_strong(pre: #self_ty, post: #self_ty, #label_param) -> ::core::primitive::bool {
                #vstd::prelude::exists(|step: #step_ty| Self::next_strong_by(pre, post, #label_arg step))
            }
        });
    }

    let super_self_ty = Type::Verbatim(quote! { super::#self_ty });

    let (gen1, gen2) = generic_components_for_fn(&sm.generics);

    for trans in &sm.transitions {
        if filter_fn(&trans) {
            let label_arg = if expect_first_param_is_label(sm, trans) {
                let id = &trans.params[0].name;
                quote! { , #id }
            } else {
                quote! {}
            };

            let tr_name = &trans.name;
            if is_init {
                let params = post_assoc_params(&super_self_ty, &trans.params);
                let args = post_args(&trans.params);

                //let step_args = just_args(&trans.params);
                show_stream.extend(quote_vstd! { vstd =>
                    #[cfg(verus_keep_ghost_body)]
                    #[verus::internal(verus_macro)]
                    #[verifier::external_body] /* vattr */
                    #[verifier::proof]
                    pub fn #tr_name#gen1(#params) #gen2 {
                        #vstd::prelude::requires(super::State::#tr_name(#args));
                        #vstd::prelude::ensures(super::State::init(post #label_arg));
                    }

                    // #[cfg(verus_macro_erase_ghost)]
                    use bool as #tr_name;
                });
            } else {
                let params = pre_post_assoc_params(&super_self_ty, &trans.params);
                let args = pre_post_args(&trans.params);
                //let step_args = just_args(&trans.params);
                show_stream.extend(quote_vstd! { vstd =>
                    #[cfg(verus_keep_ghost_body)]
                    #[verus::internal(verus_macro)]
                    #[verifier::external_body] /* vattr */
                    #[verifier::proof]
                    pub fn #tr_name#gen1(#params) #gen2 {
                        #vstd::prelude::requires(super::State::#tr_name(#args));
                        #vstd::prelude::ensures(super::State::next(pre, post #label_arg));
                    }

                    // #[cfg(verus_macro_erase_ghost)]
                    use bool as #tr_name;
                });
            }
        }
    }
}

/// pre: Self, post: Self, params...
fn pre_post_params(params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            let ty = &param.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        pre: Self,
        post: Self,
        #(#params),*
    };
}

/// pre: Self, post: Self, params...
fn pre_params(params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            let ty = &param.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        pre: Self,
        #(#params),*
    };
}

fn expect_first_param_is_label(sm: &SM, tr: &Transition) -> bool {
    match tr.kind {
        TransitionKind::Property => false,
        TransitionKind::Init => sm.init_label.is_some(),
        TransitionKind::Transition | TransitionKind::ReadonlyTransition => {
            sm.transition_label.is_some()
        }
    }
}

// params... (types only, no identifiers)
fn step_params(sm: &SM, tr: &Transition) -> TokenStream {
    let skip_n = if expect_first_param_is_label(sm, tr) { 1 } else { 0 };

    let params: Vec<TokenStream> = tr
        .params
        .iter()
        .skip(skip_n)
        .map(|param| {
            let ty = &param.ty;
            quote! { #ty }
        })
        .collect();
    return quote! {
        #(#params),*
    };
}

// pre: X, params...
fn pre_assoc_params(ty: &Type, params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            let ty = &param.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        pre: #ty,
        #(#params),*
    };
}

// post: X, params...
fn post_assoc_params(ty: &Type, params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            let ty = &param.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        post: #ty,
        #(#params),*
    };
}

// post: X, params...
fn pre_post_assoc_params(ty: &Type, params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            let ty = &param.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        pre: #ty,
        post: #ty,
        #(#params),*
    };
}

// post: Self, params...
fn post_params(params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            let ty = &param.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        post: Self,
        #(#params),*
    };
}

// params...
fn just_params(params: &Vec<TransitionParam>) -> TokenStream {
    let params: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            let ty = &param.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        #(#params),*
    };
}

// pre, args...
fn pre_args(params: &Vec<TransitionParam>) -> TokenStream {
    let args: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            quote! { #ident }
        })
        .collect();
    return quote! {
        pre,
        #(#args),*
    };
}

// pre, post, args...
fn pre_post_args(params: &Vec<TransitionParam>) -> TokenStream {
    let args: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            quote! { #ident }
        })
        .collect();
    return quote! {
        pre,
        post,
        #(#args),*
    };
}

fn pre_post_label_args(params: &Vec<TransitionParam>) -> TokenStream {
    let args: Vec<TokenStream> = params
        .iter()
        .skip(1)
        .map(|param| {
            let ident = &param.name;
            quote! { #ident }
        })
        .collect();
    return quote! {
        pre,
        post,
        label,
        #(#args),*
    };
}

// post, args...
fn post_args(params: &Vec<TransitionParam>) -> TokenStream {
    let args: Vec<TokenStream> = params
        .iter()
        .map(|param| {
            let ident = &param.name;
            quote! { #ident }
        })
        .collect();
    return quote! {
        post,
        #(#args),*
    };
}

fn post_label_args(params: &Vec<TransitionParam>) -> TokenStream {
    let args: Vec<TokenStream> = params
        .iter()
        .skip(1)
        .map(|param| {
            let ident = &param.name;
            quote! { #ident }
        })
        .collect();
    return quote! {
        post,
        init_label,
        #(#args),*
    };
}

// args...
fn just_args(params: &Vec<TransitionParam>, skip_first: bool) -> TokenStream {
    let args: Vec<TokenStream> = params
        .iter()
        .skip(if skip_first { 1 } else { 0 })
        .map(|param| {
            let ident = &param.name;
            quote! { #ident }
        })
        .collect();
    return quote! {
        #(#args),*
    };
}

pub fn shardable_type_to_type(span: Span, stype: &ShardableType) -> Type {
    match stype {
        ShardableType::Variable(ty) => ty.clone(),
        ShardableType::Constant(ty) => ty.clone(),
        ShardableType::NotTokenized(ty) => ty.clone(),
        ShardableType::Option(ty)
        | ShardableType::PersistentOption(ty)
        | ShardableType::StorageOption(ty) => {
            Type::Verbatim(quote_spanned! { span => ::core::option::Option<#ty> })
        }
        ShardableType::Set(ty) | ShardableType::PersistentSet(ty) => {
            Type::Verbatim(quote_spanned_vstd! { vstd, span => #vstd::set::Set<#ty> })
        }
        ShardableType::Map(key, val)
        | ShardableType::PersistentMap(key, val)
        | ShardableType::StorageMap(key, val) => {
            Type::Verbatim(quote_spanned_vstd! { vstd, span => #vstd::map::Map<#key, #val> })
        }
        ShardableType::Multiset(ty) => {
            Type::Verbatim(quote_spanned_vstd! { vstd, span => #vstd::multiset::Multiset<#ty> })
        }
        ShardableType::Count | ShardableType::PersistentCount => {
            Type::Verbatim(quote_spanned_vstd! { vstd, span => #vstd::prelude::nat })
        }
        ShardableType::Bool | ShardableType::PersistentBool => {
            Type::Verbatim(quote_spanned! { span => ::core::primitive::bool })
        }
    }
}

fn output_other_fns(
    bundle: &SMBundle,
    impl_stream: &mut TokenStream,
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
    impl_stream.extend(quote! {
        #[cfg(verus_keep_ghost_body)]
        #[verifier::spec]
        #[verus::internal(verus_macro)]
        #[verus::internal(open)] /* vattr */
        pub fn invariant(&self) -> ::core::primitive::bool {
            #conj
        }
    });

    for inv in invariants {
        let mut f = inv.func.clone();
        fix_attrs(&mut f.attrs);
        // TODO allow spec(checked) or something
        f.sig.mode = FnMode::Spec(ModeSpec { spec_token: token::Spec { span: inv.func.span() } });
        f.sig.publish = Publish::Open(Open { token: token::Open { span: inv.func.span() } });
        impl_stream.extend(quote! { #[cfg(verus_keep_ghost_body)] ::builtin_macros::verus!{ #f } });
    }

    for inv in invariants {
        let inv_ident = &inv.func.sig.ident;
        let inv_name = inv_ident.to_string();
        let error_msg = format!("could not show invariant `{:}` on the `post` state", inv_name);
        let lemma_msg_ident = Ident::new(&format!("lemma_msg_{:}", inv_name), inv_ident.span());
        let self_ty = get_self_ty(&bundle.sm);
        impl_stream.extend(quote_vstd! { vstd =>
            #[cfg(verus_keep_ghost_body)]
            #[verifier::custom_req_err(#error_msg)] /* vattr */
            #[verifier::external_body] /* vattr */
            #[verus::internal(verus_macro)]
            #[verifier::proof]
            fn #lemma_msg_ident(s: #self_ty) {
                #vstd::prelude::requires(s.#inv_ident());
                #vstd::prelude::ensures(s.#inv_ident());
            }
        });
    }

    for lemma in lemmas {
        let mut f = lemma.func.clone();
        lemma_update_body(bundle, lemma, &mut f);
        let span = f.sig.span(); // TODO better span choice
        set_mode_proof(&mut f.sig, span);
        fix_attrs(&mut f.attrs);
        impl_stream.extend(quote! {
          #[cfg(verus_keep_ghost_body)]
          ::builtin_macros::verus!{ #f }
        })
    }

    let mut normal_fn_stream = TokenStream::new();
    for iim in normal_fns {
        iim.to_tokens(&mut normal_fn_stream);
    }

    impl_stream.extend(quote! {
        ::builtin_macros::verus!{
            #normal_fn_stream
        }
    });
}

fn left_of_colon<'a>(fn_arg: &'a FnArg) -> &'a Pat {
    match &fn_arg.kind {
        FnArgKind::Receiver(_) => panic!("should have been ruled out by lemma well-formedness"),
        FnArgKind::Typed(pat_type) => &pat_type.pat,
    }
}

/// Add pre-conditions and post-conditions to the inductiveness lemma.
///
/// For 'init' routines:
///   requires(initialized(post, ...));
///   ensures(post.invariant());
///
/// For normal transitions:
///   requires(pre.invariant() && transition(pre, post, ...));
///   ensures(post.invariant());
///
/// For 'readonly' transitions, there is no need to prove inductiveness.
/// We should have already ruled out the existence of such lemmas.

fn lemma_update_body(bundle: &SMBundle, l: &Lemma, func: &mut ImplItemMethod) {
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
        let self_ty = get_self_ty_turbofish(&bundle.sm);
        let trans_args: Vec<&Pat> = l.func.sig.inputs.iter().map(|i| left_of_colon(i)).collect();
        quote! { pre.invariant() && #self_ty::#trans_name_strong(#(#trans_args),*) }
    };

    let mut stmts = vec![
        Stmt::Semi(
            Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::requires(
                    #precondition
                )
            }),
            token::Semi { spans: [l.func.span()] },
        ),
        Stmt::Semi(
            Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::ensures(
                    post.invariant()
                )
            }),
            token::Semi { spans: [l.func.span()] },
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
            token::Semi { spans: [l.func.span()] },
        ));
    }

    let new_block = Block { brace_token: func.block.brace_token.clone(), stmts: stmts };
    func.block = new_block;
}
