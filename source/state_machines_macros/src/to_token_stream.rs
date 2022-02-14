#![allow(unused_imports)]

use crate::ast::{
    Extras, Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind,
    TransitionParam, TransitionStmt, SM,
};
use crate::concurrency_tokens::output_token_types_and_fns;
use crate::parse_token_stream::SMBundle;
use crate::transitions::{has_any_assert, safety_condition_body};
use crate::weakest::{get_safety_conditions, to_weakest};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Colon2;
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, FieldsNamed, FnArg, GenericParam, Generics, Ident,
    ImplItemMethod, Meta, MetaList, NestedMeta, Path, PathArguments, PathSegment, Type,
};

pub fn output_token_stream(bundle: SMBundle, concurrent: bool) -> syn::parse::Result<TokenStream> {
    let mut token_stream = TokenStream::new();
    let mut impl_token_stream = TokenStream::new();

    let self_ty = get_self_ty(&bundle.sm);

    output_primary_stuff(&mut token_stream, &mut impl_token_stream, &bundle.sm);

    if concurrent {
        output_token_types_and_fns(&mut token_stream, &bundle.sm)?;
    }

    output_other_fns(
        &mut impl_token_stream,
        &bundle.extras.invariants,
        &bundle.extras.lemmas,
        bundle.normal_fns,
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
    let name = &sm.name;
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

pub fn fix_attr(attr: &mut Attribute) {
    let should_wrap_in_verified = match attr.parse_meta() {
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
    };

    if should_wrap_in_verified {
        let span = attr.span();
        let mut old_toks = attr.path.to_token_stream();
        old_toks.extend(attr.tokens.clone());
        let toks = quote_spanned! {span =>
            (state_machine_fn(#old_toks))
        };
        let mut segs = Punctuated::<PathSegment, Colon2>::new();
        segs.push(PathSegment {
            ident: Ident::new("verifier", span),
            arguments: PathArguments::None,
        });
        let p = Path { leading_colon: None, segments: segs };

        attr.tokens = toks;
        attr.path = p;
    }
}

pub fn fix_attrs(attrs: &mut Vec<Attribute>) {
    for attr in attrs.iter_mut() {
        fix_attr(attr);
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
        //#[verifier(state_machine_struct)]
        pub struct #name #gen #fields_named
    };
    token_stream.extend(code);

    let self_ty = get_self_ty(&sm);

    for trans in &sm.transitions {
        let mut strong_rel_idents: Vec<Ident> = Vec::new();

        if trans.kind != TransitionKind::Readonly {
            let f = to_weakest(sm, trans);
            let name = &trans.name;
            let rel_fn;
            if trans.kind == TransitionKind::Init {
                let args = post_params(&trans.params);
                rel_fn = quote! {
                    #[spec]
                    #[verifier(state_machine_fn(init(#name)))]
                    pub fn #name (#args) -> bool {
                        #f
                    }
                };
            } else {
                let args = self_post_params(&trans.params);
                rel_fn = quote! {
                    #[spec]
                    #[verifier(state_machine_fn(transition(#name)))]
                    pub fn #name (#args) -> bool {
                        #f
                    }
                };
            }
            impl_token_stream.extend(rel_fn);
        }

        for (i, safety_cond) in get_safety_conditions(&trans.body).iter().enumerate() {
            let args = self_params(&trans.params);
            let idx = i + 1;
            let name = Ident::new(
                &(trans.name.to_string() + "_safety_" + &idx.to_string()),
                trans.name.span(),
            );
            let idx_lit = syn::LitInt::new(&idx.to_string(), trans.name.span());
            let rel_fn = quote! {
                #[spec]
                #[verifier(state_machine_fn(safety_condition(#name, #idx_lit)))]
                pub fn #name (#args) -> bool {
                    #safety_cond
                }
            };
            impl_token_stream.extend(rel_fn);
            strong_rel_idents.push(name);
        }

        if trans.kind == TransitionKind::Transition {
            let params = self_post_params(&trans.params);
            let name = Ident::new(&(trans.name.to_string() + "_strong"), trans.name.span());

            let base_name = &trans.name;
            let args = lone_args(&trans.params);
            let p_args = post_args(&trans.params);

            let mut conjuncts = vec![quote! {
                self.#base_name(#p_args)
            }];
            for ident in strong_rel_idents {
                conjuncts.push(quote! {
                    self.#ident(#args)
                });
            }

            let rel_fn = quote! {
                #[spec]
                pub fn #name (#params) -> bool {
                    #(#conjuncts)&&*
                }
            };
            impl_token_stream.extend(rel_fn);
        }

        if has_any_assert(&trans.body) {
            let b = safety_condition_body(&trans.body);
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

// self, params...
fn self_params(params: &Vec<TransitionParam>) -> TokenStream {
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

fn post_args(args: &Vec<TransitionParam>) -> TokenStream {
    let args: Vec<TokenStream> = args
        .iter()
        .map(|arg| {
            let ident = &arg.ident;
            quote! { #ident }
        })
        .collect();
    return quote! {
        post,
        #(#args),*
    };
}

fn lone_args(args: &Vec<TransitionParam>) -> TokenStream {
    let args: Vec<TokenStream> = args
        .iter()
        .map(|arg| {
            let ident = &arg.ident;
            quote! { #ident }
        })
        .collect();
    return quote! {
        #(#args),*
    };
}

pub fn shardable_type_to_type(stype: &ShardableType<Type>) -> Type {
    match stype {
        ShardableType::Variable(ty) => ty.clone(),
        ShardableType::Constant(ty) => ty.clone(),
    }
}

/*
fn field_to_tokens(field: &Field<Ident, Type>) -> TokenStream {
    let name = &field.ident;
    let ty = shardable_type_to_type(&field.stype);
    return quote! {
        #[spec] pub #name: #ty
    };
}
*/

fn output_other_fns(
    impl_token_stream: &mut TokenStream,
    invariants: &Vec<Invariant>,
    lemmas: &Vec<Lemma>,
    normal_fns: Vec<ImplItemMethod>,
) {
    let inv_names = invariants.iter().map(|i| &i.func.sig.ident);
    impl_token_stream.extend(quote! {
        #[spec]
        pub fn invariant(&self) -> bool {
            #(self.#inv_names())&&*
        }
    });

    for inv in invariants {
        impl_token_stream.extend(quote! { #[spec] });
        let mut f = inv.func.clone();
        fix_attrs(&mut f.attrs);
        f.to_tokens(impl_token_stream);
    }
    for lemma in lemmas {
        impl_token_stream.extend(quote! { #[proof] });
        let mut f = lemma.func.clone();
        fix_attrs(&mut f.attrs);
        f.to_tokens(impl_token_stream);
    }
    for iim in normal_fns {
        iim.to_tokens(impl_token_stream);
    }
}
