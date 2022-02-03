#![allow(unused_imports)]

use crate::concurrency_tokens::output_token_types_and_fns;
use crate::parse_token_stream::{MaybeSM, SMAndFuncs};
use crate::weakest::{get_safety_conditions, to_weakest};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use smir::ast::{
    Arg, Extras, Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind,
    TransitionStmt, SM,
};
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Colon2;
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, FieldsNamed, FnArg, Ident, ImplItemMethod, Meta,
    MetaList, NestedMeta, Path, PathArguments, PathSegment, Type,
};

pub fn output_token_stream(sm_and_funcs: SMAndFuncs, concurrent: bool) -> syn::parse::Result<TokenStream> {
    let SMAndFuncs { normal_fns, sm: maybe_sm } = sm_and_funcs;

    let mut token_stream = TokenStream::new();
    let mut impl_token_stream = TokenStream::new();

    match &maybe_sm {
        MaybeSM::SM(sm, fields_named, trans_fns) => {
            output_primary_stuff(
                &mut token_stream,
                &mut impl_token_stream,
                &sm,
                &fields_named,
                trans_fns,
            );
            output_other_fns(&mut impl_token_stream, &sm.invariants, &sm.lemmas, normal_fns);

            if concurrent {
                output_token_types_and_fns(&mut token_stream, sm)?;
            }
        }
        MaybeSM::Extras(ex) => {
            output_other_fns(&mut impl_token_stream, &ex.invariants, &ex.lemmas, normal_fns);
        }
    }

    let name = match maybe_sm {
        MaybeSM::SM(sm, _, _) => sm.name,
        MaybeSM::Extras(ex) => ex.name,
    };

    let final_code = quote! {
        #token_stream

        impl #name {
            #impl_token_stream
        }
    };

    return Ok(final_code);
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
    sm: &SM<Span, Ident, ImplItemMethod, Expr, Type>,
    fields_named: &FieldsNamed,
    trans_fns: &Vec<ImplItemMethod>,
) {
    let name = &sm.name;
    //let fields: Vec<TokenStream> = sm.fields.iter().map(field_to_tokens).collect();

    let mut fields_named = fields_named.clone();
    fields_named_fix_attrs(&mut fields_named);

    // Note: #fields_named will include the braces.
    let code: TokenStream = quote! {
        #[verifier(state_machine_struct)]
        pub struct #name #fields_named
    };
    token_stream.extend(code);

    // We will fill in the 'inv' body later
    let inv_sig = quote! {
        #[spec]
        pub fn invariant(&self) -> bool {
            ::builtin::state_machine_ops::to_be_determined()
        }
    };
    impl_token_stream.extend(inv_sig);

    /*
    for trans_fn in trans_fns {
        let mut f = trans_fn.clone();
        fix_attrs(&mut f.attrs);
        f.to_tokens(impl_token_stream);
    }
    */

    for trans in &sm.transitions {
        let mut strong_rel_idents: Vec<String> = Vec::new();

        if trans.kind != TransitionKind::Readonly {
            let f = to_weakest(sm, trans);
            let name = &trans.name;
            let rel_fn;
            if trans.kind == TransitionKind::Init {
                let args = post_params(&trans.args);
                rel_fn = quote! {
                    #[spec]
                    #[verifier(state_machine_fn(init(#name)))]
                    pub fn #name (#args) -> bool {
                        #f
                    }
                };
            } else {
                let args = self_post_params(&trans.args);
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
            let args = self_params(&trans.args);
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
            strong_rel_idents.push(name.to_string());
        }

        if trans.kind == TransitionKind::Transition {
            let params = self_post_params(&trans.args);
            let name = Ident::new(&(trans.name.to_string() + "_strong"), trans.name.span());

            let base_name = &trans.name;
            let args = lone_args(&trans.args);
            let p_args = post_args(&trans.args);

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
    }
}

fn self_post_params(args: &Vec<Arg<Ident, Type>>) -> TokenStream {
    let args: Vec<TokenStream> = args
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
        #(#args),*
    };
}

fn self_params(args: &Vec<Arg<Ident, Type>>) -> TokenStream {
    let args: Vec<TokenStream> = args
        .iter()
        .map(|arg| {
            let ident = &arg.ident;
            let ty = &arg.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        self,
        #(#args),*
    };
}

fn post_params(args: &Vec<Arg<Ident, Type>>) -> TokenStream {
    let args: Vec<TokenStream> = args
        .iter()
        .map(|arg| {
            let ident = &arg.ident;
            let ty = &arg.ty;
            quote! { #ident: #ty }
        })
        .collect();
    return quote! {
        post: Self,
        #(#args),*
    };
}

fn post_args(args: &Vec<Arg<Ident, Type>>) -> TokenStream {
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

fn lone_args(args: &Vec<Arg<Ident, Type>>) -> TokenStream {
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

fn shardable_type_to_type(stype: &ShardableType<Type>) -> Type {
    match stype {
        ShardableType::Variable(ty) => ty.clone(),
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
    invariants: &Vec<Invariant<ImplItemMethod>>,
    lemmas: &Vec<Lemma<Ident, ImplItemMethod>>,
    normal_fns: Vec<ImplItemMethod>,
) {
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
