#![allow(unused_imports)]

use proc_macro2::TokenStream;
use crate::parse_token_stream::{SMAndFuncs, MaybeSM};
use syn::parse::{Parse, ParseStream};
use syn::{ImplItemMethod, braced, Ident, Error, FieldsNamed, Expr, Type, Meta, NestedMeta, Attribute, AttrStyle, MetaList, FnArg};
use syn::buffer::Cursor;
use proc_macro2::Span;
use syn::spanned::Spanned;
use smir::ast::{SM, Invariant, Lemma, LemmaPurpose, Transition, TransitionKind, TransitionStmt, Extras, Field, ShardableType};
use quote::{ToTokens, quote};

pub fn output_token_stream(sm_and_funcs: SMAndFuncs) -> TokenStream {
    let SMAndFuncs { normal_fns, sm: maybe_sm } = sm_and_funcs;

    let mut token_stream = TokenStream::new();
    let mut impl_token_stream = TokenStream::new();

    match &maybe_sm {
        MaybeSM::SM(sm) => {
            output_primary_stuff(&mut token_stream, &mut impl_token_stream, &sm);
            output_other_fns(&mut impl_token_stream, &sm.invariants, &sm.lemmas, normal_fns);
        }
        MaybeSM::Extras(ex) => {
            output_other_fns(&mut impl_token_stream, &ex.invariants, &ex.lemmas, normal_fns);
        }
    }

    let name = match maybe_sm {
        MaybeSM::SM(sm) => { sm.name }
        MaybeSM::Extras(ex) => { ex.name }
    };

    let final_code = quote! {
        #token_stream

        impl #name {
            #impl_token_stream
        }
    };

    return final_code;
}

pub fn output_primary_stuff(
    token_stream: &mut TokenStream,
    impl_token_stream: &mut TokenStream,
    sm: &SM<ImplItemMethod, Expr, Type>,
) {
    let name = &sm.name;
    let fields: Vec<TokenStream> = sm.fields.iter().map(field_to_tokens).collect();

    let code: TokenStream = quote! {
        pub struct #name {
            #( #fields ),*
        }
    };
    token_stream.extend(code);

    // We will fill in the 'inv' body later
    let inv_sig = quote! {
        #[spec]
        pub fn inv(&self) -> bool { panic!("to be determined"); }
    };
    impl_token_stream.extend(inv_sig);

    for tr in &sm.transitions {
        unimplemented!();
        //let tr_sig = quote! {
        //};
        //impl_token_stream.extend(tr_sig);
    }
}

fn shardable_type_to_type(stype: &ShardableType<Type>) -> Type {
    match stype {
        ShardableType::Variable(ty) => {
            ty.clone()
        }
    }
}

fn field_to_tokens(field: &Field<Type>) -> TokenStream {
    let name = &field.ident;
    let ty = shardable_type_to_type(&field.stype);
    return quote! {
        #[spec] pub #name: #ty
    };
}

fn output_other_fns(impl_token_stream: &mut TokenStream,
    invariants: &Vec<Invariant<ImplItemMethod>>,
    lemmas: &Vec<Lemma<ImplItemMethod>>,
    normal_fns: Vec<ImplItemMethod>,
) {
    for inv in invariants {
        inv.func.to_tokens(impl_token_stream);
    }
    for lemma in lemmas {
        lemma.func.to_tokens(impl_token_stream);
    }
    for iim in normal_fns {
        iim.to_tokens(impl_token_stream);
    }
}
