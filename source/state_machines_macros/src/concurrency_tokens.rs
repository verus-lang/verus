#![allow(unused_imports)]

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

fn inst_type_name(sm_name: &Ident) -> Ident {
    let name = sm_name.to_string() + "_Instance";
    Ident::new(&name, sm_name.span())
}

fn field_token_type_name(sm_name: &Ident, field: &Field<Ident, Type>) -> Ident {
    let name = sm_name.to_string() + "_" + &field.ident.to_string();
    Ident::new(&name, field.ident.span())
}

fn field_token_field_name(field: &Field<Ident, Type>) -> Ident {
    field.ident.clone()
}

fn field_token_field_type(field: &Field<Ident, Type>) -> Type {
    match &field.stype {
        ShardableType::Variable(ty) => ty.clone(),
    }
}

fn instance_struct_stream(sm: &SM<Span, Ident, ImplItemMethod, Expr, Type>) -> TokenStream {
    let insttype = inst_type_name(&sm.name);
    return quote! {
        #[spec]
        #[allow(non_camel_case_types)]
        pub struct #insttype {
            #[spec] pub id: ::builtin::int,
        }
    }
}

fn token_struct_stream(sm_name: &Ident, field: &Field<Ident, Type>) -> TokenStream {
    let tokenname = field_token_type_name(sm_name, field);
    let fieldname = field_token_field_name(field);
    let fieldtype = field_token_field_type(field);
    let insttype = inst_type_name(sm_name);

    return quote! {
        #[proof]
        #[verifier(unforgeable)]
        #[allow(non_camel_case_types)]
        pub struct #tokenname {
            #[spec] pub instance: #insttype,
            #[spec] pub #fieldname: #fieldtype,
        }
    };
}

pub fn output_token_types_and_fns(token_stream: &mut TokenStream, sm: &SM<Span, Ident, ImplItemMethod, Expr, Type>) {
    token_stream.extend(instance_struct_stream(sm));
    for field in &sm.fields {
        token_stream.extend(token_struct_stream(&sm.name, field));
    }
}
