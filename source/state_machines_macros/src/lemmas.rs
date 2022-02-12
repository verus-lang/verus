#![allow(unused_imports)]

use crate::concurrency_tokens::output_token_types_and_fns;
use crate::parse_token_stream::{SMBundle};
use crate::weakest::{get_safety_conditions, to_weakest};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use crate::ast::{
    TransitionParam, Extras, Field, Invariant, Lemma, LemmaPurpose, ShardableType, Transition, TransitionKind,
    TransitionStmt, SM,
};
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Colon2;
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, FieldsNamed, FnArg, Ident, ImplItemMethod, Meta,
    MetaList, NestedMeta, Path, PathArguments, PathSegment, Type, Generics, GenericParam,
};
use crate::transitions::{has_any_assert, safety_condition_body};
use std::collections::HashMap;
use crate::to_token_stream::get_self_ty;

pub fn check_lemmas(bundle: &SMBundle) -> syn::parse::Result<()> {
    check_each_lemma_valid(bundle)?;
    check_no_dupe_lemmas(bundle)?;
    check_lemmas_cover_all_cases(bundle)?;

    Ok(())
}

fn check_each_lemma_valid(_bundle: &SMBundle) -> syn::parse::Result<()> {
    // TODO
    Ok(())
}

fn check_no_dupe_lemmas(_bundle: &SMBundle) -> syn::parse::Result<()> {
    // TODO
    Ok(())
}

fn check_lemmas_cover_all_cases(bundle: &SMBundle) -> syn::parse::Result<()> {
    let mut names = HashMap::new();
    for t in bundle.sm.transitions.iter() {
        if t.kind != TransitionKind::Readonly {
            names.insert(t.name.to_string().clone(), &t.args);
        }
    }

    for l in bundle.extras.lemmas.iter() {
        let name = l.purpose.transition.to_string();
        assert!(names.contains_key(&name));
        names.remove(&name);
    }

    // Iterate through 'transitions' again, so the error messages come out in
    // a deterministic order.
    let mut msgs = vec![];
    for t in bundle.sm.transitions.iter() {
        if t.kind != TransitionKind::Readonly {
            let name = t.name.to_string();
            match names.get(&name) {
                None => { }
                Some(fields) => {
                    let self_ty = get_self_ty(&bundle.sm);
                    let is_init = t.kind == TransitionKind::Init;
                    let params = transition_params_to_string(&self_ty, is_init, fields);
                    msgs.push(format!("    #[inductive({name:})]\n    fn {name:}_inductive({params:}) {{ }}\n"));
                }
            }
        }
    }

    if msgs.len() > 0 {
        return Err(Error::new(bundle.name.span(),
            format!("missing inductiveness proofs for {:} transition(s); try adding the following stubs:\n\n", msgs.len()) + &msgs.join("\n")));
    }

    Ok(())
}

fn transition_params_to_string(self_ty: &Type, is_init: bool, fields: &Vec<TransitionParam>) -> String {
    let mut v1 = vec![];
    if is_init {
        v1.push("self: ".to_string() + &self_ty.to_token_stream().to_string());
    }
    v1.push("post: ".to_string() + &self_ty.to_token_stream().to_string());
    v1.extend(fields.iter().map(|f|
        f.ident.to_string() + ": " + &f.ty.to_token_stream().to_string()
    ));
    v1.join(", ")
}
