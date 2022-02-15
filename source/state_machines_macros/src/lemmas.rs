use crate::ast::{Transition, TransitionKind, TransitionParam, SM};
use crate::parse_token_stream::SMBundle;
use crate::to_token_stream::get_self_ty;
use proc_macro2::Span;
use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Comma;
use syn::{Error, FnArg, Ident, Pat, PatIdent, PatType, ReturnType, Type};

pub fn check_lemmas(bundle: &SMBundle) -> syn::parse::Result<()> {
    check_each_lemma_valid(bundle)?;
    check_lemmas_cover_all_cases(bundle)?;

    Ok(())
}

pub fn get_transition<'a>(
    transitions: &'a Vec<Transition>,
    name: &String,
) -> Option<&'a Transition> {
    for t in transitions.iter() {
        if t.name.to_string() == *name {
            return Some(t);
        }
    }
    None
}

fn check_each_lemma_valid(bundle: &SMBundle) -> syn::parse::Result<()> {
    let mut seen_lemmas = HashSet::new();

    for l in &bundle.extras.lemmas {
        let name = l.purpose.transition.to_string();
        if seen_lemmas.contains(&name) {
            return Err(Error::new(
                l.func.span(),
                format!("duplicate 'inductive' lemma for transition `{name:}`"),
            ));
        }

        seen_lemmas.insert(name.clone());

        let t = match get_transition(&bundle.sm.transitions, &name) {
            None => {
                return Err(Error::new(
                    l.func.span(),
                    format!("could not find transition `{name:}`"),
                ));
            }
            Some(t) => t,
        };

        match &t.kind {
            TransitionKind::Readonly => {
                return Err(Error::new(
                    l.func.sig.generics.span(),
                    format!("'inductive' lemma does not make sense for a 'readonly' transition"),
                ));
            }
            _ => {}
        }

        if l.func.sig.generics.params.len() > 0 {
            return Err(Error::new(
                l.func.sig.generics.span(),
                format!("'inductive' lemma should have no generic parameters"),
            ));
        }

        match &l.func.sig.output {
            ReturnType::Default => {}
            _ => {
                return Err(Error::new(
                    l.func.sig.output.span(),
                    format!("'inductive' lemma should have no return type"),
                ));
            }
        }

        let expected_params = get_expected_params(&bundle.sm, t);
        if let Some(err_span) = params_match(&expected_params, &l.func.sig.inputs) {
            return Err(Error::new(
                err_span,
                format!(
                    "params for 'inductive' lemma should be: `{:}`",
                    params_to_string(&expected_params)
                ),
            ));
        }
    }

    Ok(())
}

fn get_expected_params(sm: &SM, t: &Transition) -> Vec<TransitionParam> {
    let mut v = vec![];
    let self_ty = get_self_ty(sm);
    match &t.kind {
        TransitionKind::Init => {
            v.push(TransitionParam { ident: Ident::new("post", self_ty.span()), ty: self_ty });
        }
        TransitionKind::Transition => {
            v.push(TransitionParam {
                ident: Ident::new("self", self_ty.span()),
                ty: self_ty.clone(),
            });
            v.push(TransitionParam { ident: Ident::new("post", self_ty.span()), ty: self_ty });
        }
        TransitionKind::Readonly => {
            panic!("case should have been ruled out earlier");
        }
    }
    v.extend(t.params.clone());
    v
}

// If yes, return None
// if no, return a span to error at
fn params_match(
    expected: &Vec<TransitionParam>,
    actual: &Punctuated<FnArg, Comma>,
) -> Option<Span> {
    for (i, fn_arg) in actual.iter().enumerate() {
        if i >= expected.len() {
            return Some(actual[i].span());
        }
        match fn_arg {
            FnArg::Receiver(_) => {
                return Some(fn_arg.span());
            }
            FnArg::Typed(PatType { attrs, pat, colon_token: _, ty }) => {
                if attrs.len() > 0 {
                    return Some(attrs[0].span());
                }

                if !pat_is_ident(pat, &expected[i].ident) {
                    return Some(pat.span());
                }

                // Compare as strings (using == would check the spans as well)
                if ty.to_token_stream().to_string() != expected[i].ty.to_token_stream().to_string()
                {
                    return Some(ty.span());
                }
            }
        }
    }

    if actual.len() != expected.len() {
        return Some(actual.span());
    }

    return None;
}

fn pat_is_ident(pat: &Pat, ident: &Ident) -> bool {
    match pat {
        Pat::Ident(PatIdent {
            attrs,
            by_ref: None,
            mutability: None,
            ident: id0,
            subpat: None,
        }) if attrs.len() == 0 && id0.to_string() == ident.to_string() => true,
        _ => false,
    }
}

fn check_lemmas_cover_all_cases(bundle: &SMBundle) -> syn::parse::Result<()> {
    let mut names = HashMap::new();
    for t in bundle.sm.transitions.iter() {
        if t.kind != TransitionKind::Readonly {
            names.insert(t.name.to_string().clone(), &t.params);
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
                None => {}
                Some(fields) => {
                    let self_ty = get_self_ty(&bundle.sm);
                    let is_init = t.kind == TransitionKind::Init;
                    let params = transition_params_to_string(&self_ty, is_init, fields);
                    msgs.push(format!(
                        "    #[inductive({name:})]\n    fn {name:}_inductive({params:}) {{ }}\n"
                    ));
                }
            }
        }
    }

    if msgs.len() > 0 {
        return Err(Error::new(
            bundle.name.span(),
            format!(
                "missing inductiveness proofs for {:} transition(s); try adding the following stubs:\n\n",
                msgs.len()
            ) + &msgs.join("\n"),
        ));
    }

    Ok(())
}

fn params_to_string(params: &Vec<TransitionParam>) -> String {
    let mut v1 = vec![];
    v1.extend(
        params.iter().map(|f| f.ident.to_string() + ": " + &f.ty.to_token_stream().to_string()),
    );
    v1.join(", ")
}

fn transition_params_to_string(
    self_ty: &Type,
    is_init: bool,
    params: &Vec<TransitionParam>,
) -> String {
    let mut v1 = vec![];
    if !is_init {
        v1.push("self: ".to_string() + &self_ty.to_token_stream().to_string());
    }
    v1.push("post: ".to_string() + &self_ty.to_token_stream().to_string());
    v1.extend(
        params.iter().map(|f| f.ident.to_string() + ": " + &f.ty.to_token_stream().to_string()),
    );
    v1.join(", ")
}
