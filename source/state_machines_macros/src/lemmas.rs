use crate::ast::{Transition, TransitionKind, TransitionParam};
use crate::parse_token_stream::SMBundle;
use proc_macro2::Span;
use quote::{quote, ToTokens};
use std::collections::{HashMap, HashSet};
use syn_verus::parse;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::{
    Error, Expr, ExprCall, ExprPath, FnArg, FnArgKind, FnMode, Ident, Pat, PatIdent, PatType,
    ReturnType, Stmt, Type,
};

/// Check that the declarations of 'inductive' lemmas are well-formed.

pub fn check_lemmas(bundle: &SMBundle) -> parse::Result<()> {
    check_each_lemma_valid(bundle)?;
    if bundle.extras.invariants.len() > 0 {
        check_lemmas_cover_all_cases(bundle)?;
    }
    check_no_explicit_conditions(bundle)?;

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

/// Check that each lemma is valid by making sure it has the right arguments.
/// They should match token-by-token (since at this point we are incapable of more complex
/// type analysis) and be named the same.
///
/// Naturally, in the process, we check that each lemma actually names a transition
/// that exists. We also check that there are no duplicate lemmas.
///
/// Make sure the error message is helpful. On error, just tell the user exactly
/// what params they can copy-paste in.

fn check_each_lemma_valid(bundle: &SMBundle) -> parse::Result<()> {
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
            TransitionKind::ReadonlyTransition => {
                return Err(Error::new(
                    l.func.span(),
                    format!("'inductive' lemma does not make sense for a 'readonly' transition"),
                ));
            }
            TransitionKind::Property => {
                return Err(Error::new(
                    l.func.span(),
                    format!("'inductive' lemma does not make sense for a 'property' definition"),
                ));
            }
            TransitionKind::Init | TransitionKind::Transition => {}
        }

        match &l.func.sig.mode {
            FnMode::Default | FnMode::Proof(_) => {}
            FnMode::Spec(mode_spec) => {
                return Err(Error::new(
                    mode_spec.span(),
                    "an inductiveness lemma should be `proof`",
                ));
            }
            FnMode::SpecChecked(mode_spec_checked) => {
                return Err(Error::new(
                    mode_spec_checked.span(),
                    "an inductiveness lemma should be `proof`",
                ));
            }
            FnMode::Exec(mode_exec) => {
                return Err(Error::new(
                    mode_exec.span(),
                    "an inductiveness lemma should be `proof`",
                ));
            }
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

        let expected_params = get_expected_params(t);
        if let Some(err_span) =
            params_match(&expected_params, &l.func.sig.inputs, l.func.sig.span())
        {
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

/// For the lemma about an 'init' routine,
/// we expect params: `post: X, ...` where `...` are the transition params and X is the Self type.
/// For a 'transition' routine,
/// we expect params: `pre: X, post: X, ...`

fn get_expected_params(t: &Transition) -> Vec<TransitionParam> {
    let mut v = vec![];
    let self_ty = Type::Verbatim(quote! { Self });
    match &t.kind {
        TransitionKind::Init => {
            v.push(TransitionParam { name: Ident::new("post", self_ty.span()), ty: self_ty });
        }
        TransitionKind::Transition => {
            v.push(TransitionParam {
                name: Ident::new("pre", self_ty.span()),
                ty: self_ty.clone(),
            });
            v.push(TransitionParam { name: Ident::new("post", self_ty.span()), ty: self_ty });
        }
        TransitionKind::ReadonlyTransition | TransitionKind::Property => {
            panic!("case should have been ruled out earlier");
        }
    }
    v.extend(t.params.clone());
    v
}

/// If the params match, return None.
/// If not, return a span to error at. Pick the earliest span where a discrepancy is found.

fn params_match(
    expected: &Vec<TransitionParam>,
    actual: &Punctuated<FnArg, token::Comma>,
    sig_span: Span,
) -> Option<Span> {
    for (i, fn_arg) in actual.iter().enumerate() {
        if i >= expected.len() {
            return Some(actual[i].kind.span());
        }
        match fn_arg {
            FnArg { tracked: _, kind: FnArgKind::Receiver(_) } => {
                return Some(fn_arg.kind.span());
            }
            FnArg {
                tracked,
                kind: FnArgKind::Typed(PatType { attrs, pat, colon_token: _, ty }),
            } => {
                match tracked {
                    Some(token::Tracked { span }) => {
                        return Some(*span);
                    }
                    None => {}
                }

                if attrs.len() > 0 {
                    return Some(attrs[0].span());
                }

                if !pat_is_ident(pat, &expected[i].name) {
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
        return Some(sig_span);
    }

    return None;
}

/// Check if the `pat` is for the given ident, with no extra stuff.
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

/// Check that every transition has a corresponding 'inductive' lemma.
/// On error, print out a list of stubs that the user can directly copy-paste into their source.

fn check_lemmas_cover_all_cases(bundle: &SMBundle) -> parse::Result<()> {
    let mut names = HashMap::new();
    for t in bundle.sm.transitions.iter() {
        if t.kind.requires_invariant_lemma() {
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
        if t.kind.requires_invariant_lemma() {
            let name = t.name.to_string();
            match names.get(&name) {
                None => {}
                Some(fields) => {
                    let is_init = t.kind == TransitionKind::Init;
                    let params = transition_params_to_string(is_init, fields);
                    msgs.push(format!(
                        " #[inductive({name:})]\n fn {name:}_inductive({params:}) {{ }}\n"
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

fn ty_to_string(ty: &Type) -> String {
    let s = ty.to_token_stream().to_string();
    // Make the string look slightly better:
    let s = s.replace("< ", "<");
    let s = s.replace(" <", "<");
    let s = s.replace("> ", ">");
    let s = s.replace(" >", ">");
    let s = s.replace(":: ", "::");
    let s = s.replace(" ::", "::");
    s
}

fn params_to_string(params: &Vec<TransitionParam>) -> String {
    let mut v1 = vec![];
    v1.extend(params.iter().map(|f| f.name.to_string() + ": " + &ty_to_string(&f.ty)));
    v1.join(", ")
}

fn transition_params_to_string(is_init: bool, params: &Vec<TransitionParam>) -> String {
    let mut v1 = vec![];
    if !is_init {
        v1.push("pre: Self".to_string());
    }
    v1.push("post: Self".to_string());
    v1.extend(params.iter().map(|f| f.name.to_string() + ": " + &ty_to_string(&f.ty)));
    v1.join(", ")
}

/// Error if the user tried to add 'requires' or 'ensures' to an inductiveness lemma.

fn check_no_explicit_conditions(bundle: &SMBundle) -> parse::Result<()> {
    // Note that this check isn't strictly necessary. If the user tries to write something like:
    //
    //    fn foo() {
    //       requires(bar);
    //    }
    //
    // then it will get translated into:
    //
    //    fn foo() {
    //       requires(/* macro-generated pre-conditition */);
    //       ensures(/* macro-generated post-conditition */);
    //       {
    //           requires(bar);
    //       }
    //    }
    //
    // and Verus will reject the `requires` in the block.
    //
    // The goal of this error message is to just give a more user-friendly message.
    //
    // Strictly speaking, it isn't really even possible to do this check exactly right
    // (as it would require path-resolution) so we just do best-effort.

    for l in &bundle.extras.lemmas {
        if l.func.block.stmts.len() > 0 {
            let stmt = &l.func.block.stmts[0];
            match stmt {
                Stmt::Semi(Expr::Call(ExprCall { func, .. }), _) => match &**func {
                    Expr::Path(ExprPath { path, .. })
                        if path.is_ident("requires") || path.is_ident("ensures") =>
                    {
                        return Err(Error::new(
                            stmt.span(),
                            "header statement here was probably a mistake: in an inductiveness lemma, the precondition and postcondition are implicit, generated by the macro",
                        ));
                    }
                    _ => {}
                },
                _ => {}
            }
        }
    }

    Ok(())
}
