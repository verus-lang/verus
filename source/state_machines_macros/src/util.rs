use proc_macro2::TokenStream;
use syn_verus::parse;
use syn_verus::parse2;
use syn_verus::{Error, Expr, Pat, PatIdent, PatTuple};

// If there is at least one error, combine them all into one
// Else, return Ok(())

pub fn combine_errors_or_ok(errors: Vec<Error>) -> parse::Result<()> {
    let mut res = Ok(());
    for e in errors {
        match res {
            Ok(()) => {
                res = Err(e);
            }
            Err(e0) => {
                let mut e0 = e0;
                e0.combine(e);
                res = Err(e0);
            }
        }
    }
    res
}

pub fn combine_results(errors: Vec<parse::Result<()>>) -> parse::Result<()> {
    combine_errors_or_ok(
        errors
            .iter()
            .filter_map(|res| match res {
                Ok(_) => None,
                Err(e) => Some(e.clone()),
            })
            .collect(),
    )
}

pub fn expr_from_tokens(t: TokenStream) -> Expr {
    match parse2(t) {
        Err(_) => panic!("expr_from_tokens should not be called with user input"),
        Ok(e) => e,
    }
}

pub fn pat_from_tokens(t: TokenStream) -> Pat {
    match parse2(t) {
        Err(_) => panic!("pat_from_tokens should not be called with user input"),
        Ok(p) => p,
    }
}

pub fn is_definitely_irrefutable(pat: &Pat) -> bool {
    match pat {
        Pat::Ident(PatIdent { subpat: None, .. }) => true,
        Pat::Ident(PatIdent { subpat: Some((_, s)), .. }) => is_definitely_irrefutable(&**s),
        Pat::Tuple(PatTuple { elems, .. }) => {
            for elem in elems.iter() {
                if !is_definitely_irrefutable(elem) {
                    return false;
                }
            }
            return true;
        }
        Pat::Wild(_) => true,

        _ => false,
    }
}
