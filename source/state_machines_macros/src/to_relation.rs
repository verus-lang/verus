use crate::ast::{Arm, SimplStmt, SplitKind, TransitionStmt};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn_verus::spanned::Spanned;
use syn_verus::Expr;

/// Converts a transition description into a relation between `pre` and `post`.
/// Overall, this process has two steps:
///
/// 1. Process all 'update' statements and special ops, turning them into
///    require, assert, and postcondition operations. (See `simplification.rs`.)
/// 2. Walk the tree and straightforwardly convert it to a relation.
///
/// This function performs step (2) (and it assumes that step (1) has already been applied.
/// See `simplification.rs`.)
///
/// There are actually two different relations we can form, the "weak" relation and
/// the "strong" one.
///
/// These differ only in how they handle "assert" statements. (Thus if there are no assert
/// statements, then the two versions are the same.) In short, the 'strong' version treats
/// an 'assert' like it does any other enabling condition, while the 'weak' version puts
/// the 'asserts' on the _left_ side of the implication.
///
/// For example, consider a transition like,
///
///   require(A);
///   assert(B);
///   require(C);
///
/// Then the weak relation would become
///
///   A && (B ==> C)
///
/// While the strong relation would become simply,
///
///   A && B && C
///
/// Note that we require the user to prove that any asserts follow from the invariant.
/// (In this case, that means showing that (Inv && A ==> B).
/// Thus, subject to the invariant, the weak & strong versions will actually be equivalent.

pub fn to_relation(sops: &Vec<SimplStmt>, weak: bool) -> TokenStream {
    match to_relation_vec(sops, None, weak) {
        Some(e) => e,
        None => quote! { true },
    }
}

// Recursive traversal, post-order.

fn to_relation_vec(
    sops: &Vec<SimplStmt>,
    p: Option<TokenStream>,
    weak: bool,
) -> Option<TokenStream> {
    let let_skip_brace = sops.len() == 1;
    let mut p = p;
    for e in sops.iter().rev() {
        p = to_relation_stmt(e, p, weak, let_skip_brace);
    }
    p
}

fn to_relation_stmt(
    sop: &SimplStmt,
    p: Option<TokenStream>,
    weak: bool,
    let_skip_brace: bool,
) -> Option<TokenStream> {
    match sop {
        SimplStmt::Let(_span, pat, ty, e, child) => {
            let x = to_relation_vec(child, None, weak);
            let ty_tokens = match ty {
                None => TokenStream::new(),
                Some(ty) => quote! { : #ty },
            };
            let t = match x {
                None => None,
                Some(r) => {
                    if let_skip_brace {
                        Some(quote! { let #pat #ty_tokens = #e; #r })
                    } else {
                        Some(quote! { { let #pat #ty_tokens = #e; #r } })
                    }
                }
            };
            // note this strategy is going to be quadratic in nesting depth or something
            if weak {
                conjunct_opt(t, impl_opt(asserts_to_single_predicate_simpl(sop), p))
            } else {
                conjunct_opt(t, p)
            }
        }
        SimplStmt::Split(_span, SplitKind::If(cond), es) => {
            assert!(es.len() == 2);
            let x1 = to_relation_vec(&es[0], None, weak);
            let x2 = to_relation_vec(&es[1], None, weak);
            let t = match (x1, x2) {
                (None, None) => None,
                (Some(e1), None) => Some(quote! { ::builtin::imply(#cond, #e1) }),
                (None, Some(e2)) => Some(quote! { ::builtin::imply(!(#cond), #e2) }),
                (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
            };
            // note this strategy is going to be quadratic in nesting depth or something
            if weak {
                conjunct_opt(t, impl_opt(asserts_to_single_predicate_simpl(sop), p))
            } else {
                conjunct_opt(t, p)
            }
        }
        SimplStmt::Split(span, SplitKind::Match(match_e, arms), es) => {
            let opts: Vec<Option<TokenStream>> =
                es.iter().map(|e| to_relation_vec(e, None, weak)).collect();
            let t = if opts.iter().any(|o| o.is_some()) {
                let cases: Vec<Expr> = opts
                    .into_iter()
                    .map(|o| match o {
                        None => Expr::Verbatim(quote! {true}),
                        Some(tokens) => Expr::Verbatim(tokens),
                    })
                    .collect();
                let m = emit_match(*span, match_e, arms, &cases);
                Some(quote! {#m})
            } else {
                None
            };

            if weak {
                conjunct_opt(t, impl_opt(asserts_to_single_predicate_simpl(sop), p))
            } else {
                conjunct_opt(t, p)
            }
        }
        SimplStmt::Split(..) => {
            panic!("this SplitKind should have been translated out");
        }
        SimplStmt::PostCondition(_span, e) | SimplStmt::Require(_span, e) => match p {
            None => Some(quote_spanned! { e.span() => (#e) }),
            Some(r) => Some(quote_spanned! { e.span() => ((#e) && #r) }),
        },
        SimplStmt::Assert(_span, e, _) => {
            if weak {
                match p {
                    None => None,
                    Some(r) => Some(quote! { ::builtin::imply(#e, #r) }),
                }
            } else {
                match p {
                    None => Some(quote_spanned! { e.span() => (#e) }),
                    Some(r) => Some(quote_spanned! { e.span() => ((#e) && (#r)) }),
                }
            }
        }
        SimplStmt::Assign(..) => {
            panic!("Assign should have been removed in pre-processing step");
        }
    }
}

fn conjunct_opt(a: Option<TokenStream>, b: Option<TokenStream>) -> Option<TokenStream> {
    match a {
        None => b,
        Some(x) => match b {
            None => Some(x),
            Some(y) => Some(quote! { (#x && #y) }),
        },
    }
}

fn impl_opt(a: Option<TokenStream>, b: Option<TokenStream>) -> Option<TokenStream> {
    match a {
        None => b,
        Some(x) => match b {
            None => None,
            Some(y) => Some(quote! { ::builtin::imply(#x, #y) }),
        },
    }
}

pub fn asserts_to_single_predicate_simpl_vec(sops: &Vec<SimplStmt>) -> Option<TokenStream> {
    let mut o = None;
    for t in sops {
        o = conjunct_opt(o, asserts_to_single_predicate_simpl(t));
    }
    o
}

pub fn asserts_to_single_predicate_simpl(sop: &SimplStmt) -> Option<TokenStream> {
    match sop {
        SimplStmt::Let(_span, pat, ty, e, child) => {
            let ty_tokens = match ty {
                None => TokenStream::new(),
                Some(ty) => quote! { : #ty },
            };
            match asserts_to_single_predicate_simpl_vec(child) {
                None => None,
                Some(r) => Some(quote! { { let #pat #ty_tokens = #e; #r } }),
            }
        }
        SimplStmt::Split(_span, SplitKind::If(cond), es) => {
            assert!(es.len() == 2);
            let x1 = asserts_to_single_predicate_simpl_vec(&es[0]);
            let x2 = asserts_to_single_predicate_simpl_vec(&es[1]);
            match (x1, x2) {
                (None, None) => None,
                (Some(e1), None) => Some(quote! { ::builtin::imply(#cond, #e1) }),
                (None, Some(e2)) => Some(quote! { ::builtin::imply(!(#cond), #e2) }),
                (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
            }
        }
        SimplStmt::Split(span, SplitKind::Match(match_e, arms), es) => {
            let opts: Vec<Option<TokenStream>> =
                es.iter().map(|e| asserts_to_single_predicate_simpl_vec(e)).collect();
            if opts.iter().any(|o| o.is_some()) {
                let cases = opts
                    .into_iter()
                    .map(|opt_t| Expr::Verbatim(opt_t.unwrap_or(quote! {true})))
                    .collect();
                let m = emit_match(*span, match_e, arms, &cases);
                Some(quote! {#m})
            } else {
                None
            }
        }
        SimplStmt::Split(..) => {
            panic!("other 'split' kinds should have been translated out");
        }
        SimplStmt::Assert(_span, e, _) => Some(quote_spanned! { e.span() => (#e) }),
        SimplStmt::Require(..) => None,
        SimplStmt::PostCondition(..) => None,
        SimplStmt::Assign(..) => {
            panic!("Assign should have been removed");
        }
    }
}

pub fn asserts_to_single_predicate(ts: &TransitionStmt) -> Option<TokenStream> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut o = None;
            for t in v {
                o = conjunct_opt(o, asserts_to_single_predicate(t));
            }
            o
        }
        TransitionStmt::Split(_span, SplitKind::Let(pat, ty, _, e), es) => {
            let ty_tokens = match ty {
                None => TokenStream::new(),
                Some(ty) => quote! { : #ty },
            };
            assert!(es.len() == 1);
            let child = &es[0];
            match asserts_to_single_predicate(child) {
                None => None,
                Some(r) => Some(quote! { { let #pat #ty_tokens = #e; #r } }),
            }
        }
        TransitionStmt::Split(_span, SplitKind::If(cond), es) => {
            assert!(es.len() == 2);
            let x1 = asserts_to_single_predicate(&es[0]);
            let x2 = asserts_to_single_predicate(&es[1]);
            match (x1, x2) {
                (None, None) => None,
                (Some(e1), None) => Some(quote! { ::builtin::imply(#cond, #e1) }),
                (None, Some(e2)) => Some(quote! { ::builtin::imply(!(#cond), #e2) }),
                (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
            }
        }
        TransitionStmt::Split(span, SplitKind::Match(match_e, arms), es) => {
            let opts: Vec<Option<TokenStream>> =
                es.iter().map(|e| asserts_to_single_predicate(e)).collect();
            if opts.iter().any(|o| o.is_some()) {
                let cases = opts
                    .into_iter()
                    .map(|opt_t| Expr::Verbatim(opt_t.unwrap_or(quote! {true})))
                    .collect();
                let m = emit_match(*span, match_e, arms, &cases);
                Some(quote! {#m})
            } else {
                None
            }
        }
        TransitionStmt::Split(_span, SplitKind::Special(..), _es) => {
            panic!("Special should have been translated out");
        }
        TransitionStmt::Assert(_span, e, _) => Some(quote_spanned! { e.span() => (#e) }),
        TransitionStmt::PostCondition(..)
        | TransitionStmt::Require(..)
        | TransitionStmt::Initialize(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::SubUpdate(..) => None,
    }
}

pub fn emit_match<T: quote::ToTokens>(
    span: Span,
    match_e: &Expr,
    arms: &Vec<Arm>,
    exprs: &Vec<T>,
) -> Expr {
    assert!(arms.len() == exprs.len());
    let cases: Vec<TokenStream> = arms
        .iter()
        .zip(exprs.iter())
        .map(|(arm, expr)| {
            let Arm { pat, guard, fat_arrow_token, comma: _ } = arm;
            let g = match guard {
                None => None,
                Some((if_token, box guard_e)) => Some(quote! { #if_token #guard_e }),
            };
            quote! { #pat #g #fat_arrow_token { #expr } }
        })
        .collect();
    Expr::Verbatim(quote_spanned! { span =>
        match #match_e {
            #( #cases )*
        }
    })
}
