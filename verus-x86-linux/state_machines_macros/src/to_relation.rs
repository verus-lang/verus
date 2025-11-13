use crate::ast::{Arm, SimplStmt, SplitKind};
use indexmap::IndexSet;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, quote_spanned};
use syn_verus::spanned::Spanned;
use syn_verus::visit::Visit;
use syn_verus::{Expr, Lit, LitStr};

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
    let x = if weak {
        let sops = crate::simplify_asserts::simplify_asserts(sops);
        let sops = annotate_extractions(&sops);
        simpl_conjunct_vec(&sops, None)
    } else {
        // Leave the assertions is; they will be included as normal conjuncts
        let sops = annotate_extractions(&sops);
        simpl_conjunct_vec(&sops, None)
    };

    match x {
        Some(e) => e,
        None => quote! { true },
    }
}

pub fn to_is_enabled_condition_weak(sops: &Vec<SimplStmt>) -> TokenStream {
    let sops = remove_post_conditions_vec(sops);
    to_relation(&sops, true)
}

/// Mark each scope-creating node with the assign-vars that need to be extracted
/// Also, remove any 'assign' that isn't used.

fn annotate_extractions(sops: &Vec<SimplStmt>) -> Vec<SimplStmt> {
    let mut all_assign_vars = IndexSet::new();
    for sop in sops {
        get_all_assigns(sop, &mut all_assign_vars);
    }

    let mut used_ids = IndexSet::new();
    let mut sops = sops.clone();
    annotate_extractions_vec(&mut sops, &mut used_ids);

    // Sanity check. In a well-formed transition, no variable should be used
    // without being assigned first. That means the 'use' set at the beginning
    // should be empty (i.e., there should not be a variable which has is used,
    // and for which we are still looking for the assign).
    for var in all_assign_vars {
        assert!(!used_ids.contains(&var));
    }

    sops
}

fn get_all_assigns(sop: &SimplStmt, assigned: &mut IndexSet<String>) {
    match sop {
        SimplStmt::Let(_span, _pat, _ty, _e, inner, _) => {
            for op in inner {
                get_all_assigns(op, assigned);
            }
        }
        SimplStmt::Split(_span, _split_kind, inners, _) => {
            for inner in inners.iter() {
                for op in inner.1.iter() {
                    get_all_assigns(op, assigned);
                }
            }
        }
        SimplStmt::Require(..) => {}
        SimplStmt::PostCondition(..) => {}
        SimplStmt::Assert(..) => {}
        SimplStmt::Assign(_span, id, _ty, _e, _prequel) => {
            assigned.insert(id.to_string());
        }
    }
}

fn add_used_ids_from_expr(used_ids: &mut IndexSet<String>, e: &Expr) {
    let mut u = UseGetter { used_ids };
    u.visit_expr(e);
}

struct UseGetter<'a> {
    used_ids: &'a mut IndexSet<String>,
}

impl<'ast> Visit<'ast> for UseGetter<'ast> {
    fn visit_ident(&mut self, node: &'ast Ident) {
        self.used_ids.insert(node.to_string());
    }

    fn visit_expr(&mut self, node: &'ast Expr) {
        syn_verus::visit::visit_expr(self, node);

        match node {
            Expr::Verbatim(stream) => {
                self.visit_stream(stream.clone());
            }
            _ => {}
        }
    }
}

impl<'ast> UseGetter<'ast> {
    fn visit_stream(&mut self, stream: TokenStream) {
        for token_tree in stream.into_iter() {
            match token_tree {
                proc_macro2::TokenTree::Group(group) => {
                    self.visit_stream(group.stream());
                }
                proc_macro2::TokenTree::Ident(ident) => {
                    self.used_ids.insert(ident.to_string());
                }
                proc_macro2::TokenTree::Punct(_) => {}
                proc_macro2::TokenTree::Literal(_) => {}
            }
        }
    }
}

fn annotate_extractions_vec(sops: &mut Vec<SimplStmt>, used_ids: &mut IndexSet<String>) {
    let mut old_sops: Vec<SimplStmt> = Vec::new();
    core::mem::swap(&mut old_sops, sops);
    for mut sop in old_sops.into_iter().rev() {
        let stmt_creates_scope = match &sop {
            SimplStmt::Let(..) => true,
            SimplStmt::Split(..) => true,
            SimplStmt::Require(..) => false,
            SimplStmt::PostCondition(..) => false,
            SimplStmt::Assert(..) => false,
            SimplStmt::Assign(..) => false,
        };

        if stmt_creates_scope {
            let mut get_assigns = IndexSet::new();
            get_all_assigns(&sop, &mut get_assigns);

            let span = sop.get_span();
            let intersection: Vec<Ident> =
                get_assigns.intersection(&*used_ids).map(|s| Ident::new(&s, span)).collect();

            match &mut sop {
                SimplStmt::Let(_, _, _, _, _, extractions) => {
                    *extractions = intersection;
                }
                SimplStmt::Split(_, _, _, extractions) => {
                    *extractions = intersection;
                }
                _ => {
                    panic!("stmt_creates_scope");
                }
            }
        }

        if let SimplStmt::Assign(_span, ident, _ty, e, _prequel) = &sop {
            // Remove the variable name from the 'use' set.
            // In doing so, we check if it was already there;
            // if the variable isn't used, then we can skip this step entirely.
            let is_used = used_ids.remove(&ident.to_string());
            if is_used {
                add_used_ids_from_expr(used_ids, e);
                sops.push(sop);
            }
        } else {
            annotate_extractions_stmt(&mut sop, used_ids);
            sops.push(sop);
        }
    }
    sops.reverse();
}

fn annotate_extractions_stmt(sop: &mut SimplStmt, used_ids: &mut IndexSet<String>) {
    match sop {
        SimplStmt::Let(_span, _pat, _ty, e, inner, _) => {
            annotate_extractions_vec(inner, used_ids);
            add_used_ids_from_expr(used_ids, e);
        }
        SimplStmt::Split(_span, SplitKind::If(cond), inners, _) => {
            let mut union = IndexSet::<String>::new();
            for inner in inners.iter_mut() {
                let mut inner_used_ids: IndexSet<String> = used_ids.clone();
                annotate_extractions_vec(&mut inner.1, &mut inner_used_ids);

                set_union(&mut union, inner_used_ids);
            }
            *used_ids = union;
            add_used_ids_from_expr(used_ids, cond);
        }
        SimplStmt::Split(_span, SplitKind::Match(m, arms), inners, _) => {
            let mut union = IndexSet::<String>::new();
            for (i, inner) in inners.iter_mut().enumerate() {
                let mut inner_used_ids: IndexSet<String> = used_ids.clone();
                annotate_extractions_vec(&mut inner.1, &mut inner_used_ids);

                if let Some(g) = &arms[i].guard {
                    add_used_ids_from_expr(&mut inner_used_ids, &*g.1);
                }

                set_union(&mut union, inner_used_ids);
            }
            *used_ids = union;
            add_used_ids_from_expr(used_ids, m);
        }
        SimplStmt::Split(..) => {
            panic!("unexpected SplitKind here");
        }
        SimplStmt::Require(_span, e) => {
            add_used_ids_from_expr(used_ids, e);
        }
        SimplStmt::PostCondition(_span, e, _reason) => {
            add_used_ids_from_expr(used_ids, e);
        }
        SimplStmt::Assert(_span, e, _pf) => {
            add_used_ids_from_expr(used_ids, e);
        }
        SimplStmt::Assign(..) => {
            // should be handled as separate case by the caller
            panic!("simply_assigns_stmt doesn't handle Assign");
        }
    }
}

/// Collect all conjuncts

fn simpl_conjunct_vec(sops: &Vec<SimplStmt>, p: Option<TokenStream>) -> Option<TokenStream> {
    let let_skip_brace = sops.len() == 1;

    let mut p = p;
    for i in (0..sops.len()).rev() {
        let e = &sops[i];
        let assign_skip_brace = i == 0 || matches!(sops[i - 1], SimplStmt::Assign(..));
        p = simpl_conjunct_stmt(e, p, let_skip_brace, assign_skip_brace);
    }
    p
}

fn simpl_conjunct_stmt(
    sop: &SimplStmt,
    p: Option<TokenStream>,
    let_skip_brace: bool,
    assign_skip_brace: bool,
) -> Option<TokenStream> {
    match sop {
        SimplStmt::Assign(_span, ident, ty, e, _prelude) => match p {
            None => None,
            Some(r) => {
                if assign_skip_brace {
                    Some(quote! { let #ident : #ty = #e; #r })
                } else {
                    Some(quote! { { let #ident : #ty = #e; #r } })
                }
            }
        },
        SimplStmt::Let(span, pat, ty, e, child, _) => {
            let x = simpl_conjunct_vec(child, None);
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

            let l = get_extraction_decl_stmt(sop);
            conjunct_opt(t, prepend_let_stmt(*span, l, p))
        }
        SimplStmt::Split(span, SplitKind::If(cond), es, _) => {
            assert!(es.len() == 2);
            let x1 = simpl_conjunct_vec(&es[0].1, None);
            let x2 = simpl_conjunct_vec(&es[1].1, None);
            let t = match (x1, x2) {
                (None, None) => None,
                (Some(e1), None) => {
                    Some(quote_vstd! { vstd => #vstd::prelude::imply(#cond, {#e1}) })
                }
                (None, Some(e2)) => {
                    Some(quote_vstd! { vstd => #vstd::prelude::imply(!(#cond), {#e2}) })
                }
                (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
            };

            let l = get_extraction_decl_stmt(sop);
            conjunct_opt(t, prepend_let_stmt(*span, l, p))
        }
        SimplStmt::Split(span, SplitKind::Match(match_e, arms), es, _) => {
            let opts: Vec<Option<TokenStream>> =
                es.iter().map(|e| simpl_conjunct_vec(&e.1, None)).collect();
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

            let l = get_extraction_decl_stmt(sop);
            conjunct_opt(t, prepend_let_stmt(*span, l, p))
        }
        SimplStmt::Split(..) => {
            panic!("this SplitKind should have been translated out");
        }
        SimplStmt::PostCondition(_span, e, reason) => prepend_conjunct(e, p, &reason.to_err_msg()),
        SimplStmt::Require(_span, e) => prepend_conjunct(e, p, "cannot prove this condition holds"),
        SimplStmt::Assert(_span, e, _) => {
            prepend_conjunct(e, p, "cannot prove this 'assert' holds")
        }
    }
}

/// Extract assignments that were done within scopes

fn get_extraction_decl_stmt(sop: &SimplStmt) -> Option<TokenStream> {
    match sop {
        SimplStmt::Let(span, pat, ty, e, child, extractions) => {
            if extractions.len() == 0 {
                return None;
            }
            let extup = get_extup(extractions);

            let c = extr_vec(child);

            let ty_tokens = match ty {
                None => TokenStream::new(),
                Some(ty) => quote! { : #ty },
            };
            Some(quote_spanned! { *span =>
                let #extup = ({
                    let #pat #ty_tokens = #e;
                    #c
                    #extup
                });
            })
        }
        SimplStmt::Split(span, SplitKind::If(cond), es, extractions) => {
            if extractions.len() == 0 {
                return None;
            }
            let extup = get_extup(extractions);

            assert!(es.len() == 2);
            let c1 = extr_vec(&es[0].1);
            let c2 = extr_vec(&es[1].1);

            Some(quote_spanned! { *span =>
                let #extup = (if (#cond) {
                    #c1 #extup
                } else {
                    #c2 #extup
                });
            })
        }
        SimplStmt::Split(span, SplitKind::Match(match_e, arms), es, extractions) => {
            if extractions.len() == 0 {
                return None;
            }
            let extup = get_extup(extractions);

            let cases = es
                .iter()
                .map(|e| {
                    let c = extr_vec(&e.1);
                    Expr::Verbatim(quote_spanned! { *span => #c #extup })
                })
                .collect();

            let m = emit_match(*span, match_e, arms, &cases);

            Some(quote_spanned! { *span =>
                let #extup = (#m);
            })
        }
        _ => {
            panic!("get_extraction_decl_stmt got unexpected stmt");
        }
    }
}

fn extr_vec(sops: &Vec<SimplStmt>) -> TokenStream {
    let mut res = TokenStream::new();
    for sop in sops {
        match sop {
            SimplStmt::Let(..) | SimplStmt::Split(..) => {
                if let Some(ts) = get_extraction_decl_stmt(sop) {
                    res.extend(ts)
                }
            }
            SimplStmt::Require(..) | SimplStmt::PostCondition(..) | SimplStmt::Assert(..) => {}
            SimplStmt::Assign(span, ident, ty, expr, _prelude) => {
                res.extend(quote_spanned! { *span =>
                    let #ident : #ty = (#expr);
                })
            }
        }
    }
    res
}

// Utils

fn prepend_let_stmt(
    span: Span,
    l: Option<TokenStream>,
    p: Option<TokenStream>,
) -> Option<TokenStream> {
    match (l, p) {
        (_, None) => None,
        (None, Some(q)) => Some(q),
        (Some(l), Some(q)) => Some(quote_spanned! { span => { #l #q } }),
    }
}

fn prepend_conjunct(e: &Expr, p: Option<TokenStream>, msg: &str) -> Option<TokenStream> {
    let msg_lit = Lit::Str(LitStr::new(msg, e.span()));
    let err_attr = quote_spanned! { e.span() =>
        #[verifier(custom_err(#msg_lit))] /* vattr */
    };
    match p {
        None => Some(quote_spanned! { e.span() => #err_attr (#e) }),
        Some(r) => Some(quote_spanned! { e.span() => (#err_attr (#e) && #r) }),
    }
}

pub fn conjunct_opt(a: Option<TokenStream>, b: Option<TokenStream>) -> Option<TokenStream> {
    match a {
        None => b,
        Some(x) => match b {
            None => Some(x),
            Some(y) => Some(quote! { ((#x) && (#y)) }),
        },
    }
}

fn get_extup(a: &Vec<Ident>) -> TokenStream {
    assert!(a.len() > 0);
    if a.len() == 1 {
        let x = &a[0];
        quote! { #x }
    } else {
        quote! { (#(#a),*) }
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
                Some((if_token, guard_e)) => {
                    let guard_e = &**guard_e;
                    Some(quote! { #if_token #guard_e })
                }
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

fn set_union(s: &mut IndexSet<String>, t: IndexSet<String>) {
    for x in t.into_iter() {
        s.insert(x);
    }
}

fn remove_post_conditions_vec(sops: &Vec<SimplStmt>) -> Vec<SimplStmt> {
    let mut res = vec![];
    for sop in sops.iter() {
        match sop {
            SimplStmt::Let(span, pat, ty, e, child, ex) => {
                let op = SimplStmt::Let(
                    *span,
                    pat.clone(),
                    ty.clone(),
                    e.clone(),
                    remove_post_conditions_vec(child),
                    ex.clone(),
                );
                res.push(op);
            }
            SimplStmt::Split(span, sk, es, ex) => {
                let mut es2 = vec![];
                for (sp, child) in es {
                    let child2 = remove_post_conditions_vec(child);
                    es2.push((*sp, child2));
                }
                let op = SimplStmt::Split(*span, sk.clone(), es2, ex.clone());
                res.push(op);
            }
            SimplStmt::PostCondition(..) => {}
            SimplStmt::Require(..) | SimplStmt::Assert(..) | SimplStmt::Assign(..) => {
                res.push(sop.clone());
            }
        }
    }
    res
}
