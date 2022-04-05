use crate::ast::{SimplStmt, SM};
use proc_macro2::{TokenStream, TokenTree};
use quote::quote;
use std::collections::HashSet;
use syn::visit::Visit;
use syn::{Expr, Ident, Pat};

/// Returns an equivalent SimplStmt sequence that has no 'assign' statements in it.

pub fn simplify_assigns(sm: &SM, sops: &Vec<SimplStmt>) -> Vec<SimplStmt> {
    let mut all_assign_vars = HashSet::new();
    for sop in sops {
        get_all_assigns(sop, &mut all_assign_vars);
    }

    let mut used_ids = HashSet::new();
    let res = simplify_assigns_vec(sm, sops, &mut used_ids);

    // Sanity check. In a well-formed transition, no variable should be used
    // without being assigned first. That means the 'use' set at the beginning
    // should be empty (i.e., there should not be a variable which has is used,
    // and for which we are still looking for the assign).
    for var in all_assign_vars {
        assert!(!used_ids.contains(&var));
    }

    res
}

fn simplify_assigns_vec(
    sm: &SM,
    sops: &Vec<SimplStmt>,
    used_ids: &mut HashSet<String>,
) -> Vec<SimplStmt> {
    let mut v: Vec<SimplStmt> = Vec::new();
    for sop in sops.iter().rev() {
        let stmt_creates_scope = match sop {
            SimplStmt::Let(..) => true,
            SimplStmt::Split(..) => true,
            SimplStmt::Require(..) => false,
            SimplStmt::PostCondition(..) => false,
            SimplStmt::Assert(..) => false,
            SimplStmt::Assign(..) => false,
        };

        if stmt_creates_scope {
            let mut get_assigns = HashSet::new();
            get_all_assigns(sop, &mut get_assigns);
            let intersection: Vec<&String> = get_assigns.intersection(&*used_ids).collect();
            if intersection.len() > 0 {
                // TODO implement this
                panic!("currently not supported to read or update a field after a scoped update");
            }
        }

        match sop {
            SimplStmt::Assign(span, ident, ty, e) => {
                // Remove the variable name from the 'use' set.
                // In doing so, we check if it was already there;
                // if the variable isn't used, then we can skip this step entirely.
                let is_used = used_ids.remove(&ident.to_string());
                if is_used {
                    add_used_ids_from_expr(used_ids, e);

                    // Turn the `Assign` into a `Let` block.
                    v = vec![SimplStmt::Let(
                        *span,
                        Pat::Verbatim(quote! { #ident }),
                        Some(ty.clone()),
                        e.clone(),
                        v.into_iter().rev().collect(),
                    )];
                }
            }
            _ => {
                let new_sop = simplify_assigns_stmt(sm, sop, used_ids);
                v.push(new_sop);
            }
        }
    }
    v.into_iter().rev().collect()
}

fn simplify_assigns_stmt(sm: &SM, sop: &SimplStmt, used_ids: &mut HashSet<String>) -> SimplStmt {
    match sop {
        SimplStmt::Let(span, pat, ty, e, inner) => {
            // Note: right now we assume that assign-vars can only be 'used' from
            // require/assert/update (because that is how they are added in
            // the simplification pass). So we don't call `add_used_ids` here.
            // That might change later.

            let mut inner_used_ids: HashSet<String> = HashSet::new();
            let simpl_inner = simplify_assigns_vec(sm, inner, &mut inner_used_ids);
            set_union(used_ids, inner_used_ids);
            SimplStmt::Let(*span, pat.clone(), ty.clone(), e.clone(), simpl_inner)
        }
        SimplStmt::Split(span, split_kind, inners) => {
            let mut simpl_inners = Vec::new();
            for inner in inners.iter() {
                let mut inner_used_ids: HashSet<String> = HashSet::new();
                let simpl_inner = simplify_assigns_vec(sm, inner, &mut inner_used_ids);
                set_union(used_ids, inner_used_ids);
                simpl_inners.push(simpl_inner);
            }
            SimplStmt::Split(*span, split_kind.clone(), simpl_inners)
        }
        SimplStmt::Require(span, e) => {
            add_used_ids_from_expr(used_ids, e);
            SimplStmt::Require(*span, e.clone())
        }
        SimplStmt::PostCondition(span, e) => {
            add_used_ids_from_expr(used_ids, e);
            SimplStmt::PostCondition(*span, e.clone())
        }
        SimplStmt::Assert(span, e, pf) => {
            add_used_ids_from_expr(used_ids, e);
            SimplStmt::Assert(*span, e.clone(), pf.clone())
        }
        SimplStmt::Assign(..) => {
            // should be handled as separate case by the caller
            panic!("simply_assigns_stmt doesn't handle Assign");
        }
    }
}

fn get_all_assigns(sop: &SimplStmt, assigned: &mut HashSet<String>) {
    match sop {
        SimplStmt::Let(_span, _pat, _ty, _e, inner) => {
            for op in inner {
                get_all_assigns(op, assigned);
            }
        }
        SimplStmt::Split(_span, _split_kind, inners) => {
            for inner in inners.iter() {
                for op in inner {
                    get_all_assigns(op, assigned);
                }
            }
        }
        SimplStmt::Require(..) => {}
        SimplStmt::PostCondition(..) => {}
        SimplStmt::Assert(..) => {}
        SimplStmt::Assign(_span, id, _ty, _e) => {
            assigned.insert(id.to_string());
        }
    }
}

fn add_used_ids_from_expr(used_ids: &mut HashSet<String>, e: &Expr) {
    let mut u = UseGetter { used_ids };
    u.visit_expr(e);
}

struct UseGetter<'a> {
    used_ids: &'a mut HashSet<String>,
}

impl<'ast> Visit<'ast> for UseGetter<'ast> {
    fn visit_ident(&mut self, node: &'ast Ident) {
        self.used_ids.insert(node.to_string());
    }

    fn visit_expr(&mut self, node: &'ast Expr) {
        syn::visit::visit_expr(self, node);

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
                TokenTree::Group(group) => {
                    self.visit_stream(group.stream());
                }
                TokenTree::Ident(ident) => {
                    self.used_ids.insert(ident.to_string());
                }
                TokenTree::Punct(_) => {}
                TokenTree::Literal(_) => {}
            }
        }
    }
}

fn set_union(s: &mut HashSet<String>, t: HashSet<String>) {
    for x in t.into_iter() {
        s.insert(x);
    }
}
