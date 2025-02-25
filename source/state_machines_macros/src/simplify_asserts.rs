use crate::ast::SimplStmt;
use crate::safety_conditions::has_any_assert_simpl;
use quote::quote;
use syn_verus::{Expr, Ident, Type};

/// Returns an equivalent SimplStmt sequence that has no 'assert' statements in it.
///
/// Essentially, we replace
///     assert a;
///     require b;
/// with:
///     require a ==> b;

pub fn simplify_asserts(sops: &Vec<SimplStmt>) -> Vec<SimplStmt> {
    let mut idx_of_first_assert = None;
    for i in 0..sops.len() {
        if has_any_assert_simpl(&sops[i]) {
            idx_of_first_assert = Some(i);
            break;
        }
    }

    if let Some(idx) = idx_of_first_assert {
        let span = sops[idx].get_span();
        let ident = Ident::new("tmp_assert", span);

        let mut res1 = sops[0..idx].to_vec();
        let mut res2 = simplify_asserts_vec(&sops[idx..].to_vec(), &ident);
        let initial = SimplStmt::Assign(
            span,
            ident,
            Type::Verbatim(quote! { ::core::primitive::bool }),
            Expr::Verbatim(quote! { true }),
            false,
        );
        let mut res = vec![initial];
        res.append(&mut res1);
        res.append(&mut res2);
        res
    } else {
        sops.clone()
    }
}

fn simplify_asserts_vec(sops: &Vec<SimplStmt>, assert_ident: &Ident) -> Vec<SimplStmt> {
    sops.iter().map(|sop| simplify_asserts_stmt(sop, assert_ident)).collect()
}

fn simplify_asserts_stmt(sop: &SimplStmt, assert_ident: &Ident) -> SimplStmt {
    match sop {
        SimplStmt::Let(span, pat, typ, expr, stmts, ex) => SimplStmt::Let(
            *span,
            pat.clone(),
            typ.clone(),
            expr.clone(),
            simplify_asserts_vec(stmts, assert_ident),
            ex.clone(),
        ),
        SimplStmt::Split(span, sk, splits, ex) => {
            let splits2 = splits
                .iter()
                .map(|(s, sops)| (s.clone(), simplify_asserts_vec(sops, assert_ident)))
                .collect();
            SimplStmt::Split(*span, sk.clone(), splits2, ex.clone())
        }

        SimplStmt::Require(span, expr) => SimplStmt::Require(
            *span,
            Expr::Verbatim(quote_spanned_vstd!(vstd, *span => {
                #vstd::prelude::imply(
                    #assert_ident,
                    #expr
                )
            })),
        ),
        SimplStmt::PostCondition(span, expr, reason) => SimplStmt::PostCondition(
            *span,
            Expr::Verbatim(quote_spanned_vstd!(vstd, *span => {
                #vstd::prelude::imply(
                    #assert_ident,
                    #expr
                )
            })),
            reason.clone(),
        ),
        SimplStmt::Assert(span, expr, _assert_proof) => SimplStmt::Assign(
            *span,
            assert_ident.clone(),
            Type::Verbatim(quote! { ::core::primitive::bool }),
            Expr::Verbatim(quote! {
                #assert_ident && (#expr)
            }),
            false,
        ),
        SimplStmt::Assign(..) => sop.clone(),
    }
}
