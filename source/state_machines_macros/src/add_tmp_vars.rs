use crate::ast::{Field, LetKind, MonoidElt, SpecialOp, TransitionStmt, SM};
use crate::to_token_stream::shardable_type_to_type;
use proc_macro2::Span;
use quote::quote;
use syn::{Expr, Ident, Type};

/// Add temp variables for special ops. More specifically:
/// Replace each `SpecialOp(_, _, expr)` with
/// `let update_tmp_x = expr; SpecialOp(_, _, update_tmp_x);`
/// The scope of the newly-introduced let-statement will reach forward as far as possible.

pub fn add_tmp_vars_special_ops(sm: &SM, ts: &TransitionStmt) -> TransitionStmt {
    let mut ctxt = Ctxt { counter: 0 };

    add_tmp_vars(sm, ts, &mut ctxt)
}

struct Ctxt {
    pub counter: usize,
}

impl Ctxt {
    fn get_next_name(&mut self) -> String {
        let i = self.counter;
        self.counter += 1;
        "update_tmp_".to_string() + &i.to_string()
    }
}

fn add_tmp_vars(sm: &SM, ts: &TransitionStmt, ctxt: &mut Ctxt) -> TransitionStmt {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut fv = Vec::new();
            for t in v {
                flatten(t, &mut fv);
            }
            add_tmp_vars_vec(sm, *span, fv, ctxt)
        }
        TransitionStmt::Let(span, id, ty, lk, e, child) => {
            let child = add_tmp_vars(sm, child, ctxt);
            TransitionStmt::Let(*span, id.clone(), ty.clone(), *lk, e.clone(), Box::new(child))
        }
        TransitionStmt::If(span, cond, thn, els) => {
            let thn = add_tmp_vars(sm, thn, ctxt);
            let els = add_tmp_vars(sm, els, ctxt);
            TransitionStmt::If(*span, cond.clone(), Box::new(thn), Box::new(els))
        }

        TransitionStmt::Require(..)
        | TransitionStmt::Assert(..)
        | TransitionStmt::Initialize(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::Special(..)
        | TransitionStmt::PostCondition(..) => {
            add_tmp_vars_vec(sm, *ts.get_span(), vec![ts.clone()], ctxt)
        }
    }
}

fn add_tmp_vars_vec(
    sm: &SM,
    span: Span,
    v: Vec<TransitionStmt>,
    ctxt: &mut Ctxt,
) -> TransitionStmt {
    let mut stmts: Vec<TransitionStmt> = Vec::new();
    let mut bindings: Vec<(Ident, Type, Expr)> = Vec::new();

    for ts in v.iter() {
        match ts {
            TransitionStmt::Require(..)
            | TransitionStmt::Assert(..)
            | TransitionStmt::Initialize(..)
            | TransitionStmt::Update(..)
            | TransitionStmt::PostCondition(..) => {
                stmts.push(ts.clone());
            }

            TransitionStmt::Special(span, ident, op, proof) => {
                let field = crate::transitions::get_field(&sm.fields, ident);
                let (new_op, new_bindings) = op_replace_with_tmps(ctxt, *span, op.clone(), field);
                let new_special =
                    TransitionStmt::Special(*span, ident.clone(), new_op, proof.clone());
                stmts.push(new_special);
                bindings.extend(new_bindings);
            }

            _ => {
                stmts.push(add_tmp_vars(sm, ts, ctxt));
            }
        }
    }

    let mut node = TransitionStmt::Block(span, stmts);
    for (id, ty, e) in bindings.into_iter().rev() {
        node = TransitionStmt::Let(span, id, Some(ty), LetKind::Normal, e, Box::new(node));
    }

    node
}

fn op_replace_with_tmps(
    ctxt: &mut Ctxt,
    span: Span,
    op: SpecialOp,
    field: &Field,
) -> (SpecialOp, Vec<(Ident, Type, Expr)>) {
    let mut op = op;

    let bindings = match &mut op.elt {
        MonoidElt::OptionSome(e) => {
            let tmp_name = ctxt.get_next_name();
            let tmp_ident = Ident::new(&tmp_name, span);
            let ty = field.stype.get_option_param_type();
            let binding = (tmp_ident.clone(), ty, e.clone());
            *e = Expr::Verbatim(quote! { #tmp_ident });
            vec![binding]
        }
        MonoidElt::SingletonMultiset(e) => {
            let tmp_name = ctxt.get_next_name();
            let tmp_ident = Ident::new(&tmp_name, span);
            let ty = field.stype.get_multiset_param_type();
            let binding = (tmp_ident.clone(), ty, e.clone());
            *e = Expr::Verbatim(quote! { #tmp_ident });
            vec![binding]
        }
        MonoidElt::General(e) => {
            let tmp_name = ctxt.get_next_name();
            let tmp_ident = Ident::new(&tmp_name, span);
            let ty = shardable_type_to_type(field.type_span, &field.stype);
            let binding = (tmp_ident.clone(), ty, e.clone());
            *e = Expr::Verbatim(quote! { #tmp_ident });
            vec![binding]
        }

        MonoidElt::SingletonKV(e1, e2) => {
            let tmp_name1 = ctxt.get_next_name();
            let tmp_ident1 = Ident::new(&tmp_name1, span);
            let ty1 = field.stype.get_map_key_type();
            let binding1 = (tmp_ident1.clone(), ty1, e1.clone());

            let tmp_name2 = ctxt.get_next_name();
            let tmp_ident2 = Ident::new(&tmp_name2, span);
            let ty2 = field.stype.get_map_value_type();
            let binding2 = (tmp_ident2.clone(), ty2, e2.clone());

            *e1 = Expr::Verbatim(quote! { #tmp_ident1 });
            *e2 = Expr::Verbatim(quote! { #tmp_ident2 });
            vec![binding1, binding2]
        }
    };

    (op, bindings)
}

fn flatten(ts: &TransitionStmt, res: &mut Vec<TransitionStmt>) {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for t in v {
                flatten(t, res);
            }
        }
        _ => {
            res.push(ts.clone());
        }
    }
}
