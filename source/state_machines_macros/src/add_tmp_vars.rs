use crate::ast::{LetKind, SpecialOp, TransitionStmt};
use proc_macro2::Span;
use quote::quote;
use syn::{Expr, Ident};

pub fn add_tmp_vars_special_ops(ts: &TransitionStmt) -> TransitionStmt {
    let mut ctxt = Ctxt { counter: 0 };

    add_tmp_vars(ts, &mut ctxt)
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

fn add_tmp_vars(ts: &TransitionStmt, ctxt: &mut Ctxt) -> TransitionStmt {
    match ts {
        TransitionStmt::Block(span, v) => {
            let mut fv = Vec::new();
            for t in v {
                flatten(t, &mut fv);
            }
            add_tmp_vars_vec(*span, fv, ctxt)
        }
        TransitionStmt::Let(span, id, lk, e, child) => {
            let child = add_tmp_vars(child, ctxt);
            TransitionStmt::Let(*span, id.clone(), *lk, e.clone(), Box::new(child))
        }
        TransitionStmt::If(span, cond, thn, els) => {
            let thn = add_tmp_vars(thn, ctxt);
            let els = add_tmp_vars(els, ctxt);
            TransitionStmt::If(*span, cond.clone(), Box::new(thn), Box::new(els))
        }

        TransitionStmt::Require(_, _)
        | TransitionStmt::Assert(_, _)
        | TransitionStmt::Initialize(_, _, _)
        | TransitionStmt::Update(_, _, _)
        | TransitionStmt::Special(_, _, _)
        | TransitionStmt::PostCondition(..) => {
            add_tmp_vars_vec(*ts.get_span(), vec![ts.clone()], ctxt)
        }
    }
}

fn add_tmp_vars_vec(span: Span, v: Vec<TransitionStmt>, ctxt: &mut Ctxt) -> TransitionStmt {
    let mut res: Vec<TransitionStmt> = Vec::new();

    for ts in v.iter().rev() {
        match ts {
            TransitionStmt::Require(_, _)
            | TransitionStmt::Assert(_, _)
            | TransitionStmt::Initialize(_, _, _)
            | TransitionStmt::Update(_, _, _)
            | TransitionStmt::PostCondition(..) => {
                res.push(ts.clone());
            }

            TransitionStmt::Special(span, ident, op) => {
                let (new_op, bindings) = op_replace_with_tmps(ctxt, *span, op.clone());
                let new_special = TransitionStmt::Special(*span, ident.clone(), new_op);
                res.push(new_special);
                let mut node = TransitionStmt::Block(*span, res.into_iter().rev().collect());

                for (id, e) in bindings {
                    node = TransitionStmt::Let(*span, id, LetKind::Normal, e, Box::new(node));
                }

                res = vec![node];
            }

            _ => {
                res.push(add_tmp_vars(ts, ctxt));
            }
        }
    }

    TransitionStmt::Block(span, res.into_iter().rev().collect())
}

fn op_replace_with_tmps(
    ctxt: &mut Ctxt,
    span: Span,
    op: SpecialOp,
) -> (SpecialOp, Vec<(Ident, Expr)>) {
    let mut op = op;

    let bindings = match &mut op {
        SpecialOp::AddSome(e)
        | SpecialOp::RemoveSome(e)
        | SpecialOp::HaveSome(e)
        | SpecialOp::AddElement(e)
        | SpecialOp::RemoveElement(e)
        | SpecialOp::HaveElement(e)
        | SpecialOp::DepositSome(e)
        | SpecialOp::WithdrawSome(e)
        | SpecialOp::GuardSome(e) => {
            let tmp_name = ctxt.get_next_name();
            let tmp_ident = Ident::new(&tmp_name, span);
            let binding = (tmp_ident.clone(), e.clone());
            *e = Expr::Verbatim(quote! { #tmp_ident });
            vec![binding]
        }

        SpecialOp::AddKV(e1, e2) | SpecialOp::RemoveKV(e1, e2) | SpecialOp::HaveKV(e1, e2) => {
            let tmp_name1 = ctxt.get_next_name();
            let tmp_ident1 = Ident::new(&tmp_name1, span);
            let binding1 = (tmp_ident1.clone(), e1.clone());

            let tmp_name2 = ctxt.get_next_name();
            let tmp_ident2 = Ident::new(&tmp_name2, span);
            let binding2 = (tmp_ident2.clone(), e2.clone());

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
