//! For state machines marked `#![verifier::prophetic]`, prophetic expressions are only
//! allowed in `require` and `assert` statements. To enforce this, before simplification,
//! we wrap every other expression in a call to the `prophecy_disallowed` builtin,
//! which is checked by Verus's mode checker.
//!
//! Note that this needs to happen *before* simplification, since some special statements
//! (e.g., `add`, `remove`, `have`) lower to `require` or `assert` statements, and we want
//! to disallow prophecy in those as well.

use crate::ast::{MonoidElt, SM, ShardableType, SpecialOp, SplitKind, SubIdx, TransitionStmt};
use verus_syn::Expr;
use verus_syn::spanned::Spanned;

pub fn disallow_prophecy(sm: &SM, ts: &TransitionStmt) -> TransitionStmt {
    let mut ts = ts.clone();
    disallow_prophecy_stmt(sm, &mut ts);
    ts
}

fn wrap(e: &mut Expr, reason: &str) {
    let span = e.span();
    *e = Expr::Verbatim(quote_spanned_vstd! { vstd, span =>
        #vstd::prelude::prophecy_disallowed(#reason, #e)
    });
}

/// Like `wrap`, but supplies `nat` as an explicit type argument for cases where `nat` is expected.
/// This makes type inference work better and prevents errors about "type annotations needed"
/// from `spec_literal_integer`
fn wrap_nat(e: &mut Expr, reason: &str, expect_nat: bool) {
    if expect_nat {
        let span = e.span();
        *e = Expr::Verbatim(quote_spanned_vstd! { vstd, span =>
            #vstd::prelude::prophecy_disallowed::<#vstd::prelude::nat>(#reason, #e)
        });
    } else {
        wrap(e, reason)
    }
}

fn disallow_prophecy_stmt(sm: &SM, ts: &mut TransitionStmt) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter_mut() {
                disallow_prophecy_stmt(sm, t);
            }
        }
        TransitionStmt::Split(_, split_kind, es) => {
            match &mut **split_kind {
                SplitKind::Let(_pat, _ty, _lk, e) => {
                    wrap(e, "`let` statement");
                }
                SplitKind::If(cond) => {
                    wrap(cond, "`if` condition");
                }
                SplitKind::Match(match_e, arms) => {
                    wrap(match_e, "`match` scrutinee");
                    for arm in arms.iter_mut() {
                        if let Some((_, guard_e)) = &mut arm.guard {
                            wrap(&mut **guard_e, "`match` guard");
                        }
                    }
                }
                SplitKind::Special(f, op, _proof, _pat_opt) => {
                    let expect_nat = sm.fields.iter().find(|f0| f0.name == *f).is_some_and(|f| {
                        matches!(f.stype, ShardableType::Count | ShardableType::PersistentCount)
                    });
                    disallow_prophecy_op(op, expect_nat);
                }
            }
            for e in es.iter_mut() {
                disallow_prophecy_stmt(sm, e);
            }
        }
        TransitionStmt::Require(..) | TransitionStmt::Assert(..) => {}
        TransitionStmt::SubUpdate(_, _f, subs, e) => {
            for sub in subs.iter_mut() {
                match sub {
                    SubIdx::Field(_) => {}
                    SubIdx::Idx(idx) => {
                        wrap(&mut **idx, "`update` statement");
                    }
                }
            }
            wrap(e, "`update` statement");
        }
        TransitionStmt::Update(_, _f, e) => {
            wrap(e, "`update` statement");
        }
        TransitionStmt::Initialize(_, _f, e) => {
            wrap(e, "`init` statement");
        }
        TransitionStmt::PostCondition(_, e) => {
            wrap(e, "post-condition");
        }
    }
}

fn disallow_prophecy_op(op: &mut SpecialOp, expect_nat: bool) {
    let reason = format!("`{}` statement", op.stmt.name());
    match &mut op.elt {
        MonoidElt::True | MonoidElt::OptionSome(None) => {}
        MonoidElt::OptionSome(Some(e))
        | MonoidElt::SingletonMultiset(e)
        | MonoidElt::SingletonSet(e)
        | MonoidElt::General(e) => {
            wrap_nat(e, &reason, expect_nat);
        }
        MonoidElt::SingletonKV(k, v_opt) => {
            wrap(k, &reason);
            if let Some(v) = v_opt {
                wrap(&mut **v, &reason);
            }
        }
    }
}
