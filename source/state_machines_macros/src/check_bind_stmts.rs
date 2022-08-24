use crate::ast::{MonoidElt, MonoidStmtType, SplitKind, TransitionStmt, SM};
use syn_verus::parse::Error;

pub fn check_bind_stmts(sm: &SM, ts: &mut TransitionStmt, errors: &mut Vec<Error>) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter_mut() {
                check_bind_stmts(sm, t, errors);
            }
        }
        TransitionStmt::Split(span, kind, splits) => {
            match kind {
                SplitKind::If(..) => {}
                SplitKind::Match(..) => {}
                SplitKind::Let(..) => {}
                SplitKind::Special(_, op, _, _) => {
                    if uses_bind(&op.elt) {
                        match op.stmt {
                            MonoidStmtType::Have
                            | MonoidStmtType::Withdraw
                            | MonoidStmtType::Remove => {
                                // ok
                            }

                            MonoidStmtType::Add(_) => {
                                errors.push(Error::new(
                                    *span,
                                    "pattern-binding cannot be used in an 'add' statement; there is no way to infer what value should be added",
                                ));
                            }
                            MonoidStmtType::Deposit => {
                                errors.push(Error::new(
                                    *span,
                                    "pattern-binding cannot be used in a 'deposit' statement; there is no way to infer what value should be deposited",
                                ));
                            }
                            MonoidStmtType::Guard => {
                                errors.push(Error::new(
                                    *span,
                                    "pattern-binding cannot be used in a 'guard' statement; a guard value must be a deterministic function of the local inputs",
                                ));
                            }
                        }
                    }
                }
            }

            for split in splits {
                check_bind_stmts(sm, split, errors);
            }
        }
        TransitionStmt::Require(..) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::Update(..) => {}
        TransitionStmt::SubUpdate(..) => {}
        TransitionStmt::Initialize(..) => {}
        TransitionStmt::PostCondition(..) => {}
    }
}

pub fn uses_bind(elt: &MonoidElt) -> bool {
    match elt {
        MonoidElt::OptionSome(None) => true,
        MonoidElt::OptionSome(Some(_)) => false,
        MonoidElt::SingletonKV(_, None) => true,
        MonoidElt::SingletonKV(_, Some(_)) => false,
        MonoidElt::SingletonMultiset(_) => false,
        MonoidElt::SingletonSet(_) => false,
        MonoidElt::True => false,
        MonoidElt::General(_) => false,
    }
}
