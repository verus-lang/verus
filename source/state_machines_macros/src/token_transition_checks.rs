//! More sanity checks on transitions, checking properties specifically for
//! concurrency_tokens.rs

use crate::ast::{SplitKind, TransitionStmt, SM};
use syn_verus::parse;
use syn_verus::parse::Error;

/// Check if any SpecialOp is inside a conditional, which is currently unsupported.
/// e.g., this is disallowed:
///
/// if cond {
///    add_element(...);
/// }
///
/// Such a thing would mean we need "conditional arguments" in the exchange methods
/// (presumably via Option types) a feature that we don't implement.
///
/// Also checks to make sure there are no sub-updates.

pub fn check_unsupported_updates(ts: &TransitionStmt) -> parse::Result<()> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter() {
                check_unsupported_updates(child)?;
            }
            Ok(())
        }
        TransitionStmt::Split(_span, SplitKind::Let(..), es)
        | TransitionStmt::Split(_span, SplitKind::Special(..), es) => {
            for e in es {
                check_unsupported_updates(e)?;
            }
            Ok(())
        }
        TransitionStmt::Split(_span, SplitKind::If(..), es)
        | TransitionStmt::Split(_span, SplitKind::Match(..), es) => {
            for e in es {
                check_unsupported_updates_helper(e)?;
            }
            Ok(())
        }
        TransitionStmt::Require(..) => Ok(()),
        TransitionStmt::Assert(..) => Ok(()),
        TransitionStmt::Update(..) => Ok(()),
        TransitionStmt::SubUpdate(span, _, _, _) => Err(Error::new(
            *span,
            format!("field updates and index updates are not supported in tokenized transitions"),
        )),
        TransitionStmt::Initialize(..) => Ok(()),
        TransitionStmt::PostCondition(..) => Ok(()),
    }
}

fn check_unsupported_updates_helper(ts: &TransitionStmt) -> parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v {
                check_unsupported_updates_helper(t)?;
            }
            Ok(())
        }
        TransitionStmt::Split(span, SplitKind::Special(..), _) => {
            let name = ts.statement_name();
            return Err(Error::new(
                *span,
                format!("currently, '{name:}' statements are not supported inside conditionals"),
            ));
        }
        TransitionStmt::Split(_, _, es) => {
            for e in es {
                check_unsupported_updates_helper(e)?;
            }
            Ok(())
        }
        TransitionStmt::Require(_, _) => Ok(()),
        TransitionStmt::Assert(..) => Ok(()),
        TransitionStmt::Update(_, _, _) => Ok(()),
        TransitionStmt::SubUpdate(..) => Ok(()),
        TransitionStmt::Initialize(_, _, _) => Ok(()),
        TransitionStmt::PostCondition(..) => Ok(()),
    }
}

/// We require the token updates to go in remove -> have -> add order.
/// This isn't strictly necessary; however, doing otherwise might result in a transition
/// relation which is weaker than would be enforced by the exchange method.
///
/// The reason is that 'remove' corresponds to input tokens that are consumed
/// 'have' corresponds to readonly input tokens, and 'add' corresponds to output tokens.
/// However, this translation does not take into account the order of statements,
/// while the order of statements IS meaningful to the operational definitions of
/// have/remove/add for the purposes of constructing a relation.
/// And in particular, the exchange method corresponds to the remove -> have -> add order.
///
/// For example, suppose the user entered the commands in a different order:
///
/// have(x);
/// remove(y);
///
/// Operationally, this means that the starting state contains `x`, and then the state `y`
/// is removed. This means `x` and `y` might overlap. However, the exchange method will
/// take both 'x' and 'y' as tokens (the first read-only, the second not). But here, the
/// tokens are necessarily disjoint!
///
/// Note that we don't apply a similar restriction for withdraw/deposit/guard. For one thing,
/// 'guard' can only be in a readonly transiton and 'withdraw/deposit' in a normal transition.
/// So those can't interact at all. For another, there could conceivably be reason
/// to put 'withdraw' and 'deposit' in either order.

pub fn check_ordering_remove_have_add(sm: &SM, ts: &TransitionStmt) -> parse::Result<()> {
    for field in &sm.fields {
        check_ordering_remove_have_add_rec(ts, &field.name.to_string(), false, false)?;
    }
    Ok(())
}

pub fn check_ordering_remove_have_add_rec(
    ts: &TransitionStmt,
    field_name: &String,
    seen_have: bool,
    seen_add: bool,
) -> parse::Result<(bool, bool)> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut seen_have = seen_have;
            let mut seen_add = seen_add;
            for t in v {
                let (h, a) =
                    check_ordering_remove_have_add_rec(t, field_name, seen_have, seen_add)?;
                seen_have = h;
                seen_add = a;
            }
            Ok((seen_have, seen_add))
        }
        TransitionStmt::Split(span, split_kind, es) => {
            let mut seen_have = seen_have;
            let mut seen_add = seen_add;

            match split_kind {
                SplitKind::Special(id, op, _, _) => {
                    let msg = "updates for a field should always go in order 'remove -> have -> add'; otherwise, the transition relation may be weaker than necessary";
                    if id.to_string() == *field_name {
                        if op.is_remove() {
                            if seen_have || seen_add {
                                return Err(Error::new(*span, msg));
                            }
                        } else if op.is_have() {
                            if seen_add {
                                return Err(Error::new(*span, msg));
                            }
                            seen_have = true;
                        } else if op.is_add() {
                            seen_add = true;
                        }
                    }
                }
                _ => {}
            }

            let mut h = false;
            let mut a = false;

            assert!(es.len() > 0);
            for e in es {
                let (h1, a1) =
                    check_ordering_remove_have_add_rec(e, field_name, seen_have, seen_add)?;
                h |= h1;
                a |= a1;
            }
            Ok((h, a))
        }

        TransitionStmt::Require(..)
        | TransitionStmt::Assert(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::SubUpdate(..)
        | TransitionStmt::Initialize(..)
        | TransitionStmt::PostCondition(..) => Ok((seen_have, seen_add)),
    }
}
