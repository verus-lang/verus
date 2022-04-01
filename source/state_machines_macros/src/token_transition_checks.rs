//! More sanity checks on transitions, checking properties specifically for
//! concurrency_tokens.rs

use crate::ast::{TransitionStmt, SM};
use syn::parse::Error;

/// Check if any SpecialOp is inside a conditional, which is currently unsupported.
/// e.g., this is disallowed:
///
/// if cond {
///    add_element(...);
/// }
///
/// Such a thing would mean we need "conditional arguments" in the exchange methods
/// (presumably via Option types) a feature that we don't implement.

pub fn check_unsupported_updates_in_conditionals(ts: &TransitionStmt) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter() {
                check_unsupported_updates_in_conditionals(child)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_span, _id, _ty, _lk, _init_e, child) => {
            check_unsupported_updates_in_conditionals(child)?;
            Ok(())
        }
        TransitionStmt::If(_span, _cond_e, e1, e2) => {
            check_unsupported_updates_helper(e1)?;
            check_unsupported_updates_helper(e2)?;
            Ok(())
        }
        TransitionStmt::Require(..) => Ok(()),
        TransitionStmt::Assert(..) => Ok(()),
        TransitionStmt::Update(..) => Ok(()),
        TransitionStmt::Initialize(..) => Ok(()),
        TransitionStmt::Special(..) => Ok(()),
        TransitionStmt::PostCondition(..) => Ok(()),
    }
}

fn check_unsupported_updates_helper(ts: &TransitionStmt) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v {
                check_unsupported_updates_helper(t)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_, _, _, _, _, child) => check_unsupported_updates_helper(child),
        TransitionStmt::If(_, _, e1, e2) => {
            check_unsupported_updates_helper(e1)?;
            check_unsupported_updates_helper(e2)?;
            Ok(())
        }
        TransitionStmt::Require(_, _) => Ok(()),
        TransitionStmt::Assert(..) => Ok(()),
        TransitionStmt::Update(_, _, _) => Ok(()),
        TransitionStmt::Initialize(_, _, _) => Ok(()),
        TransitionStmt::PostCondition(..) => Ok(()),

        TransitionStmt::Special(span, _, _, _) => {
            let name = ts.statement_name();
            return Err(Error::new(
                *span,
                format!("currently, a '{name:}' statement is not supported inside a conditional"),
            ));
        }
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

pub fn check_ordering_remove_have_add(sm: &SM, ts: &TransitionStmt) -> syn::parse::Result<()> {
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
) -> syn::parse::Result<(bool, bool)> {
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
        TransitionStmt::Let(_, _, _, _, _, child) => {
            check_ordering_remove_have_add_rec(child, field_name, seen_have, seen_add)
        }
        TransitionStmt::If(_, _, e1, e2) => {
            let (h1, a1) = check_ordering_remove_have_add_rec(e1, field_name, seen_have, seen_add)?;
            let (h2, a2) = check_ordering_remove_have_add_rec(e2, field_name, seen_have, seen_add)?;
            Ok((h1 || h2, a1 || a2))
        }

        TransitionStmt::Require(..)
        | TransitionStmt::Assert(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::Initialize(..)
        | TransitionStmt::PostCondition(..) => Ok((seen_have, seen_add)),

        TransitionStmt::Special(span, id, op, _) => {
            let msg = "updates for a field should always go in order 'remove -> have -> add'; otherwise, the transition relation may be weaker than necessary";
            if id.to_string() == *field_name {
                if op.is_remove() {
                    if seen_have || seen_add {
                        return Err(Error::new(*span, msg));
                    }
                    Ok((seen_have, seen_add))
                } else if op.is_have() {
                    if seen_add {
                        return Err(Error::new(*span, msg));
                    }
                    Ok((true, seen_add))
                } else if op.is_add() {
                    Ok((seen_have, true))
                } else {
                    Ok((seen_have, seen_add))
                }
            } else {
                Ok((seen_have, seen_add))
            }
        }
    }
}
