use crate::ast::{SM, TransitionStmt};
use syn::parse::Error;

pub fn check_unsupported_updates_in_conditionals(ts: &TransitionStmt) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter() {
                check_unsupported_updates_in_conditionals(child)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_span, _id, _init_e) => Ok(()),
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
        TransitionStmt::Let(_, _, _) => Ok(()),
        TransitionStmt::If(_, _, e1, e2) => {
            check_unsupported_updates_helper(e1)?;
            check_unsupported_updates_helper(e2)?;
            Ok(())
        }
        TransitionStmt::Require(_, _) => Ok(()),
        TransitionStmt::Assert(_, _) => Ok(()),
        TransitionStmt::Update(_, _, _) => Ok(()),
        TransitionStmt::Initialize(_, _, _) => Ok(()),
        TransitionStmt::PostCondition(..) => Ok(()),

        TransitionStmt::Special(span, _, _) => {
            let name = ts.statement_name();
            return Err(Error::new(
                *span,
                format!("currently, a '{name:}' statement is not supported inside a conditional"),
            ));
        }
    }
}

pub fn check_ordering_remove_have_add(sm: &SM, ts: &TransitionStmt) -> syn::parse::Result<()> {
    for field in &sm.fields {
        check_ordering_remove_have_add_rec(ts, &field.ident.to_string(), false, false)?;
    }
    Ok(())
}

pub fn check_ordering_remove_have_add_rec(ts: &TransitionStmt,
      field_name: &String,
      seen_have: bool,
      seen_add: bool
) -> syn::parse::Result<(bool, bool)> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut seen_have = seen_have;
            let mut seen_add = seen_add;
            for t in v {
                let (h, a) = check_ordering_remove_have_add_rec(t, field_name, seen_have, seen_add)?;
                seen_have = h;
                seen_add = a;
            }
            Ok((seen_have, seen_add))
        }
        TransitionStmt::If(_, _, e1, e2) => {
            let (h1, a1) = check_ordering_remove_have_add_rec(e1, field_name, seen_have, seen_add)?;
            let (h2, a2) = check_ordering_remove_have_add_rec(e2, field_name, seen_have, seen_add)?;
            Ok((h1 || h2, a1 || a2))
        }

        TransitionStmt::Let(_, _, _) |
        TransitionStmt::Require(_, _) |
        TransitionStmt::Assert(_, _) |
        TransitionStmt::Update(_, _, _) |
        TransitionStmt::Initialize(_, _, _) |
        TransitionStmt::PostCondition(..) => {
            Ok((seen_have, seen_add))
        }

        TransitionStmt::Special(span, id, op) => {
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
