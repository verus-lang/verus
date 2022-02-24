use crate::ast::TransitionStmt;
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

pub fn check_ordering_remove_have_add(_ts: &TransitionStmt) -> syn::parse::Result<()> {
    //panic!("check_ordering_remove_have_add not implemented");
    // TODO implement this check
    Ok(())
}
