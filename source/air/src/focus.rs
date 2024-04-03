use crate::ast::{AssertId, Command, CommandX, Commands, QueryX, Stmt, StmtX};
use std::sync::Arc;

pub fn focus_commands_on_assert_id(commands: &Commands, assert_id: &AssertId) -> Commands {
    Arc::new(commands.iter().filter_map(|c| focus_command_on_assert_id(c, assert_id)).collect())
}

pub fn focus_command_on_assert_id(command: &Command, assert_id: &AssertId) -> Option<Command> {
    match &**command {
        CommandX::Push | CommandX::Pop | CommandX::SetOption(..) | CommandX::Global(..) => {
            Some(command.clone())
        }
        CommandX::CheckValid(query) => {
            let (assertion, found) = focus_stmt_on_assert_id(&query.assertion, assert_id);
            if !found {
                return None;
            }
            let query = Arc::new(QueryX { local: query.local.clone(), assertion });
            Some(Arc::new(CommandX::CheckValid(query)))
        }
        #[cfg(feature = "singular")]
        CommandX::CheckSingular(..) => {
            // TODO: what should we do here?
            None
        }
    }
}

pub fn focus_stmt_on_assert_id(stmt: &Stmt, assert_id: &AssertId) -> (Stmt, bool) {
    match &**stmt {
        StmtX::Assert(assert_id_opt, _msg, _filter, _e) => {
            if assert_id_opt == &Some(assert_id.clone()) {
                (stmt.clone(), true)
            } else {
                (Arc::new(StmtX::Block(Arc::new(vec![]))), false)
            }
        }
        StmtX::Assume(..) => (stmt.clone(), false),
        StmtX::Havoc(..) | StmtX::Assign(..) | StmtX::Snapshot(..) => (stmt.clone(), false),
        StmtX::DeadEnd(stmt) => {
            let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
            if found {
                (Arc::new(StmtX::DeadEnd(stmt)), true)
            } else {
                (Arc::new(StmtX::Block(Arc::new(vec![]))), false)
            }
        }
        StmtX::Breakable(ident, stmt) => {
            let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
            (Arc::new(StmtX::Breakable(ident.clone(), stmt)), found)
        }
        StmtX::Break(_) => (stmt.clone(), false),
        StmtX::Block(stmts) => {
            let mut v = vec![];
            for stmt in stmts.iter() {
                let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
                if !is_trivial(&stmt) {
                    v.push(stmt);
                }
                if found {
                    // If found in one of the cases, we just drop everything after it
                    return (Arc::new(StmtX::Block(Arc::new(v))), true);
                }
            }
            (Arc::new(StmtX::Block(Arc::new(v))), false)
        }
        StmtX::Switch(stmts) => {
            let mut v = vec![];
            for stmt in stmts.iter() {
                let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
                if found {
                    // If found in one of the cases, we just drop all the other cases
                    return (stmt, true);
                }
                v.push(stmt);
            }
            (Arc::new(StmtX::Switch(Arc::new(v))), false)
        }
    }
}

fn is_trivial(stmt: &Stmt) -> bool {
    match &**stmt {
        StmtX::Block(stmts) => stmts.len() == 0,
        _ => false,
    }
}
