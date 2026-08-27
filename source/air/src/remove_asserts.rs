use crate::ast::{Stmt, StmtX};
use std::sync::Arc;

pub fn remove_asserts(stmt: &Stmt) -> Stmt {
    match &**stmt {
        StmtX::Assert(_assert_id_opt, _msg, _filter, _e) => {
            Arc::new(StmtX::Block(Arc::new(vec![])))
        }
        StmtX::Assume(..) => stmt.clone(),
        StmtX::Havoc(..) | StmtX::Assign(..) | StmtX::Snapshot(..) => stmt.clone(),
        StmtX::DeadEnd(_stmt) => {
            // We can skip this entirely since it can't have any effect on what comes after
            Arc::new(StmtX::Block(Arc::new(vec![])))
        }
        StmtX::Breakable(ident, stmt) => {
            let stmt = remove_asserts(stmt);
            Arc::new(StmtX::Breakable(ident.clone(), stmt))
        }
        StmtX::Break(_) => stmt.clone(),
        StmtX::Block(stmts) => {
            let mut v = vec![];
            for stmt in stmts.iter() {
                let stmt = remove_asserts(stmt);
                if !crate::focus::is_trivial(&stmt) {
                    v.push(stmt);
                }
            }
            Arc::new(StmtX::Block(Arc::new(v)))
        }
        StmtX::Switch(stmts) => {
            let mut v = vec![];
            for stmt in stmts.iter() {
                let stmt = remove_asserts(stmt);
                v.push(stmt);
            }
            Arc::new(StmtX::Switch(Arc::new(v)))
        }
    }
}
