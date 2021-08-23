// Replace declare-var and assign with declare-const and assume
use crate::ast::{
    BinaryOp, Decl, DeclX, Expr, ExprX, Ident, Query, QueryX, Snapshots, Stmt, StmtX, Typ,
};
use crate::ast_util::string_var;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn find_version(versions: &HashMap<Ident, u32>, x: &String) -> u32 {
    *versions.get(x).unwrap_or_else(|| panic!("variable {} not declared", x))
}

pub fn rename_var(x: &String, n: u32) -> String {
    if x.ends_with("@") { format!("{}{}", x, n) } else { format!("{}@{}", x, n) }
}

fn lower_expr_visitor(versions: &HashMap<Ident, u32>, snapshots: &Snapshots, expr: &Expr) -> Expr {
    match &**expr {
        ExprX::Var(x) if versions.contains_key(x) => {
            let xn = rename_var(x, find_version(&versions, x));
            Arc::new(ExprX::Var(Arc::new(xn)))
        }
        ExprX::Old(snap, x) if snapshots.contains_key(snap) && snapshots[snap].contains_key(x) => {
            let xn = rename_var(x, find_version(&snapshots[snap], x));
            Arc::new(ExprX::Var(Arc::new(xn)))
        }
        ExprX::Old(_, x) => Arc::new(ExprX::Var(x.clone())),
        _ => expr.clone(),
    }
}

fn lower_expr(versions: &HashMap<Ident, u32>, snapshots: &Snapshots, expr: &Expr) -> Expr {
    crate::visitor::map_expr_visitor(&expr, &mut |e| lower_expr_visitor(versions, snapshots, e))
}

fn lower_stmt(
    decls: &mut Vec<Decl>,
    versions: &mut HashMap<Ident, u32>,
    version_decls: &mut HashSet<Ident>,
    snapshots: &mut Snapshots,
    all_snapshots: &mut Snapshots,
    types: &HashMap<Ident, Typ>,
    stmt: &Stmt,
) -> Stmt {
    let stmt = crate::visitor::map_stmt_expr_visitor(&stmt, &mut |e| {
        lower_expr_visitor(versions, snapshots, e)
    });
    match &*stmt {
        StmtX::Assume(_) | StmtX::Assert(_, _) => stmt,
        StmtX::Havoc(x) | StmtX::Assign(x, _) => {
            let n = find_version(&versions, x);
            let typ = types[x].clone();
            versions.insert(x.clone(), n + 1);
            let x = Arc::new(rename_var(x, n + 1));
            if !version_decls.contains(&x) {
                let decl = Arc::new(DeclX::Const(x.clone(), typ));
                decls.push(decl);
                version_decls.insert(x.clone());
            }
            match &*stmt {
                StmtX::Assign(_, e) => {
                    let expr1 = Arc::new(ExprX::Var(x));
                    let expr = Arc::new(ExprX::Binary(BinaryOp::Eq, expr1, e.clone()));
                    Arc::new(StmtX::Assume(expr))
                }
                _ => Arc::new(StmtX::Block(Arc::new(vec![]))),
            }
        }
        StmtX::Snapshot(snap) => {
            snapshots.insert(snap.clone(), versions.clone());
            all_snapshots.insert(snap.clone(), versions.clone());
            Arc::new(StmtX::Block(Arc::new(vec![])))
        }
        StmtX::Block(ss) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.push(lower_stmt(
                    decls,
                    versions,
                    version_decls,
                    snapshots,
                    all_snapshots,
                    types,
                    s,
                ));
            }
            Arc::new(StmtX::Block(Arc::new(stmts)))
        }
        StmtX::Switch(ss) if ss.len() == 0 => stmt,
        StmtX::Switch(ss) => {
            let mut all_versions: Vec<HashMap<Ident, u32>> = Vec::new();
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                let mut versions_i = versions.clone();
                let mut snapshots_i = snapshots.clone();
                stmts.push(lower_stmt(
                    decls,
                    &mut versions_i,
                    version_decls,
                    &mut snapshots_i,
                    all_snapshots,
                    types,
                    s,
                ));
                all_versions.push(versions_i);
                all_snapshots.extend(snapshots_i);
            }
            for x in all_versions[0].keys() {
                // For each variable x, the different branches may have different versions[x],
                // so choose the maximum versions[x] from all the branches,
                // and have every branch assign to that maximum version.
                versions.insert(x.clone(), all_versions.iter().map(|v| v[x]).max().unwrap());
            }
            for i in 0..ss.len() {
                let mut branch: Vec<Stmt> = Vec::new();
                branch.push(stmts[i].clone());
                let versions_i = &all_versions[i];
                for x in versions.keys() {
                    // Make sure this branch assigns to maximum version of x
                    if versions_i[x] < versions[x] {
                        let xk = string_var(&rename_var(x, versions_i[x]));
                        let xm = string_var(&rename_var(x, versions[x]));
                        let eq = Arc::new(ExprX::Binary(BinaryOp::Eq, xm, xk));
                        branch.push(Arc::new(StmtX::Assume(eq)));
                    }
                }
                stmts[i] = Arc::new(StmtX::Block(Arc::new(branch)));
            }
            Arc::new(StmtX::Switch(Arc::new(stmts)))
        }
    }
}

pub(crate) fn lower_query(query: &Query) -> (Query, Snapshots, Vec<Decl>) {
    let QueryX { local, assertion } = &**query;
    let mut decls: Vec<Decl> = Vec::new();
    let mut versions: HashMap<Ident, u32> = HashMap::new();
    let mut version_decls: HashSet<Ident> = HashSet::new();
    let mut snapshots: Snapshots = HashMap::new();
    let mut all_snapshots: Snapshots = HashMap::new();
    let mut types: HashMap<Ident, Typ> = HashMap::new();
    let mut local_vars: Vec<Decl> = Vec::new();

    for decl in local.iter() {
        if let DeclX::Axiom(expr) = &**decl {
            let decl_x = DeclX::Axiom(lower_expr(&versions, &snapshots, expr));
            decls.push(Arc::new(decl_x));
        } else {
            decls.push(decl.clone());
        }
        if let DeclX::Var(x, t) = &**decl {
            versions.insert(x.clone(), 0);
            types.insert(x.clone(), t.clone());
            let x = Arc::new(rename_var(x, 0));
            let decl = Arc::new(DeclX::Const(x.clone(), t.clone()));
            decls.push(decl);
        }
        if let DeclX::Const(_, _) = &**decl {
            local_vars.push(decl.clone());
        }
    }
    let assertion = lower_stmt(
        &mut decls,
        &mut versions,
        &mut version_decls,
        &mut snapshots,
        &mut all_snapshots,
        &types,
        assertion,
    );
    let local = Arc::new(decls);
    (Arc::new(QueryX { local, assertion }), all_snapshots, local_vars)
}
