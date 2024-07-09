// Replace declare-var and assign with declare-const and assume
use crate::ast::{
    Axiom, BinaryOp, Decl, DeclX, Expr, ExprX, Ident, Query, QueryX, Snapshots, Stmt, StmtX, Typ,
};
use crate::ast_util::string_var;
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn find_version(versions: &IndexMap<Ident, u32>, x: &String) -> u32 {
    *versions.get(x).unwrap_or_else(|| panic!("variable {} not declared", x))
}

pub fn rename_var(x: &String, n: u32) -> String {
    if x.ends_with("@") { format!("{}{}", x, n) } else { format!("{}@{}", x, n) }
}

fn lower_expr_visitor(versions: &IndexMap<Ident, u32>, snapshots: &Snapshots, expr: &Expr) -> Expr {
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

fn lower_expr(versions: &IndexMap<Ident, u32>, snapshots: &Snapshots, expr: &Expr) -> Expr {
    crate::visitor::map_expr_visitor(&expr, &mut |e| lower_expr_visitor(versions, snapshots, e))
}

fn update_versions_from_all_branches(
    all_versions: &Vec<IndexMap<Ident, u32>>,
    versions: &mut IndexMap<Ident, u32>,
) {
    for x in all_versions[0].keys() {
        // For each variable x, the different branches may have different versions[x],
        // so choose the maximum versions[x] from all the branches,
        // and have every branch assign to that maximum version.
        versions.insert(x.clone(), all_versions.iter().map(|v| v[x]).max().unwrap());
    }
}

// Bring stmt, currently at versions_from, up to date with versions_to
fn update_branch_to_versions(
    versions_from: &IndexMap<Ident, u32>,
    versions_to: &IndexMap<Ident, u32>,
    stmt: &Stmt,
    update_before: bool,
) -> Stmt {
    let mut branch: Vec<Stmt> = Vec::new();
    if !update_before {
        branch.push(stmt.clone());
    }
    for x in versions_to.keys() {
        // Make sure this branch assigns to maximum version of x
        if versions_from[x] < versions_to[x] {
            let xk = string_var(&rename_var(x, versions_from[x]));
            let xm = string_var(&rename_var(x, versions_to[x]));
            let eq = Arc::new(ExprX::Binary(BinaryOp::Eq, xm, xk));
            branch.push(Arc::new(StmtX::Assume(eq)));
        }
    }
    if update_before {
        branch.push(stmt.clone());
    }
    Arc::new(StmtX::Block(Arc::new(branch)))
}

fn update_breaks_to_versions(
    label: &Ident,
    all_versions: &Vec<IndexMap<Ident, u32>>,
    versions_to: &IndexMap<Ident, u32>,
    break_i: &mut usize,
    stmt: &Stmt,
) -> Stmt {
    match &**stmt {
        StmtX::Assume(_) | StmtX::Assert(..) => stmt.clone(),
        StmtX::Havoc(_) | StmtX::Assign(..) => stmt.clone(),
        StmtX::Snapshot(_) => stmt.clone(),
        StmtX::DeadEnd(s) => {
            let s = update_breaks_to_versions(label, all_versions, versions_to, break_i, s);
            Arc::new(StmtX::DeadEnd(s))
        }
        StmtX::Breakable(x, s) => {
            let s = update_breaks_to_versions(label, all_versions, versions_to, break_i, s);
            Arc::new(StmtX::Breakable(x.clone(), s))
        }
        StmtX::Break(x) if x == label => {
            let s = update_branch_to_versions(&all_versions[*break_i], versions_to, &stmt, true);
            *break_i += 1;
            s
            // Note: after the break, we may later merge the (unreachable) path following the break
            // with other paths, which may add more equality assumptions along the unreachable path.
            // This assumptions will be irrelevant, since they can't be reached.
            // The only assumptions that matter are the reachable ones we introduce here.
        }
        StmtX::Break(_) => stmt.clone(),
        StmtX::Block(ss) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.push(update_breaks_to_versions(label, all_versions, versions_to, break_i, s));
            }
            Arc::new(StmtX::Block(Arc::new(stmts)))
        }
        StmtX::Switch(ss) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.push(update_breaks_to_versions(label, all_versions, versions_to, break_i, s));
            }
            Arc::new(StmtX::Switch(Arc::new(stmts)))
        }
    }
}

struct LowerStmtState {
    decls: Vec<Decl>,
    break_versions: HashMap<Ident, Vec<IndexMap<Ident, u32>>>,
    version_decls: HashSet<Ident>,
    all_snapshots: Snapshots,
}

fn lower_stmt(
    state: &mut LowerStmtState,
    versions: &mut IndexMap<Ident, u32>,
    snapshots: &mut Snapshots,
    types: &HashMap<Ident, Typ>,
    stmt: &Stmt,
) -> Stmt {
    let stmt = crate::visitor::map_stmt_expr_visitor(&stmt, &mut |e| {
        lower_expr_visitor(versions, snapshots, e)
    });
    match &*stmt {
        StmtX::Assume(_) | StmtX::Assert(..) => stmt,
        StmtX::Havoc(x) | StmtX::Assign(x, _) => {
            let n = find_version(&versions, x);
            let typ = types[x].clone();
            versions.insert(x.clone(), n + 1);
            let x = Arc::new(rename_var(x, n + 1));
            if !state.version_decls.contains(&x) {
                let decl = Arc::new(DeclX::Const(x.clone(), typ));
                state.decls.push(decl);
                state.version_decls.insert(x.clone());
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
            state.all_snapshots.insert(snap.clone(), versions.clone());
            Arc::new(StmtX::Block(Arc::new(vec![])))
        }
        StmtX::DeadEnd(s) => {
            let s = lower_stmt(state, versions, snapshots, types, s);
            Arc::new(StmtX::DeadEnd(s))
        }
        StmtX::Breakable(label, s) => {
            state
                .break_versions
                .insert(label.clone(), Vec::new())
                .map(|_| panic!("break_versions"));
            let s = lower_stmt(state, versions, snapshots, types, s);
            // See the Switch case below.
            // This is similar to Switch, where:
            // - Switch has n branches
            // - Breakable(L, s) has 1 non-breaking "branch" plus 1 "branch" for each Break(L)
            // However, the breaks may be embedded deep inside s,
            // so we need a second pass through s to ensure that all the breaks have the same
            // version (the maximum version) of each variable x.
            let mut all_versions: Vec<IndexMap<Ident, u32>> =
                state.break_versions.remove(label).expect("break_versions");
            all_versions.insert(0, versions.clone());
            update_versions_from_all_branches(&all_versions, versions);
            let mut break_i: usize = 1;
            let s = update_breaks_to_versions(label, &all_versions, versions, &mut break_i, &s);
            assert!(break_i == all_versions.len());
            let s = update_branch_to_versions(&all_versions[0], versions, &s, false);
            Arc::new(StmtX::Breakable(label.clone(), s))
        }
        StmtX::Break(label) => {
            state.break_versions.get_mut(label).expect("break_versions").push(versions.clone());
            stmt
        }
        StmtX::Block(ss) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                stmts.push(lower_stmt(state, versions, snapshots, types, s));
            }
            Arc::new(StmtX::Block(Arc::new(stmts)))
        }
        StmtX::Switch(ss) if ss.len() == 0 => stmt,
        StmtX::Switch(ss) => {
            let mut all_versions: Vec<IndexMap<Ident, u32>> = Vec::new();
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                let mut versions_i = versions.clone();
                let mut snapshots_i = snapshots.clone();
                stmts.push(lower_stmt(state, &mut versions_i, &mut snapshots_i, types, s));
                all_versions.push(versions_i);
                state.all_snapshots.extend(snapshots_i);
            }
            update_versions_from_all_branches(&all_versions, versions);
            for i in 0..ss.len() {
                stmts[i] = update_branch_to_versions(&all_versions[i], versions, &stmts[i], false);
            }
            Arc::new(StmtX::Switch(Arc::new(stmts)))
        }
    }
}

pub(crate) fn lower_query(query: &Query) -> (Query, Snapshots, Vec<Decl>) {
    let QueryX { local, assertion } = &**query;
    let mut decls: Vec<Decl> = Vec::new();
    let mut versions: IndexMap<Ident, u32> = IndexMap::new();
    let break_versions: HashMap<Ident, Vec<IndexMap<Ident, u32>>> = HashMap::new();
    let version_decls: HashSet<Ident> = HashSet::new();
    let mut snapshots: Snapshots = HashMap::new();
    let all_snapshots: Snapshots = HashMap::new();
    let mut types: HashMap<Ident, Typ> = HashMap::new();
    let mut local_vars: Vec<Decl> = Vec::new();

    for decl in local.iter() {
        if let DeclX::Axiom(Axiom { named, expr }) = &**decl {
            let decl_x = DeclX::Axiom(Axiom {
                named: named.clone(),
                expr: lower_expr(&versions, &snapshots, expr),
            });
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
    let mut state = LowerStmtState { decls, break_versions, version_decls, all_snapshots };
    let assertion = lower_stmt(&mut state, &mut versions, &mut snapshots, &types, assertion);
    let local = Arc::new(state.decls);
    (Arc::new(QueryX { local, assertion }), state.all_snapshots, local_vars)
}
