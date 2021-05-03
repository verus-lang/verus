// Replace declare-var and assign with declare-const and assume
use crate::ast::{BinaryOp, Decl, DeclX, ExprX, Ident, Query, QueryX, StmtX, Typ};
use std::collections::HashMap;
use std::rc::Rc;

fn find_version(versions: &HashMap<Ident, u32>, x: &String) -> u32 {
    match versions.get(x) {
        None => panic!("variable {} not declared", x),
        Some(n) => *n,
    }
}

fn rename_var(x: &String, n: u32) -> String {
    if x.ends_with("@") { format!("{}{}", x, n) } else { format!("{}@{}", x, n) }
}

pub(crate) fn lower_query(query: &Query) -> Query {
    let QueryX { local, assertion } = &**query;
    let mut decls: Vec<Decl> = Vec::new();
    let mut versions: HashMap<Ident, u32> = HashMap::new();
    let mut snapshots: HashMap<Ident, HashMap<Ident, u32>> = HashMap::new();
    let mut types: HashMap<Ident, Typ> = HashMap::new();
    for decl in local.iter() {
        decls.push(decl.clone());
        if let DeclX::Var(x, t) = &**decl {
            versions.insert(x.clone(), 0);
            types.insert(x.clone(), t.clone());
            let x = Rc::new(rename_var(x, 0));
            let decl = Rc::new(DeclX::Const(x.clone(), t.clone()));
            decls.push(decl);
        }
    }
    let assertion = crate::visitor::map_stmt_visitor(assertion, &mut |s| {
        let s = crate::visitor::map_stmt_expr_visitor(s, &mut |e| match &**e {
            ExprX::Var(x) if versions.contains_key(x) => {
                let xn = rename_var(x, find_version(&versions, x));
                Rc::new(ExprX::Var(Rc::new(xn)))
            }
            ExprX::Old(snap, x)
                if snapshots.contains_key(snap) && snapshots[snap].contains_key(x) =>
            {
                let xn = rename_var(x, find_version(&snapshots[snap], x));
                Rc::new(ExprX::Var(Rc::new(xn)))
            }
            ExprX::Old(_, x) => Rc::new(ExprX::Var(x.clone())),
            _ => e.clone(),
        });
        match &*s {
            StmtX::Havoc(x) | StmtX::Assign(x, _) => {
                let n = find_version(&versions, x);
                let typ = types[x].clone();
                versions.insert(x.clone(), n + 1);
                let x = Rc::new(rename_var(x, n + 1));
                let decl = Rc::new(DeclX::Const(x.clone(), typ));
                decls.push(decl);
                match &*s {
                    StmtX::Assign(_, e) => {
                        let expr1 = Rc::new(ExprX::Var(x));
                        let expr = Rc::new(ExprX::Binary(BinaryOp::Eq, expr1, e.clone()));
                        Rc::new(StmtX::Assume(expr))
                    }
                    _ => Rc::new(StmtX::Block(Rc::new(vec![]))),
                }
            }
            StmtX::Snapshot(snap) => {
                snapshots.insert(snap.clone(), versions.clone());
                Rc::new(StmtX::Block(Rc::new(vec![])))
            }
            _ => s,
        }
    });
    let local = Rc::new(decls);
    Rc::new(QueryX { local, assertion })
}
