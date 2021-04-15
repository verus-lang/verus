// Replace declare-var and assign with declare-const and assume
use crate::ast::{BinaryOp, Declaration, DeclarationX, ExprX, Ident, Query, QueryX, StmtX, Typ};
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
    let mut decls: Vec<Declaration> = Vec::new();
    let mut versions: HashMap<Ident, u32> = HashMap::new();
    let mut types: HashMap<Ident, Typ> = HashMap::new();
    for decl in local.iter() {
        if let DeclarationX::Var(x, t) = &**decl {
            versions.insert(x.clone(), 0);
            types.insert(x.clone(), t.clone());
            let x = Rc::new(rename_var(x, 0));
            let decl = Rc::new(DeclarationX::Const(x.clone(), t.clone()));
            decls.push(decl);
        } else {
            decls.push(decl.clone())
        }
    }
    let assertion = crate::visitor::map_stmt_visitor(assertion, &mut |s| {
        let s = crate::visitor::map_stmt_expr_visitor(s, &mut |e| match &**e {
            ExprX::Var(x) if versions.contains_key(x) => {
                let xn = rename_var(x, find_version(&versions, x));
                Rc::new(ExprX::Var(Rc::new(xn)))
            }
            _ => e.clone(),
        });
        match &*s {
            StmtX::Assign(x, e) => {
                let n = find_version(&versions, x);
                let typ = types[x].clone();
                versions.insert(x.clone(), n + 1);
                let x = Rc::new(rename_var(x, n + 1));
                let decl = Rc::new(DeclarationX::Const(x.clone(), typ));
                decls.push(decl);
                let expr1 = Rc::new(ExprX::Var(x));
                let expr = Rc::new(ExprX::Binary(BinaryOp::Eq, expr1, e.clone()));
                Rc::new(StmtX::Assume(expr))
            }
            _ => s,
        }
    });
    let local = Rc::new(decls.into_boxed_slice());
    Rc::new(QueryX { local, assertion })
}
