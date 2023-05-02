use crate::ast::{Expr, ExprX, FunctionX, GenericBoundX, Krate, KrateX, Typ, TypX, UnaryOpr};
use crate::ast_visitor::{
    expr_visitor_check, expr_visitor_dfs, typ_visitor_check, VisitorControlFlow, VisitorScopeMap,
};
pub use air::ast_util::{ident_binder, str_ident};

fn check_expr_simplified(_scope_map: &VisitorScopeMap, expr: &Expr) -> Result<(), ()> {
    match expr.x {
        ExprX::ConstVar(_)
        | ExprX::UnaryOpr(UnaryOpr::TupleField { .. }, _)
        | ExprX::Tuple(_)
        | ExprX::Match(..) => Err(()),
        _ => Ok(()),
    }
}

fn check_typ_simplified(typ: &Typ) -> Result<(), ()> {
    match &**typ {
        TypX::Tuple(..) => Err(()),
        _ => Ok(()),
    }
}

/// Panics if the ast uses nodes that should have been removed by ast_simplify
pub fn check_krate_simplified(krate: &Krate) {
    check_krate(krate);

    let KrateX {
        functions,
        datatypes,
        traits: _,
        module_ids: _,
        external_fns: _,
        external_types: _,
    } = &**krate;

    for function in functions {
        let FunctionX { require, ensure, decrease, body, typ_bounds, params, ret, .. } =
            &function.x;

        let all_exprs =
            require.iter().chain(ensure.iter()).chain(decrease.iter()).chain(body.iter());
        for expr in all_exprs {
            expr_visitor_check(expr, &mut check_expr_simplified)
                .expect("function AST expression uses node that should have been simplified");
        }

        for (_, bound) in typ_bounds.iter() {
            match &**bound {
                GenericBoundX::Traits(_) => {}
            }
        }

        for param in params.iter().chain(std::iter::once(ret)) {
            typ_visitor_check(&param.x.typ, &mut check_typ_simplified)
                .expect("function param typ uses node that should have been simplified");
        }
    }

    for datatype in datatypes {
        for variant in datatype.x.variants.iter() {
            for field in variant.a.iter() {
                let (typ, _, _) = &field.a;
                typ_visitor_check(typ, &mut check_typ_simplified)
                    .expect("datatype field typ uses node that should have been simplified");
            }
        }
    }
}

fn expr_no_loc_in_spec(
    expr: &Expr,
    scope_map: &mut VisitorScopeMap,
    in_spec: bool,
) -> VisitorControlFlow<()> {
    let mut recurse_in_spec = |e| match expr_visitor_dfs(
        e,
        scope_map,
        &mut |scope_map: &mut VisitorScopeMap, expr: &Expr| {
            expr_no_loc_in_spec(expr, scope_map, true)
        },
    ) {
        VisitorControlFlow::Recurse | VisitorControlFlow::Return => Ok(false),
        VisitorControlFlow::Stop(()) => Err(()),
    };
    match match &expr.x {
        ExprX::Quant(_q, _b, qexpr) => recurse_in_spec(qexpr),
        ExprX::Choose { params: _, cond, body } => {
            recurse_in_spec(cond).and_then(|_| recurse_in_spec(body))
        }
        ExprX::Forall { vars: _, require, ensure, proof: _ } => {
            recurse_in_spec(require).and_then(|_| recurse_in_spec(ensure))
        }
        ExprX::VarLoc(_) | ExprX::Loc(_) if in_spec => Err(()),
        _ => Ok(true),
    } {
        Ok(true) => VisitorControlFlow::Recurse,
        Ok(false) => VisitorControlFlow::Return,
        Err(()) => VisitorControlFlow::Stop(()),
    }
}

/// Panics if the ast uses nodes that should have been removed by ast_simplify
pub fn check_krate(krate: &Krate) {
    let KrateX {
        functions,
        datatypes: _,
        traits: _,
        module_ids: _,
        external_fns: _,
        external_types: _,
    } = &**krate;

    for function in functions {
        let FunctionX { require, ensure, decrease, body, .. } = &function.x;

        let all_exprs =
            require.iter().chain(ensure.iter()).chain(decrease.iter()).chain(body.iter());
        for expr in all_exprs {
            match expr_visitor_dfs(
                expr,
                &mut air::scope_map::ScopeMap::new(),
                &mut |scope_map: &mut VisitorScopeMap, expr: &Expr| {
                    expr_no_loc_in_spec(expr, scope_map, false)
                },
            ) {
                VisitorControlFlow::Recurse | VisitorControlFlow::Return => Ok(()),
                VisitorControlFlow::Stop(()) => Err(()),
            }
            .expect("function AST expression uses node that should have been simplified");
        }
    }
}
