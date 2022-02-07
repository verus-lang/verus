use crate::ast::{Expr, ExprX, FunctionX, GenericBoundX, Krate, KrateX, Typ, TypX, UnaryOpr};
use crate::ast_visitor::{
    expr_visitor_check, expr_visitor_dfs, typ_visitor_check, VisitorControlFlow, VisitorScopeMap,
};
pub use air::ast_util::{ident_binder, str_ident};

fn check_expr_simplified(expr: &Expr) -> Result<(), ()> {
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

    let KrateX { functions, datatypes, module_ids: _ } = &**krate;

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
                GenericBoundX::None => (),
                GenericBoundX::FnSpec(typs, typ) => {
                    let all_typs = typs.iter().chain(std::iter::once(typ));
                    for typ in all_typs {
                        typ_visitor_check(typ, &mut check_typ_simplified).expect(
                            "function typ bound uses node that should have been simplified",
                        );
                    }
                }
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

fn expr_no_loc_in_quant(
    expr: &Expr,
    scope_map: &mut VisitorScopeMap,
    in_quant: bool,
) -> VisitorControlFlow<()> {
    match &expr.x {
        ExprX::Quant(_q, _b, qexpr) => match expr_visitor_dfs(
            qexpr,
            scope_map,
            &mut |scope_map: &mut VisitorScopeMap, expr: &Expr| {
                expr_no_loc_in_quant(expr, scope_map, true)
            },
        ) {
            VisitorControlFlow::Recurse | VisitorControlFlow::Return => VisitorControlFlow::Return,
            VisitorControlFlow::Stop(()) => VisitorControlFlow::Stop(()),
        },
        ExprX::VarLoc(_) | ExprX::Loc(_) if in_quant => VisitorControlFlow::Stop(()),
        _ => VisitorControlFlow::Recurse,
    }
}

/// Panics if the ast uses nodes that should have been removed by ast_simplify
pub fn check_krate(krate: &Krate) {
    let KrateX { functions, datatypes: _, module_ids: _ } = &**krate;

    for function in functions {
        let FunctionX { require, ensure, decrease, body, .. } = &function.x;

        let all_exprs =
            require.iter().chain(ensure.iter()).chain(decrease.iter()).chain(body.iter());
        for expr in all_exprs {
            match expr_visitor_dfs(
                expr,
                &mut air::scope_map::ScopeMap::new(),
                &mut |scope_map: &mut VisitorScopeMap, expr: &Expr| {
                    expr_no_loc_in_quant(expr, scope_map, false)
                },
            ) {
                VisitorControlFlow::Recurse | VisitorControlFlow::Return => Ok(()),
                VisitorControlFlow::Stop(()) => Err(()),
            }
            .expect("function AST expression uses node that should have been simplified");
        }
    }
}
