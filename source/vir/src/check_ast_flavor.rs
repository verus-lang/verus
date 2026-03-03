use crate::ast::{
    Expr, ExprX, Function, FunctionX, GenericBoundX, Idents, Krate, KrateX, MaskSpec, Typ, TypX,
};
use crate::ast_visitor::{
    VisitorControlFlow, VisitorScopeMap, expr_visitor_check, expr_visitor_dfs, typ_visitor_check,
};
pub use air::ast_util::{ident_binder, str_ident};
use std::sync::Arc;

fn check_expr_simplified(expr: &Expr, function: &Function) -> Result<(), ()> {
    check_typ_simplified(&expr.typ, &function.x.typ_params)?;
    match expr.x {
        ExprX::ConstVar(..) | ExprX::Match(..) => Err(()),
        _ => Ok(()),
    }
}

fn check_typ_simplified(typ: &Typ, typ_params: &Idents) -> Result<(), ()> {
    match &**typ {
        TypX::TypParam(id) if !typ_params.contains(id) => Err(()),
        _ => Ok(()),
    }
}

/// Panics if the ast uses nodes that should have been removed by ast_simplify
pub fn check_krate_simplified(krate: &Krate) {
    check_krate(krate);

    let KrateX {
        functions,
        reveal_groups: _,
        datatypes,
        opaque_types: _,
        traits: _,
        trait_impls: _,
        assoc_type_impls: _,
        modules: _,
        external_fns: _,
        external_types: _,
        path_as_rust_names: _,
        arch: _,
    } = &**krate;

    for function in functions {
        let FunctionX {
            require,
            ensure: (ensure0, ensure1),
            decrease,
            body,
            typ_bounds,
            params,
            ret,
            mask_spec,
            body_visibility,
            ..
        } = &function.x;

        if let crate::ast::BodyVisibility::Uninterpreted = body_visibility {
            assert!(body.is_none());
        }

        let mask_exprs = match mask_spec {
            Some(MaskSpec::InvariantOpens(_span, es)) => es.clone(),
            Some(MaskSpec::InvariantOpensExcept(_span, es)) => es.clone(),
            Some(MaskSpec::InvariantOpensSet(e)) => Arc::new(vec![e.clone()]),
            None => Arc::new(vec![]),
        };

        let all_exprs = require
            .iter()
            .chain(ensure0.iter())
            .chain(ensure1.iter())
            .chain(decrease.iter())
            .chain(body.iter())
            .chain(mask_exprs.iter());
        for expr in all_exprs {
            expr_visitor_check(expr, &mut |_, e| check_expr_simplified(e, function))
                .expect("function AST expression uses node that should have been simplified");
        }

        for bound in typ_bounds.iter() {
            match &**bound {
                GenericBoundX::Trait(_, ts) => {
                    for t in ts.iter() {
                        typ_visitor_check(t, &mut |t| {
                            check_typ_simplified(t, &function.x.typ_params)
                        })
                        .expect("function param bound uses node that should have been simplified");
                    }
                }
                GenericBoundX::TypEquality(_, ts, _, t) => {
                    for t in ts.iter().chain(vec![t].into_iter()) {
                        typ_visitor_check(t, &mut |t| {
                            check_typ_simplified(t, &function.x.typ_params)
                        })
                        .expect("function param bound uses node that should have been simplified");
                    }
                }
                GenericBoundX::ConstTyp(t, s) => {
                    for t in [t, s] {
                        typ_visitor_check(t, &mut |t| {
                            check_typ_simplified(t, &function.x.typ_params)
                        })
                        .expect("function param bound uses node that should have been simplified");
                    }
                }
            }
        }

        for param in params.iter().chain(std::iter::once(ret)) {
            typ_visitor_check(&param.x.typ, &mut |t| {
                check_typ_simplified(t, &function.x.typ_params)
            })
            .expect("function param typ uses node that should have been simplified");
        }
    }

    for datatype in datatypes {
        let typ_params = Arc::new(datatype.x.typ_params.iter().map(|(id, _)| id.clone()).collect());
        for variant in datatype.x.variants.iter() {
            for field in variant.fields.iter() {
                let (typ, _, _) = &field.a;
                typ_visitor_check(typ, &mut |t| check_typ_simplified(t, &typ_params))
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
        ExprX::AssertBy { vars: _, require, ensure, proof: _ } => {
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
        reveal_groups: _,
        datatypes: _,
        opaque_types: _,
        traits: _,
        trait_impls: _,
        assoc_type_impls: _,
        modules: _,
        external_fns: _,
        external_types: _,
        path_as_rust_names: _,
        arch: _,
    } = &**krate;

    for function in functions {
        let FunctionX { require, ensure: (ensure0, ensure1), decrease, body, .. } = &function.x;

        let all_exprs = require
            .iter()
            .chain(ensure0.iter())
            .chain(ensure1.iter())
            .chain(decrease.iter())
            .chain(body.iter());
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
