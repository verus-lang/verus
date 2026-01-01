use crate::ast::*;
use crate::ast_visitor::VisitorScopeMap;
use air::scope_map::ScopeMap;
use std::collections::HashSet;
use std::sync::Arc;

/// Port every functions signature from old-style to new-mut-ref style
pub fn ignore_mut_ref_only_fns(krate: Krate) -> Krate {
    let mut krate = krate;
    let kratex = Arc::make_mut(&mut krate);
    let functions = std::mem::take(&mut kratex.functions);
    kratex.functions =
        functions.into_iter().filter(|f| !f.x.attrs.ignore_outside_new_mut_ref).collect();
    krate
}

/// Port every functions signature from old-style to new-mut-ref style
pub fn migrate_mut_ref_krate(krate: Krate) -> Krate {
    let mut krate = krate;
    let kratex = Arc::make_mut(&mut krate);
    for function in kratex.functions.iter_mut() {
        migrate_mut_ref_function(function);
    }
    krate
}

/// Port the function's signature from old-style to new-mut-ref style
pub fn migrate_mut_ref_function(f: &mut Function) {
    let fx = &mut Arc::make_mut(f).x;

    let mut params_migrated: HashSet<VarIdent> = HashSet::new();
    let new_params = Arc::new(
        fx.params
            .iter()
            .map(&mut |p: &Param| {
                if p.x.is_mut {
                    params_migrated.insert(p.x.name.clone());
                    p.new_x(ParamX {
                        name: p.x.name.clone(),
                        typ: Arc::new(TypX::MutRef(p.x.typ.clone())),
                        mode: p.x.mode,
                        is_mut: false,
                        unwrapped_info: p.x.unwrapped_info.clone(),
                    })
                } else {
                    p.clone()
                }
            })
            .collect::<Vec<_>>(),
    );

    if params_migrated.len() == 0 {
        return;
    }

    fx.params = new_params;

    let mut map: VisitorScopeMap = ScopeMap::new();
    let function = crate::ast_visitor::map_function_visitor_env(
        &f,
        &mut map,
        &mut (),
        &|_state, _map, expr| Ok(migrate_one_expr(expr, &params_migrated)),
        &|_state, _, stmt| Ok(vec![stmt.clone()]),
        &|_state, typ| Ok(typ.clone()),
        &|_state, _map, place| Ok(migrate_one_place(place, &params_migrated)),
    )
    .unwrap();

    *f = function;
}

fn migrate_one_expr(expr: &Expr, params_migrated: &HashSet<VarIdent>) -> Expr {
    match &expr.x {
        ExprX::VarAt(ident, VarAt::Pre) => {
            assert!(params_migrated.contains(ident));
            let mut_ref_typ = Arc::new(TypX::MutRef(expr.typ.clone()));
            let e = SpannedTyped::new(&expr.span, &mut_ref_typ, ExprX::Var(ident.clone()));
            SpannedTyped::new(&expr.span, &expr.typ, ExprX::Unary(UnaryOp::MutRefCurrent, e))
        }
        ExprX::Var(ident) if params_migrated.contains(ident) => {
            let mut_ref_typ = Arc::new(TypX::MutRef(expr.typ.clone()));
            let e = SpannedTyped::new(&expr.span, &mut_ref_typ, ExprX::Var(ident.clone()));
            let op = UnaryOp::MutRefFuture(MutRefFutureSourceName::MutRefFuture);
            SpannedTyped::new(&expr.span, &expr.typ, ExprX::Unary(op, e))
        }
        _ => expr.clone(),
    }
}

fn migrate_one_place(place: &Place, params_migrated: &HashSet<VarIdent>) -> Place {
    match &place.x {
        PlaceX::Local(ident) if params_migrated.contains(ident) => {
            let mut_ref_typ = Arc::new(TypX::MutRef(place.typ.clone()));
            let e = SpannedTyped::new(&place.span, &mut_ref_typ, ExprX::Var(ident.clone()));
            let op = UnaryOp::MutRefFuture(MutRefFutureSourceName::MutRefFuture);
            let e = SpannedTyped::new(&place.span, &place.typ, ExprX::Unary(op, e));
            SpannedTyped::new(&place.span, &place.typ, PlaceX::Temporary(e))
        }
        _ => place.clone(),
    }
}
