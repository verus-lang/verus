use crate::ast::{Expr, ExprX, SpannedTyped, Typ, TypX, UnaryOp};
use crate::messages::Span;
use crate::sst::{Exp, ExpX, UniqueIdent};
use std::sync::Arc;

pub(crate) fn make_none_expr(span: &Span, typ: &Typ) -> Expr {
    let option_path = crate::def::option_type_path();
    let option_typx =
        TypX::Datatype(option_path.clone(), Arc::new(vec![typ.clone()]), Arc::new(vec![]));
    let exprx =
        ExprX::Ctor(option_path.clone(), Arc::new("None".to_string()), Arc::new(vec![]), None);
    SpannedTyped::new(span, &Arc::new(option_typx), exprx)
}

pub(crate) fn make_option_exp(opt: Option<Exp>, span: &Span, typ: &Typ) -> Exp {
    let option_path = crate::def::option_type_path();
    let option_typx =
        TypX::Datatype(option_path.clone(), Arc::new(vec![typ.clone()]), Arc::new(vec![]));
    let expx = match opt {
        None => ExpX::Ctor(option_path.clone(), Arc::new("None".to_string()), Arc::new(vec![])),
        Some(exp) => {
            let field_id = crate::def::positional_field_ident(0);
            let field = air::ast_util::ident_binder(&field_id, &exp);
            let fields = Arc::new(vec![field]);
            ExpX::Ctor(option_path.clone(), Arc::new("Some".to_string()), fields)
        }
    };
    SpannedTyped::new(span, &Arc::new(option_typx), expx)
}

// InferSpecForLoopIter produces None if any variables in the express are modified in the loop
fn vars_unmodified(modified_vars: &Arc<Vec<UniqueIdent>>, exp: &Exp) -> bool {
    let mut map = air::scope_map::ScopeMap::new();
    let r = crate::sst_visitor::exp_visitor_check(exp, &mut map, &mut |e: &Exp, _| match &e.x {
        ExpX::Var(x) => {
            if modified_vars.contains(x) {
                Err(())
            } else {
                Ok(())
            }
        }
        _ => Ok(()),
    });
    match r {
        Ok(()) => true,
        Err(()) => false,
    }
}

pub(crate) fn finalize_inv(modified_vars: &Arc<Vec<UniqueIdent>>, exp: &Exp) -> Exp {
    crate::sst_visitor::map_exp_visitor(exp, &mut |e: &Exp| {
        match &e.x {
            ExpX::Unary(UnaryOp::InferSpecForLoopIter, e_infer) => {
                if vars_unmodified(modified_vars, e_infer) {
                    // promote to Some(e)
                    make_option_exp(Some(e_infer.clone()), &e.span, &e.typ)
                } else {
                    // otherwise, leave as-is to be removed by sst_to_air
                    e.clone()
                }
            }
            _ => e.clone(),
        }
    })
}
