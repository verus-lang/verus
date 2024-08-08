use crate::ast::{
    CallTarget, Datatype, Expr, ExprX, FieldOpr, Fun, Function, FunctionX, Path, SpannedTyped,
    Stmt, StmtX, Typ, TypX, UnaryOp, UnaryOpr, VirErr,
};
use crate::ast_util::undecorate_typ;
use crate::def::Spanned;
use crate::messages::{error, internal_error};
use crate::modes::TypeInvInfo;
use std::collections::HashMap;
use std::sync::Arc;

// We need to do the following, for any datatype that has a user-defined type invariant:
//
//  1. For any (non-spec) Ctor, add an assert that the type inv holds.
//
//  2. For any field update, add an assert that the type inv holds.
//     Make sure to handle all the nested fields.
//
//  3. For any other Loc node we error.
//     Right now these can only appear in a &mut argument to a call.
//
// NOTE: we may need to revisit after more general &mut support lands.

pub fn annotate_user_defined_invariants(
    functionx: &mut FunctionX,
    info: &TypeInvInfo,
    functions: &HashMap<Fun, Function>,
    datatypes: &HashMap<Path, Datatype>,
) -> Result<(), VirErr> {
    let module = functionx.owning_module.as_ref().unwrap();
    functionx.body = Some(crate::ast_visitor::map_expr_visitor(
        functionx.body.as_ref().unwrap(),
        &|expr: &Expr| {
            match &expr.x {
                ExprX::Ctor(..) => {
                    if info.ctor_needs_check[&expr.span.id]
                        && typ_has_user_defined_type_invariant(datatypes, &expr.typ)
                    {
                        let fun =
                            typ_get_user_defined_type_invariant(datatypes, &expr.typ).unwrap();
                        let function = functions.get(&fun).unwrap();
                        Ok(assert_and_return(&expr, function, module)?)
                    } else {
                        Ok(expr.clone())
                    }
                }
                ExprX::Assign { lhs, .. } => {
                    let mut new_asserts = asserts_for_lhs(info, functions, datatypes, module, lhs)?;
                    if new_asserts.len() > 0 {
                        new_asserts
                            .insert(0, Spanned::new(expr.span.clone(), StmtX::Expr(expr.clone())));
                        // typ should be unit
                        let block = SpannedTyped::new(
                            &expr.span,
                            &expr.typ,
                            ExprX::Block(Arc::new(new_asserts), None),
                        );
                        Ok(block)
                    } else {
                        Ok(expr.clone())
                    }
                }
                ExprX::Call(CallTarget::Fun(_, fun, _, _, _), args) => {
                    let function = &functions.get(fun).unwrap();
                    for (arg, param) in args.iter().zip(function.x.params.iter()) {
                        if param.x.is_mut {
                            error_if_mut_ref_modifies_field_affecting_type_inv(datatypes, arg)?;
                        }
                    }
                    Ok(expr.clone())
                }
                _ => Ok(expr.clone()),
            }
        },
    )?);
    Ok(())
}

fn assert_and_return(e: &Expr, function: &Function, module: &Path) -> Result<Expr, VirErr> {
    if !crate::ast_util::is_visible_to(&function.x.visibility, module) {
        return Err(error(
            &e.span,
            "type invariant function is not visible to this program point, which requires us to prove the invariant is preserved",
        ).secondary_span(&function.span));
    }
    Ok(SpannedTyped::new(
        &e.span,
        &e.typ,
        ExprX::AssertAssumeUserDefinedTypeInvariant {
            is_assume: false,
            expr: e.clone(),
            fun: function.x.name.clone(),
        },
    ))
}

fn mk_assert_stmt(e: &Expr, function: &Function, module: &Path) -> Result<Stmt, VirErr> {
    Ok(Spanned::new(e.span.clone(), StmtX::Expr(assert_and_return(e, function, module)?)))
}

fn typ_get_user_defined_type_invariant(
    datatypes: &HashMap<Path, Datatype>,
    typ: &Typ,
) -> Option<Fun> {
    match &*undecorate_typ(typ) {
        TypX::Datatype(path, ..) => {
            match &datatypes.get(path).unwrap().x.user_defined_invariant_fn {
                Some(fun) => Some(fun.clone()),
                None => None,
            }
        }
        _ => {
            dbg!(typ);
            panic!("typ_user_defined_type_invariant: expected datatype");
        }
    }
}

fn typ_has_user_defined_type_invariant(datatypes: &HashMap<Path, Datatype>, typ: &Typ) -> bool {
    typ_get_user_defined_type_invariant(datatypes, typ).is_some()
}

pub fn error_if_mut_ref_modifies_field_affecting_type_inv(
    datatypes: &HashMap<Path, Datatype>,
    lhs: &Expr,
) -> Result<(), VirErr> {
    crate::ast_visitor::expr_visitor_check(lhs, &mut |_scope_map, expr| {
        match &expr.x {
            ExprX::UnaryOpr(UnaryOpr::Field(FieldOpr { .. }), inner) => {
                if typ_has_user_defined_type_invariant(datatypes, &inner.typ) {
                    return Err(error(
                        &expr.span,
                        "currently unsupported: taking a &mut ref to a field from a datatype with a type invariant",
                    ));
                }
            }
            _ => {}
        }
        Ok(())
    })
}

/// Emits the necessary proof obligations for user-defined type invariants
/// after an assignment like `x.a.b.c = e;`
/// In such a case, proof obligations may be necessary for `x.a.b`, `x.a`, and `x`.
pub fn asserts_for_lhs(
    info: &TypeInvInfo,
    functions: &HashMap<Fun, Function>,
    datatypes: &HashMap<Path, Datatype>,
    module: &Path,
    lhs: &Expr,
) -> Result<Vec<Stmt>, VirErr> {
    let mut cur = lhs;
    let mut stmts: Vec<Stmt> = vec![];
    loop {
        match &cur.x {
            ExprX::UnaryOpr(UnaryOpr::Field(FieldOpr { .. }), inner) => {
                if info.field_loc_needs_check[&cur.span.id] {
                    if let Some(fun) = typ_get_user_defined_type_invariant(datatypes, &inner.typ) {
                        let expr = loc_to_normal_expr(inner);
                        let function = functions.get(&fun).unwrap();
                        stmts.push(mk_assert_stmt(&expr, function, module)?);
                    }
                }
                cur = inner;
            }
            ExprX::UnaryOpr(UnaryOpr::Unbox(_), inner) => {
                cur = inner;
            }
            ExprX::UnaryOpr(UnaryOpr::Box(_), inner) => {
                cur = inner;
            }
            ExprX::Unary(UnaryOp::CoerceMode { .. }, inner) => {
                cur = inner;
            }
            ExprX::VarLoc(_) => {
                break;
            }
            _ => {
                dbg!(&cur.x);
                return Err(internal_error(
                    &cur.span,
                    "assert_user_defined_type_invariants_for_assign missing case",
                ));
            }
        }
    }
    Ok(stmts)
}

pub fn loc_to_normal_expr(e: &Expr) -> Expr {
    crate::ast_visitor::map_expr_visitor(e, &mut |expr| match &expr.x {
        ExprX::VarLoc(ident) => {
            Ok(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(ident.clone())))
        }
        _ => Ok(expr.clone()),
    })
    .unwrap()
}
