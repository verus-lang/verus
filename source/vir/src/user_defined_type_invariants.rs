use crate::ast::{
    CallTarget, Datatype, Expr, ExprX, FieldOpr, Fun, Function, FunctionKind, FunctionX, Path,
    PatternX, SpannedTyped, Stmt, StmtX, Typ, TypX, UnaryOp, UnaryOpr, UnwindSpec, VarIdent,
    VarIdentDisambiguate, VirErr,
};
use crate::ast_util::undecorate_typ;
use crate::def::Spanned;
use crate::messages::Span;
use crate::messages::{error, internal_error};
use crate::modes::TypeInvInfo;
use std::cell::Cell;
use std::collections::HashMap;
use std::sync::Arc;

// We need to do the following, for any datatype that has a user-defined type invariant:
//
//  1. For any (non-spec) Ctor, add an assert that the type inv holds.
//
//  2. For any field update, add an assert that the type inv holds.
//     Make sure to handle all the nested fields.
//
//  3. For any call that takes &mut args to fields, add an assertion that
//     after the call the struct meets the type invariant again.
//
// NOTE: we may need to revisit after more general &mut support lands.

pub(crate) fn annotate_user_defined_invariants(
    functionx: &mut FunctionX,
    info: &TypeInvInfo,
    functions: &HashMap<Fun, Function>,
    datatypes: &HashMap<Path, Datatype>,
) -> Result<(), VirErr> {
    let module = functionx.owning_module.as_ref().unwrap();
    let id_cell = Cell::<u64>::new(0);
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
                    let new_asserts = asserts_for_lhs(info, functions, datatypes, module, lhs)?;
                    if new_asserts.len() > 0 {
                        Ok(expr_followed_by_stmts(expr, new_asserts, &id_cell))
                    } else {
                        Ok(expr.clone())
                    }
                }
                ExprX::Call(CallTarget::Fun(_, fun, _, _, _), args) => {
                    let function = &functions.get(fun).unwrap();
                    let mut all_asserts = vec![];
                    for (arg, param) in args.iter().zip(function.x.params.iter()) {
                        if param.x.is_mut {
                            let mut new_asserts =
                                asserts_for_lhs(info, functions, datatypes, module, arg)?;
                            all_asserts.append(&mut new_asserts);
                        }
                    }
                    if all_asserts.len() > 0 {
                        // TODO: this should go the solver
                        check_func_is_no_unwind(&expr.span, functions, function)?;

                        let stmts = all_asserts; //dedupe_asserts(all_asserts);
                        Ok(expr_followed_by_stmts(expr, stmts, &id_cell))
                    } else {
                        Ok(expr.clone())
                    }
                }
                ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: true, expr, fun: _ } => {
                    // Check that this is fine, and fill in the correct 'fun'

                    let typ = undecorate_typ(&expr.typ);
                    if !matches!(&*typ, TypX::Datatype(..)) {
                        return Err(error(&expr.span, "this type is not a datatype"));
                    }
                    if let Some(fun) = typ_get_user_defined_type_invariant(datatypes, &typ) {
                        let function = functions.get(&fun).unwrap();
                        if !crate::ast_util::is_visible_to(&function.x.visibility, module) {
                            return Err(error(
                                &expr.span,
                                "type invariant function is not visible to this program point",
                            )
                            .secondary_span(&function.span));
                        }
                        Ok(SpannedTyped::new(
                            &expr.span,
                            &expr.typ,
                            ExprX::AssertAssumeUserDefinedTypeInvariant {
                                is_assume: true,
                                expr: expr.clone(),
                                fun,
                            },
                        ))
                    } else {
                        return Err(error(
                            &expr.span,
                            "this type does not have any type invariant",
                        ));
                    }
                }
                _ => Ok(expr.clone()),
            }
        },
    )?);
    Ok(())
}

fn is_unit(t: &Typ) -> bool {
    if let TypX::Tuple(t) = &**t { t.len() == 0 } else { false }
}

fn check_func_is_no_unwind(
    span: &Span,
    functions: &HashMap<Fun, Function>,
    function: &Function,
) -> Result<(), VirErr> {
    let function = match &function.x.kind {
        FunctionKind::TraitMethodImpl { method, .. } => functions.get(method).unwrap(),
        _ => function,
    };
    let unwind_spec = function.x.unwind_spec_or_default();
    if !matches!(unwind_spec, UnwindSpec::NoUnwind) {
        return Err(error(
            span,
            "this function call takes a &mut ref of a field of a datatype with a user-defined type invariant; thus, this function should be marked no_unwind (note: this check is currently implemented overly-conservatively and requires the function to be marked no_unwind in its signature)"
        ).secondary_span(&function.span));
    }
    Ok(())
}

fn expr_followed_by_stmts(expr: &Expr, stmts: Vec<Stmt>, id_cell: &Cell<u64>) -> Expr {
    let mut stmts = stmts;

    if is_unit(&expr.typ) {
        stmts.insert(0, Spanned::new(expr.span.clone(), StmtX::Expr(expr.clone())));
        SpannedTyped::new(&expr.span, &expr.typ, ExprX::Block(Arc::new(stmts), None))
    } else {
        let id = id_cell.get();
        id_cell.set(id + 1);
        let ident = VarIdent(
            Arc::new("tmp".to_string()),
            VarIdentDisambiguate::UserDefinedTypeInvariantPass(id),
        );

        let decl = StmtX::Decl {
            pattern: SpannedTyped::new(
                &expr.span,
                &expr.typ,
                PatternX::Var { name: ident.clone(), mutable: false },
            ),
            mode: None,
            init: Some(expr.clone()),
        };
        stmts.insert(0, Spanned::new(expr.span.clone(), decl));
        SpannedTyped::new(
            &expr.span,
            &expr.typ,
            ExprX::Block(
                Arc::new(stmts),
                Some(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(ident))),
            ),
        )
    }
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

/// Emits the necessary proof obligations for user-defined type invariants
/// after an assignment like `x.a.b.c = e;`
/// In such a case, proof obligations may be necessary for `x.a.b`, `x.a`, and `x`.
fn asserts_for_lhs(
    info: &TypeInvInfo,
    functions: &HashMap<Fun, Function>,
    datatypes: &HashMap<Path, Datatype>,
    module: &Path,
    lhs: &Expr,
) -> Result<Vec<Stmt>, VirErr> {
    let mut cur = lhs;
    let mut stmts: Vec<Stmt> = vec![];
    // TODO: tuple fields
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
            ExprX::Ghost { alloc_wrapper: _, tracked: _, expr } => {
                cur = expr;
            }
            ExprX::VarLoc(_) => {
                break;
            }
            ExprX::Loc(expr) => {
                cur = expr;
            }
            _ => {
                dbg!(&cur.x);
                return Err(internal_error(
                    &cur.span,
                    "user_defined_type_invariants::asserts_for_lhs missing case",
                ));
            }
        }
    }
    Ok(stmts)
}

fn loc_to_normal_expr(e: &Expr) -> Expr {
    crate::ast_visitor::map_expr_visitor(e, &mut |expr| match &expr.x {
        ExprX::VarLoc(ident) => {
            Ok(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(ident.clone())))
        }
        ExprX::Loc(e) => Ok(e.clone()),
        _ => Ok(expr.clone()),
    })
    .unwrap()
}

/// The given type MUST have unmodified type decorations.
/// (We need to check for the absence of the Ghost type.)
pub fn check_typ_ok_for_use_typ_invariant(span: &Span, t: &Typ) -> Result<(), VirErr> {
    match &**t {
        TypX::Decorate(dec, _, t) => {
            use crate::ast::TypDecoration::*;
            match dec {
                Ref | Box | Rc | Arc | Tracked => check_typ_ok_for_use_typ_invariant(span, t),
                MutRef | Never | ConstPtr => Err(error(span, "this type is not a datatype")),
                Ghost => Err(error(span, "cannot apply use_type_invariant for Ghost<_>")),
            }
        }
        TypX::Datatype(..) => Ok(()),
        _ => Err(error(span, "this type is not a datatype")),
    }
}
