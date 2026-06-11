use crate::ast::{Datatype, Dt, Expr, ExprX, Fun, Function, Path, SpannedTyped, Typ, TypX, VirErr};
use crate::ast_util::undecorate_typ;
use crate::messages::Span;
use crate::messages::{error, internal_error};
use crate::modes::TypeInvInfo;
use std::collections::HashMap;

/// Called by resolution_inference
pub(crate) fn annotate_one(
    expr: &Expr,
    info: &TypeInvInfo,
    functions: &HashMap<Fun, Function>,
    datatypes: &HashMap<Path, Datatype>,
    module: &Path,
) -> Result<Expr, VirErr> {
    match &expr.x {
        ExprX::Ctor(Dt::Path(_), ..) => {
            if info.ctor_needs_check[&expr.span.id]
                && typ_has_user_defined_type_invariant(datatypes, &expr.typ)
            {
                let fun = typ_get_user_defined_type_invariant(datatypes, &expr.typ).unwrap();
                let Some(function) = functions.get(&fun) else {
                    return Err(internal_error(&expr.span, "missing type invariant function"));
                };
                Ok(assert_and_return(&expr, function, module)?)
            } else {
                Ok(expr.clone())
            }
        }
        ExprX::ShrRefStructWrap(..) => {
            if typ_has_user_defined_type_invariant(datatypes, &expr.typ) {
                let fun = typ_get_user_defined_type_invariant(datatypes, &expr.typ).unwrap();
                let Some(function) = functions.get(&fun) else {
                    return Err(internal_error(&expr.span, "missing type invariant function"));
                };
                Ok(assert_and_return(&expr, function, module)?)
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
                let Some(function) = functions.get(&fun) else {
                    return Err(internal_error(&expr.span, "missing type invariant function"));
                };
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
                return Err(error(&expr.span, "this type does not have any type invariant"));
            }
        }
        _ => Ok(expr.clone()),
    }
}

pub(crate) fn check_vis(span: &Span, function: &Function, module: &Path) -> Result<(), VirErr> {
    if !crate::ast_util::is_visible_to(&function.x.visibility, module) {
        return Err(error(
            span,
            "type invariant function is not visible to this program point, which requires us to prove the invariant is preserved",
        ).secondary_span(&function.span));
    }
    Ok(())
}

fn assert_and_return(e: &Expr, function: &Function, module: &Path) -> Result<Expr, VirErr> {
    check_vis(&e.span, function, module)?;
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

fn typ_get_user_defined_type_invariant(
    datatypes: &HashMap<Path, Datatype>,
    typ: &Typ,
) -> Option<Fun> {
    match &*undecorate_typ(typ) {
        TypX::Datatype(dt, ..) => match dt {
            Dt::Path(path) => match &datatypes.get(path).unwrap().x.user_defined_invariant_fn {
                Some(fun) => Some(fun.clone()),
                None => None,
            },
            Dt::Tuple(_) => None,
        },
        _ => {
            dbg!(typ);
            panic!("typ_user_defined_type_invariant: expected datatype");
        }
    }
}

fn typ_has_user_defined_type_invariant(datatypes: &HashMap<Path, Datatype>, typ: &Typ) -> bool {
    typ_get_user_defined_type_invariant(datatypes, typ).is_some()
}

/// The given type MUST have unmodified type decorations.
/// (We need to check for the absence of the Ghost type.)
pub fn check_typ_ok_for_use_typ_invariant(span: &Span, t: &Typ) -> Result<(), VirErr> {
    match &**t {
        TypX::Decorate(dec, _, t) => {
            use crate::ast::TypDecoration::*;
            match dec {
                Ref | Box | Rc | Arc | Tracked => check_typ_ok_for_use_typ_invariant(span, t),
                Never | ConstPtr => Err(error(span, "this type is not a datatype")),
                Ghost => Err(error(span, "cannot apply use_type_invariant for Ghost<_>")),
            }
        }
        TypX::Datatype(..) => Ok(()),
        _ => Err(error(span, "this type is not a datatype")),
    }
}
