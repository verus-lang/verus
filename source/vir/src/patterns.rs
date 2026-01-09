use crate::ast::*;
use crate::ast_util::bool_typ;
use crate::ast_util::{conjoin, mk_eq, mk_ineq};
use crate::context::GlobalCtx;
use crate::def::Spanned;
use crate::messages::{Span, error};
use std::sync::Arc;

pub fn pattern_to_exprs(
    ctx: &GlobalCtx,
    place: &Place,
    pattern: &Pattern,
    has_guard: bool,
    decls: &mut Vec<Stmt>,
) -> Result<Expr, VirErr> {
    let mut pattern_bound_decls = vec![];
    let e = pattern_to_exprs_rec(ctx, pattern, place, &mut pattern_bound_decls, false)?;

    for pbd in pattern_bound_decls {
        if has_guard && pbd.mut_ref {
            return Err(error(
                &pattern.span,
                "Not yet supported: guard pattern when at least one bound var is mutably borrowed",
            ));
        }

        let ComputedPatternBinding { name, mut_ref, place } = pbd;

        let place = if mut_ref {
            PlaceX::temporary(SpannedTyped::new(
                &place.span,
                &Arc::new(TypX::MutRef(place.typ.clone())),
                ExprX::BorrowMut(place.clone()),
            ))
        } else {
            place
        };

        let pattern = PatternX::simple_var(name, &place.span, &place.typ);
        // Mode doesn't matter at this stage; arbitrarily set it to 'exec'
        let decl =
            StmtX::Decl { pattern, mode: Some(Mode::Exec), init: Some(place.clone()), els: None };
        decls.push(Spanned::new(place.span.clone(), decl));
    }

    Ok(e)
}

struct ComputedPatternBinding {
    name: VarIdent,
    mut_ref: bool,
    place: Place,
}

fn computed(binding: &PatternBinding, place: &Place) -> Result<ComputedPatternBinding, VirErr> {
    Ok(ComputedPatternBinding {
        name: binding.name.clone(),
        place: place.clone(),
        mut_ref: matches!(binding.by_ref, ByRef::MutRef),
    })
}

fn read_place(place: &Place) -> Expr {
    SpannedTyped::new(
        &place.span,
        &place.typ,
        ExprX::ReadPlace(
            place.clone(),
            UnfinalizedReadKind { preliminary_kind: ReadKind::ImmutBor, id: 0 },
        ),
    )
}

fn err_if_bad_binding(span: &Span, in_immut: bool, by_ref: ByRef) -> Result<(), VirErr> {
    // extra sanity check, should be caught by lifetime checking, though
    if in_immut && matches!(by_ref, ByRef::MutRef) {
        return Err(error(
            span,
            "cannot borrow this place as mutable, as it is behind a `&` reference",
        ));
    }
    Ok(())
}

fn pattern_to_exprs_rec(
    ctx: &GlobalCtx,
    pattern: &Pattern,
    place: &Place,
    bindings: &mut Vec<ComputedPatternBinding>,
    in_immut: bool,
) -> Result<Expr, VirErr> {
    let t_bool = Arc::new(TypX::Bool);
    match &pattern.x {
        PatternX::Wildcard(_) => {
            Ok(SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Var(binding) => {
            err_if_bad_binding(&pattern.span, in_immut, binding.by_ref)?;
            bindings.push(computed(binding, place)?);
            Ok(SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Binding { binding, sub_pat } => {
            err_if_bad_binding(&pattern.span, in_immut, binding.by_ref)?;
            let pattern_test = pattern_to_exprs_rec(ctx, sub_pat, place, bindings, in_immut)?;
            // This binding needs to go last in case we have something like this:
            //   `ref mut x @ Some(y)`
            // (which is ok if the y is bound via copy)
            // In this case we need to read `y` before taking the mut ref
            bindings.push(computed(binding, place)?);
            Ok(pattern_test)
        }
        PatternX::Constructor(dt, variant, patterns) => {
            let expr = read_place(&place);
            let is_variant_opr =
                UnaryOpr::IsVariant { datatype: dt.clone(), variant: variant.clone() };
            let test_variant = SpannedTyped::new(
                &pattern.span,
                &bool_typ(),
                ExprX::UnaryOpr(is_variant_opr, expr.clone()),
            );

            let mut test = test_variant;

            for binder in patterns.iter() {
                let field_opr = FieldOpr {
                    datatype: dt.clone(),
                    variant: variant.clone(),
                    field: binder.name.clone(),
                    get_variant: false,
                    check: VariantCheck::None,
                };
                let field_typ = &binder.a.typ;
                let field_place = SpannedTyped::new(
                    &binder.a.span,
                    field_typ,
                    PlaceX::Field(field_opr, place.clone()),
                );
                let pattern_test =
                    pattern_to_exprs_rec(ctx, &binder.a, &field_place, bindings, in_immut)?;
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }

            Ok(test)
        }
        PatternX::Or(_pat1, _pat2) => {
            /*
            let mut decls1 = vec![];
            let mut decls2 = vec![];

            let pat1_matches = pattern_to_exprs_rec(ctx, expr, pat1, &mut decls1)?;
            let pat2_matches = pattern_to_exprs_rec(ctx, expr, pat2, &mut decls2)?;

            let matches = disjoin(&pattern.span, &vec![pat1_matches.clone(), pat2_matches]);

            assert!(decls1.len() == decls2.len());
            for d1 in decls1 {
                let d2 = decls2
                    .iter()
                    .find(|d| d.name == d1.name)
                    .expect("both sides of 'or' pattern should bind the same variables");
                assert!(d1.mutable == d2.mutable);
                let combined_decl = PatternBoundDecl {
                    name: d1.name,
                    mutable: d1.mutable,
                    expr: if_then_else(&pattern.span, &pat1_matches, &d1.expr, &d2.expr),
                };
                decls.push(combined_decl);
            }

            Ok(matches)
            */
            todo!(); // TODO(new_mut_ref)
        }
        PatternX::Expr(e) => {
            let expr = read_place(&place);
            Ok(mk_eq(&pattern.span, &expr, e))
        }
        PatternX::Range(lower, upper) => {
            let expr = read_place(&place);
            let mut v = vec![];
            if let Some(lower) = lower {
                v.push(mk_ineq(&pattern.span, lower, &expr, InequalityOp::Le));
            }
            if let Some((upper, upper_ineq)) = upper {
                v.push(mk_ineq(&pattern.span, &expr, upper, *upper_ineq));
            }
            Ok(conjoin(&pattern.span, &v))
        }
        PatternX::ImmutRef(sub_pat) => pattern_to_exprs_rec(ctx, sub_pat, place, bindings, true),
        PatternX::MutRef(sub_pat) => {
            let deref_place =
                SpannedTyped::new(&sub_pat.span, &sub_pat.typ, PlaceX::DerefMut(place.clone()));
            pattern_to_exprs_rec(ctx, sub_pat, &deref_place, bindings, in_immut)
        }
    }
}

pub(crate) fn pattern_find_mut_binding(pattern: &Pattern) -> Option<Span> {
    match &pattern.x {
        PatternX::Wildcard(_) => None,
        PatternX::Var(binding) => {
            if matches!(binding.by_ref, ByRef::MutRef) {
                Some(pattern.span.clone())
            } else {
                None
            }
        }
        PatternX::Binding { binding, sub_pat } => {
            if matches!(binding.by_ref, ByRef::MutRef) {
                Some(pattern.span.clone())
            } else {
                pattern_find_mut_binding(sub_pat)
            }
        }
        PatternX::Constructor(_path, _variant, patterns) => {
            for binder in patterns.iter() {
                match pattern_find_mut_binding(&binder.a) {
                    s @ Some(_) => {
                        return s;
                    }
                    None => {}
                }
            }
            None
        }
        PatternX::Or(pat1, pat2) => {
            match pattern_find_mut_binding(pat1) {
                s @ Some(_) => {
                    return s;
                }
                None => {}
            }
            pattern_find_mut_binding(pat2)
        }
        PatternX::Expr(_e) => None,
        PatternX::Range(_lower, _upper) => None,
        PatternX::ImmutRef(p) | PatternX::MutRef(p) => pattern_find_mut_binding(p),
    }
}

pub(crate) fn pattern_has_mut(pattern: &Pattern) -> bool {
    pattern_find_mut_binding(pattern).is_some()
}

pub(crate) fn pattern_has_or(pattern: &Pattern) -> bool {
    match &pattern.x {
        PatternX::Wildcard(_) => false,
        PatternX::Var(_binding) => false,
        PatternX::Binding { binding: _, sub_pat } => pattern_has_or(sub_pat),
        PatternX::Constructor(_path, _variant, patterns) => {
            for binder in patterns.iter() {
                if pattern_has_or(&binder.a) {
                    return true;
                }
            }
            false
        }
        PatternX::Or(_pat1, _pat2) => true,
        PatternX::Expr(_e) => false,
        PatternX::Range(_lower, _upper) => false,
        PatternX::ImmutRef(p) | PatternX::MutRef(p) => pattern_has_or(p),
    }
}
