use crate::ast::*;
use crate::context::GlobalCtx;
use crate::messages::{Span, error};
use std::sync::Arc;
use crate::def::Spanned;
use crate::sst_util::subst_typ_for_datatype;
use crate::ast_util::{mk_eq, mk_ineq, conjoin};
use crate::ast_util::bool_typ;
use crate::resolution_inference::ProjectionTyped;

pub fn pattern_to_exprs(
    ctx: &GlobalCtx,
    place: &Place,
    pattern: &Pattern,
    has_guard: bool,
    decls: &mut Vec<Stmt>,
) -> Result<Expr, VirErr> {
    let mut pattern_bound_decls = vec![];
    let e = pattern_to_exprs_rec(ctx, pattern, place, ByRef::No, &mut pattern_bound_decls)?;

    for pbd in pattern_bound_decls {
        if has_guard && pbd.mut_ref {
            return Err(error(
                &pattern.span,
                "Not yet supported: guard pattern when at least one bound var is mutably borrowed",
            ));
        }

        let ComputedPatternBinding { name, mutable, mut_ref, place } = pbd;

        let place = if mut_ref {
            PlaceX::temporary(SpannedTyped::new(
                &place.span,
                &Arc::new(TypX::MutRef(place.typ.clone())),
                ExprX::BorrowMut(place.clone())
            ))
        } else {
            place
        };

        let pattern = PatternX::simple_var(name, mutable, &place.span, &place.typ);
        // Mode doesn't matter at this stage; arbitrarily set it to 'exec'
        let decl = StmtX::Decl {
            pattern,
            mode: Some(Mode::Exec),
            init: Some(place.clone()),
            els: None,
        };
        decls.push(Spanned::new(place.span.clone(), decl));
    }

    Ok(e)
}

struct ComputedPatternBinding {
    name: VarIdent,
    mutable: bool,
    mut_ref: bool,
    place: Place,
}

fn computed(span: &Span, binding: &PatternBinding, place: &Place, ergo: ByRef) -> Result<ComputedPatternBinding, VirErr> {
    Ok(ComputedPatternBinding {
        name: binding.name.clone(),
        mutable: binding.mutable,
        place: place.clone(),
        mut_ref: match ergo {
            ByRef::No => {
                matches!(binding.by_ref, ByRef::MutRef)
            }
            ByRef::ImmutRef => {
                if matches!(binding.by_ref, ByRef::MutRef) {
                    // e.g. if you try to match `&Option<u64>` against `Some(ref mut x)`
                    // this ought to be caught by lifetime checking
                    return Err(error(
                        span,
                        "cannot borrow this as mutable, as it is behind a `&` reference",
                    ));
                }
                false
            }
            ByRef::MutRef => true,
        }
    })
}

// TODO(new_mut_ref): need to make sure there aren't any issues with the decorations being wrong
fn handle_ergo(place: &Place, ergo: ByRef) -> (Place, ByRef) {
    let mut place = place.clone();
    let mut ergo = ergo.clone();
    loop {
        match &*place.typ {
            TypX::Decorate(TypDecoration::Ref, None, t) => {
                place = SpannedTyped::new(&place.span, t, place.x.clone());
                ergo = ByRef::ImmutRef;
            }
            TypX::Decorate(TypDecoration::Box, None, t) => {
                place = SpannedTyped::new(&place.span, t, place.x.clone());
            }
            TypX::MutRef(t) => {
                place = SpannedTyped::new(&place.span, t, PlaceX::DerefMut(place.clone()));
                ergo = match ergo {
                    ByRef::No | ByRef::MutRef => ByRef::MutRef,
                    ByRef::ImmutRef => ByRef::ImmutRef,
                };
            }
            _ => {
                return (place, ergo);
            }
        }
    }
}

/// Similar to above, but operates on the slightly different types used by resolution_inference
pub(crate) fn handle_ergo_res_inf(projs: &Vec<ProjectionTyped>, typ: &Typ, ergo: ByRef) -> (Vec<ProjectionTyped>, Typ, ByRef) {
    assert!(ergo != ByRef::ImmutRef);
    let mut projs = projs.clone();
    let mut typ = typ.clone();
    let mut ergo = ergo;
    loop {
        match &*typ {
            TypX::Decorate(TypDecoration::Ref, None, _t) => {
                ergo = ByRef::ImmutRef;
                // this is enough, we stop at the first ImmutRef
                return (projs, typ, ergo);
            }
            TypX::Decorate(TypDecoration::Box, None, t) => {
                typ = t.clone();
            }
            TypX::MutRef(t) => {
                projs.push(ProjectionTyped::DerefMut(t.clone()));
                typ = t.clone();
                ergo = ByRef::MutRef;
            }
            _ => {
                return (projs, typ, ergo);
            }
        }
    }
}

fn read_place(place: &Place) -> Expr {
    SpannedTyped::new(&place.span, &place.typ, ExprX::ReadPlace(place.clone(),
                UnfinalizedReadKind { preliminary_kind: ReadKind::ImmutBor, id: 0 }))
}

fn pattern_to_exprs_rec(
    ctx: &GlobalCtx,
    pattern: &Pattern,
    place: &Place,
    ergo: ByRef,
    bindings: &mut Vec<ComputedPatternBinding>,
) -> Result<Expr, VirErr> {
    let t_bool = Arc::new(TypX::Bool);
    match &pattern.x {
        PatternX::Wildcard(_) => {
            Ok(SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Var(binding) => {
            bindings.push(computed(&pattern.span, binding, place, ergo)?);
            Ok(SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Binding { binding, sub_pat } => {
            let pattern_test = pattern_to_exprs_rec(ctx, sub_pat, place, ergo, bindings)?;
            // This binding needs to go last in case we have something like this:
            //   `ref mut x @ Some(y)`
            // (which is ok if the y is bound via copy)
            // In this case we need to read `y` before taking the mut ref
            bindings.push(computed(&pattern.span, binding, place, ergo)?);
            Ok(pattern_test)
        }
        PatternX::Constructor(dt, variant, patterns) => {
            let (place, ergo) = handle_ergo(place, ergo);

            let expr = read_place(&place);
            let is_variant_opr =
                UnaryOpr::IsVariant { datatype: dt.clone(), variant: variant.clone() };
            let test_variant = SpannedTyped::new(&pattern.span, &bool_typ(), ExprX::UnaryOpr(is_variant_opr, expr.clone()));

            let mut test = test_variant;

            let (dt, typ_args) = match &*place.typ {
                TypX::Datatype(dt, typ_args, _) => (dt, typ_args),
                _ => {
                    return Err(error(
                        &pattern.span,
                        "Verus internal error: pattern_to_exprs_rec failed to get Datatype type",
                    ));
                }
            };
            let datatype = match dt {
                Dt::Path(p) => Some(&ctx.datatypes[p]),
                Dt::Tuple(_) => None,
            };

            for binder in patterns.iter() {
                let field_opr = FieldOpr {
                    datatype: dt.clone(),
                    variant: variant.clone(),
                    field: binder.name.clone(),
                    get_variant: false,
                    check: VariantCheck::None,
                };
                let field_typ = match datatype {
                    Some((typ_positives, _variants)) => {
                        subst_typ_for_datatype(&typ_positives, typ_args, &place.typ)
                    }
                    None => {
                        let idx = binder.name.parse::<usize>().unwrap();
                        typ_args[idx].clone()
                    }
                };
                let field_place = SpannedTyped::new(&binder.a.span, &field_typ, PlaceX::Field(field_opr, place.clone()));
                let pattern_test = pattern_to_exprs_rec(ctx, &binder.a, &field_place, ergo, bindings)?;
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }

            Ok(test)
        }
        PatternX::Or(_pat1, _pat2) => {
            todo!(); // TODO(new_mut_ref)
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
        }
        PatternX::Expr(e) => {
            // TODO(new_mut_ref) do we need to handle_ergo here?
            let expr = read_place(&place);
            Ok(mk_eq(&pattern.span, &expr, e))
        }
        PatternX::Range(lower, upper) => {
            // TODO(new_mut_ref) do we need to handle_ergo here?
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
    }
}
