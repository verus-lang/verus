//! VIR-AST -> VIR-AST transformation to simplify away some complicated features

use crate::ast::Quant;
use crate::ast::Typs;
use crate::ast::VarBinder;
use crate::ast::VarBinderX;
use crate::ast::VarBinders;
use crate::ast::VarIdent;
use crate::ast::{
    AssocTypeImpl, AutospecUsage, BinaryOp, Binder, BoundsCheck, BuiltinSpecFun, ByRef, CallTarget,
    ChainedOp, Constant, CtorPrintStyle, CtorUpdateTail, Datatype, DatatypeTransparency, DatatypeX,
    Dt, Expr, ExprX, Exprs, Field, FieldOpr, Fun, Function, FunctionKind, Ident, InequalityOp,
    IntRange, ItemKind, Krate, KrateX, Mode, MultiOp, Path, Pattern, PatternBinding, PatternX,
    Place, PlaceX, SpannedTyped, Stmt, StmtX, TraitImpl, Typ, TypX, UnaryOp, UnaryOpr, Variant,
    VariantCheck, VirErr, Visibility,
};
use crate::ast_util::{
    conjoin, disjoin, if_then_else, mk_eq, mk_ineq, place_to_expr, typ_args_for_datatype_typ,
    wrap_in_trigger,
};
use crate::ast_visitor::VisitorScopeMap;
use crate::context::GlobalCtx;
use crate::def::dummy_param_name;
use crate::def::is_dummy_param_name;
use crate::def::{
    Spanned, positional_field_ident, prefix_tuple_param, prefix_tuple_variant, user_local_name,
};
use crate::messages::Span;
use crate::messages::{error, internal_error};
use crate::sst_util::subst_typ_for_datatype;
use crate::util::vec_map_result;
use air::ast_util::ident_binder;
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

struct State {
    // Counter to generate temporary variables
    next_var: u64,
    // Rename parameters to simplify their names
    rename_vars: HashMap<VarIdent, VarIdent>,
    // Name of a datatype to represent each tuple arity
    tuple_typs: HashSet<usize>,
    // Name of a datatype to represent each tuple arity
    closure_typs: HashMap<usize, Path>,
    // Functions for which the corresponding FnDef type is used
    fndef_typs: HashSet<Fun>,
}

impl State {
    fn new() -> Self {
        State {
            next_var: 0,
            rename_vars: HashMap::new(),
            tuple_typs: HashSet::new(),
            closure_typs: HashMap::new(),
            fndef_typs: HashSet::new(),
        }
    }

    fn reset_for_function(&mut self) {
        self.next_var = 0;
        self.rename_vars = HashMap::new();
    }

    fn next_temp(&mut self) -> VarIdent {
        self.next_var += 1;
        crate::def::simplify_temp_var(self.next_var)
    }

    fn tuple_type_name(&mut self, arity: usize) -> Dt {
        self.tuple_typs.insert(arity);
        Dt::Tuple(arity)
    }

    fn closure_type_name(&mut self, id: usize) -> Path {
        self.closure_typs.entry(id).or_insert(crate::def::prefix_closure_type(id)).clone()
    }
}

struct LocalCtxt {
    span: Span,
    typ_params: Vec<Ident>,
}

/// Should only return true if this expression is guaranteed constant
/// (i.e., does not depend on evaluation order, i.e., does not depend on any mutable variable)
fn is_small_expr(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Const(_) => true,
        ExprX::Unary(UnaryOp::Not | UnaryOp::Clip { .. }, e) => is_small_expr(e),
        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), _) => panic!("unexpected box"),
        ExprX::Loc(_) => panic!("expr is a location"),
        _ => false,
    }
}

/// Create a temporary and return:
///  - A Stmt that assigns the given `expr` to the temporary
///  - The name of the temporary
fn temp_var(state: &mut State, expr: &Expr) -> (Stmt, VarIdent) {
    let temp = state.next_temp();
    let name = temp.clone();
    let pattern = PatternX::simple_var(name, &expr.span, &expr.typ);
    let decl = StmtX::Decl {
        pattern,
        mode: Some(Mode::Exec),
        init: Some(PlaceX::temporary(expr.clone())),
        els: None,
    };
    let temp_decl = Spanned::new(expr.span.clone(), decl);
    (temp_decl, temp)
}

fn temp_expr(state: &mut State, expr: &Expr) -> (Stmt, Expr) {
    let (temp_decl, var_ident) = temp_var(state, expr);
    (temp_decl, SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(var_ident)))
}

fn small_or_temp(state: &mut State, expr: &Expr) -> (Vec<Stmt>, Expr) {
    if is_small_expr(&expr) {
        (vec![], expr.clone())
    } else {
        let (ts, te) = temp_expr(state, expr);
        (vec![ts], te)
    }
}

fn pattern_field_expr(span: &Span, expr: &Expr, pat_typ: &Typ, field_op: UnaryOpr) -> Expr {
    let field = ExprX::UnaryOpr(field_op, expr.clone());
    SpannedTyped::new(span, pat_typ, field)
}

// Compute:
// - expression that tests whether exp matches pattern
// - bindings of pattern variables to fields of exp
fn pattern_to_exprs(
    ctx: &GlobalCtx,
    state: &mut State,
    expr: &Expr,
    pattern: &Pattern,
    decls: &mut Vec<Stmt>,
) -> Result<Expr, VirErr> {
    let mut pattern_bound_decls = vec![];
    let e = pattern_to_exprs_rec(ctx, state, expr, pattern, &mut pattern_bound_decls)?;

    for pbd in pattern_bound_decls {
        let PatternBoundDecl { name, expr } = pbd;
        let pattern = PatternX::simple_var(name, &expr.span, &expr.typ);
        // Mode doesn't matter at this stage; arbitrarily set it to 'exec'
        let decl = StmtX::Decl {
            pattern,
            mode: Some(Mode::Exec),
            init: Some(PlaceX::temporary(expr.clone())),
            els: None,
        };
        decls.push(Spanned::new(expr.span.clone(), decl));
    }

    Ok(e)
}

struct PatternBoundDecl {
    name: VarIdent,
    expr: Expr,
}

fn pattern_to_exprs_rec(
    ctx: &GlobalCtx,
    state: &mut State,
    expr: &Expr,
    pattern: &Pattern,
    decls: &mut Vec<PatternBoundDecl>,
) -> Result<Expr, VirErr> {
    let t_bool = Arc::new(TypX::Bool);
    match &pattern.x {
        PatternX::Wildcard(_) => {
            Ok(SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Var(binding) => {
            decls.push(PatternBoundDecl { name: binding.name.clone(), expr: expr.clone() });
            Ok(SpannedTyped::new(&expr.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Binding { binding, sub_pat } => {
            let pattern_test = pattern_to_exprs_rec(ctx, state, expr, sub_pat, decls)?;
            decls.push(PatternBoundDecl { name: binding.name.clone(), expr: expr.clone() });
            Ok(pattern_test)
        }
        PatternX::Constructor(path, variant, patterns) => {
            let is_variant_opr =
                UnaryOpr::IsVariant { datatype: path.clone(), variant: variant.clone() };
            let test_variant = ExprX::UnaryOpr(is_variant_opr, expr.clone());
            let mut test = SpannedTyped::new(&pattern.span, &t_bool, test_variant);
            for binder in patterns.iter() {
                let field_op = UnaryOpr::Field(FieldOpr {
                    datatype: path.clone(),
                    variant: variant.clone(),
                    field: binder.name.clone(),
                    get_variant: false,
                    check: VariantCheck::None,
                });
                let field_exp = pattern_field_expr(&pattern.span, expr, &binder.a.typ, field_op);
                let pattern_test = pattern_to_exprs_rec(ctx, state, &field_exp, &binder.a, decls)?;
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }
            Ok(test)
        }
        PatternX::Or(pat1, pat2) => {
            let mut decls1 = vec![];
            let mut decls2 = vec![];

            let pat1_matches = pattern_to_exprs_rec(ctx, state, expr, pat1, &mut decls1)?;
            let pat2_matches = pattern_to_exprs_rec(ctx, state, expr, pat2, &mut decls2)?;

            let matches = disjoin(&pattern.span, &vec![pat1_matches.clone(), pat2_matches]);

            assert!(decls1.len() == decls2.len());
            for d1 in decls1 {
                let d2 = decls2
                    .iter()
                    .find(|d| d.name == d1.name)
                    .expect("both sides of 'or' pattern should bind the same variables");
                let combined_decl = PatternBoundDecl {
                    name: d1.name,
                    expr: if_then_else(&pattern.span, &pat1_matches, &d1.expr, &d2.expr),
                };
                decls.push(combined_decl);
            }

            Ok(matches)
        }
        PatternX::Expr(e) => Ok(mk_eq(&pattern.span, expr, e)),
        PatternX::Range(lower, upper) => {
            let mut v = vec![];
            if let Some(lower) = lower {
                v.push(mk_ineq(&pattern.span, lower, expr, InequalityOp::Le));
            }
            if let Some((upper, upper_ineq)) = upper {
                v.push(mk_ineq(&pattern.span, expr, upper, *upper_ineq));
            }
            Ok(conjoin(&pattern.span, &v))
        }
        PatternX::ImmutRef(p) => pattern_to_exprs_rec(ctx, state, expr, p, decls),
        PatternX::MutRef(_p) => {
            panic!("PatternX::MutRef not expected without `-V new-mut-ref`");
        }
    }
}

fn pattern_to_decls_with_no_initializer(pattern: &Pattern, stmts: &mut Vec<Stmt>) {
    match &pattern.x {
        PatternX::Wildcard(_) => {}
        PatternX::Var(binding) | PatternX::Binding { binding, sub_pat: _ } => {
            let v_patternx = PatternX::Var(PatternBinding {
                name: binding.name.clone(),
                user_mut: None,
                by_ref: ByRef::No,
                typ: binding.typ.clone(),
                copy: false,
            });
            let v_pattern = SpannedTyped::new(&pattern.span, &binding.typ, v_patternx);
            stmts.push(Spanned::new(
                pattern.span.clone(),
                StmtX::Decl {
                    pattern: v_pattern,
                    mode: Some(Mode::Exec), // mode doesn't matter anymore
                    init: None,
                    els: None,
                },
            ));

            match &pattern.x {
                PatternX::Binding { sub_pat, .. } => {
                    pattern_to_decls_with_no_initializer(sub_pat, stmts);
                }
                _ => {}
            }
        }
        PatternX::Constructor(_path, _variant, patterns) => {
            for binder in patterns.iter() {
                pattern_to_decls_with_no_initializer(&binder.a, stmts);
            }
        }
        PatternX::Or(pat1, _pat2) => {
            pattern_to_decls_with_no_initializer(&pat1, stmts);
        }
        PatternX::Expr(_) => {}
        PatternX::Range(_, _) => {}
        PatternX::ImmutRef(p) | PatternX::MutRef(p) => {
            pattern_to_decls_with_no_initializer(p, stmts);
        }
    }
}

fn rename_var(state: &State, scope_map: &VisitorScopeMap, x: &VarIdent) -> VarIdent {
    if let Some(rename) = state.rename_vars.get(x) {
        if scope_map[x].is_outer_param_or_ret {
            return rename.clone();
        }
    }
    x.clone()
}

fn simplify_one_place(
    _ctx: &GlobalCtx,
    state: &mut State,
    scope_map: &VisitorScopeMap,
    place: &Place,
) -> Result<Place, VirErr> {
    match &place.x {
        PlaceX::Local(x) => Ok(place.new_x(PlaceX::Local(rename_var(state, scope_map, x)))),
        _ => Ok(place.clone()),
    }
}

/// Returns a "pure place", i.e., a Place with no-side effects, and which is rooted
/// at a Local (rather than a Temporary).
fn place_to_pure_place(state: &mut State, place: &Place) -> (Vec<Stmt>, Place) {
    match &place.x {
        PlaceX::Field(field_opr, p) => {
            let (mut stmts, p1) = place_to_pure_place(state, p);
            match field_opr.check {
                VariantCheck::None => {}
                VariantCheck::Union => {
                    let p1_expr = place_to_expr(&p1);
                    let assert_stmt =
                        crate::place_preconditions::field_check(&place.span, &p1_expr, field_opr);
                    stmts.push(assert_stmt);
                }
            }
            let field_opr = FieldOpr { check: VariantCheck::None, ..field_opr.clone() };
            let p2 =
                SpannedTyped::new(&place.span, &place.typ, PlaceX::Field(field_opr.clone(), p1));
            (stmts, p2)
        }
        PlaceX::DerefMut(p) => {
            let (stmts, p1) = place_to_pure_place(state, p);
            let p2 = SpannedTyped::new(&place.span, &place.typ, PlaceX::DerefMut(p1));
            (stmts, p2)
        }
        PlaceX::ModeUnwrap(p, mwm) => {
            let (stmts, p1) = place_to_pure_place(state, p);
            let p2 = SpannedTyped::new(&place.span, &place.typ, PlaceX::ModeUnwrap(p1, *mwm));
            (stmts, p2)
        }
        PlaceX::Local(_l) => (vec![], place.clone()),
        PlaceX::Temporary(expr) => {
            let (ts, var_ident) = temp_var(state, expr);
            let p = SpannedTyped::new(&place.span, &place.typ, PlaceX::Local(var_ident));
            (vec![ts], p)
        }
        PlaceX::WithExpr(expr, p) => {
            let (mut stmts, p1) = place_to_pure_place(state, p);
            stmts.insert(0, Spanned::new(place.span.clone(), StmtX::Expr(expr.clone())));
            (stmts, p1)
        }
        PlaceX::Index(p, idx, kind, bounds_check) => {
            let (mut stmts, p1) = place_to_pure_place(state, p);
            let (idx_decl, idx_expr) = temp_expr(state, idx);
            stmts.push(idx_decl);

            match bounds_check {
                BoundsCheck::Allow => {}
                BoundsCheck::Error => {
                    let p1_expr = place_to_expr(&p1);
                    let assert_stmt = crate::place_preconditions::index_bound(
                        &place.span,
                        &p1_expr,
                        &idx_expr,
                        *kind,
                    );
                    stmts.push(assert_stmt);
                }
            }

            let p = SpannedTyped::new(
                &place.span,
                &place.typ,
                PlaceX::Index(p1, idx_expr, *kind, BoundsCheck::Allow),
            );

            (stmts, p)
        }
    }
}

// note that this gets called *bottom up*
// that is, if node A is the parent of children B and C,
// then simplify_one_expr is called first on B and C, and then on A

fn simplify_one_expr(
    ctx: &GlobalCtx,
    state: &mut State,
    scope_map: &VisitorScopeMap,
    expr: &Expr,
) -> Result<Expr, VirErr> {
    use crate::ast::CallTargetKind;
    match &expr.x {
        ExprX::Var(x) => Ok(expr.new_x(ExprX::Var(rename_var(state, scope_map, x)))),
        ExprX::VarAt(x, at) => Ok(expr.new_x(ExprX::VarAt(rename_var(state, scope_map, x), *at))),
        ExprX::VarLoc(x) => {
            // Note: the below reasoning is why I originally added this check, but the reasoning
            // doesn't entirely apply anymore since now ast_to_sst infers mutability rather
            // than relying on user checks. I'm leaving this for now (since the check can't hurt)
            // but this case is obselete by new-mut-ref anyway.
            //
            // ========
            //
            // If we try to mutate `x`, check that `x` is actually marked mut.
            // This is *usually* caught by rustc for us, during our lifetime checking phase.
            // However, there are a few cases to watch out for:
            //
            //  1. The user provides --no-lifetime. (We still need need to do the check
            //     because the AIR encoding later on will rely on mutability-ness being
            //     well-formed. This isn't *really* necessary, since --no-lifetime is
            //     unsound anyway and doesn't really have any guarantees - but doing
            //     this check is nicer than an AIR type error down the line.)
            //
            //  2. If the user does as @-assignment, `x@ = ...` where `t: Ghost<T>`.
            //     This is a special Verus thing so we have to do the check ourselves.
            //     (issue #424)
            //
            // It would usually make more sense to have this in well_formed.rs, but
            // in the majority of cases, it's nicer to have rustc catch the error
            // for its better diagnostics. So the check is here in ast_simplify,
            // which comes after our lifetime checking pass.
            match scope_map.get(x) {
                None => Err(error(&expr.span, "Verus Internal Error: cannot find this variable")),
                Some(entry) if entry.user_mut == Some(false) && entry.init => {
                    let name = user_local_name(x);
                    Err(error(&expr.span, format!("variable `{name:}` is not marked mutable")))
                }
                _ => Ok(expr.new_x(ExprX::VarLoc(rename_var(state, scope_map, x)))),
            }
        }
        ExprX::ConstVar(x, autospec) => {
            let call = ExprX::Call(
                CallTarget::Fun(
                    CallTargetKind::Static,
                    x.clone(),
                    Arc::new(vec![]),
                    Arc::new(vec![]),
                    *autospec,
                ),
                Arc::new(vec![]),
                None,
            );
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        ExprX::Call(
            CallTarget::Fun(kind, tgt, typs, impl_paths, autospec_usage),
            args,
            post_args,
        ) => {
            assert!(*autospec_usage == AutospecUsage::Final);

            let is_trait_impl = match kind {
                CallTargetKind::Static => false,
                CallTargetKind::ProofFn(..) => false,
                CallTargetKind::Dynamic => true,
                CallTargetKind::DynamicResolved { .. } => true,
                CallTargetKind::ExternalTraitDefault => true,
            };
            let args = if typs.len() == 0 && args.len() == 0 && !is_trait_impl {
                // To simplify the AIR/SMT encoding, add a dummy argument to any function with 0 arguments
                let typ = Arc::new(TypX::Int(IntRange::Int));
                use num_traits::Zero;
                let argx = ExprX::Const(Constant::Int(num_bigint::BigInt::zero()));
                let arg = SpannedTyped::new(&expr.span, &typ, argx);
                Arc::new(vec![arg])
            } else {
                args.clone()
            };

            let call = ExprX::Call(
                CallTarget::Fun(
                    kind.clone(),
                    tgt.clone(),
                    typs.clone(),
                    impl_paths.clone(),
                    *autospec_usage,
                ),
                args,
                post_args.clone(),
            );
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        ExprX::Ctor(name, variant, partial_binders, Some(update)) => {
            let CtorUpdateTail { place, taken_fields: _ } = update;
            let (temp_decl, update) = small_or_temp(state, &place_to_expr(place));
            let mut decls: Vec<Stmt> = Vec::new();
            let mut binders: Vec<Binder<Expr>> = Vec::new();
            if temp_decl.len() == 0 {
                for binder in partial_binders.iter() {
                    binders.push(binder.clone());
                }
            } else {
                // Because of Rust's order of evaluation here,
                // we have to put binders in temp vars, too.
                for binder in partial_binders.iter() {
                    let (temp_decl_inner, e) = small_or_temp(state, &binder.a);
                    decls.extend(temp_decl_inner.into_iter());
                    binders.push(binder.map_a(|_| e));
                }
                decls.extend(temp_decl.into_iter());
            }

            let path = match name {
                Dt::Path(p) => p,
                Dt::Tuple(_) => {
                    return Err(internal_error(
                        &expr.span,
                        "ExprX::Ctor with update and tuple type",
                    ));
                }
            };

            let (typ_positives, variants) = &ctx.datatypes[path];
            assert_eq!(variants.len(), 1);
            let fields = &variants[0].fields;
            let typ_args = typ_args_for_datatype_typ(&expr.typ);
            // replace ..update
            // with f1: update.f1, f2: update.f2, ...
            for field in fields.iter() {
                if binders.iter().find(|b| b.name == field.name).is_none() {
                    let op = UnaryOpr::Field(FieldOpr {
                        datatype: name.clone(),
                        variant: variant.clone(),
                        field: field.name.clone(),
                        get_variant: false,
                        check: VariantCheck::None,
                    });
                    let exprx = ExprX::UnaryOpr(op, update.clone());
                    let ty = subst_typ_for_datatype(&typ_positives, typ_args, &field.a.0);
                    let field_exp = SpannedTyped::new(&expr.span, &ty, exprx);
                    binders.push(ident_binder(&field.name, &field_exp));
                }
            }
            let ctorx = ExprX::Ctor(name.clone(), variant.clone(), Arc::new(binders), None);
            let ctor = SpannedTyped::new(&expr.span, &expr.typ, ctorx);
            if decls.len() == 0 {
                Ok(ctor)
            } else {
                let block = ExprX::Block(Arc::new(decls), Some(ctor));
                Ok(SpannedTyped::new(&expr.span, &expr.typ, block))
            }
        }
        ExprX::Unary(UnaryOp::CoerceMode { .. }, expr0) => Ok(expr0.clone()),
        ExprX::Multi(MultiOp::Chained(ops), args) => {
            assert!(args.len() == ops.len() + 1);
            let mut stmts: Vec<Stmt> = Vec::new();
            let mut es: Vec<Expr> = Vec::new();
            // Execute each argument in order; no short-circuiting
            for i in 0..args.len() {
                let (decl, e) = temp_expr(state, &args[i]);
                stmts.push(decl);
                es.push(e);
            }
            let mut conjunction: Expr = es[0].clone();
            for i in 0..ops.len() {
                let op = match ops[i] {
                    ChainedOp::Inequality(a) => BinaryOp::Inequality(a),
                    ChainedOp::MultiEq => BinaryOp::Eq(Mode::Spec),
                };
                let left = es[i].clone();
                let right = es[i + 1].clone();
                let span = left.span.clone();
                let binary = SpannedTyped::new(&span, &expr.typ, ExprX::Binary(op, left, right));
                if i == 0 {
                    conjunction = binary;
                } else {
                    let exprx = ExprX::Binary(BinaryOp::And, conjunction, binary);
                    conjunction = SpannedTyped::new(&span, &expr.typ, exprx);
                }
            }
            if stmts.len() == 0 {
                Ok(conjunction)
            } else {
                let block = ExprX::Block(Arc::new(stmts), Some(conjunction));
                Ok(SpannedTyped::new(&expr.span, &expr.typ, block))
            }
        }
        ExprX::Match(place, arms1) => {
            let mut place = place.clone();

            let (temp_decl, expr0) = if ctx.new_mut_ref {
                let (stmts, p) = place_to_pure_place(state, &place);
                place = p;
                let unused = crate::ast_util::mk_bool(&expr.span, false);
                (stmts, unused)
            } else {
                let expr0 = place_to_expr(&place);
                small_or_temp(state, &expr0)
            };

            // Translate into If expression
            let t_bool = Arc::new(TypX::Bool);
            let mut if_expr: Option<Expr> = None;
            for arm in arms1.iter().rev() {
                let mut decls: Vec<Stmt> = Vec::new();
                let has_guard = arm.x.has_guard();

                let test_pattern = if ctx.new_mut_ref {
                    crate::patterns::pattern_to_exprs(
                        ctx,
                        &place,
                        &arm.x.pattern,
                        has_guard,
                        &mut decls,
                    )?
                } else {
                    pattern_to_exprs(ctx, state, &expr0, &arm.x.pattern, &mut decls)?
                };

                let test = if !has_guard {
                    test_pattern
                } else {
                    assert!(!crate::patterns::pattern_has_or(&arm.x.pattern));

                    let guard = arm.x.guard.clone();
                    let test_exp = ExprX::Binary(BinaryOp::And, test_pattern, guard);
                    let test = SpannedTyped::new(&arm.x.pattern.span, &t_bool, test_exp);
                    let block = ExprX::Block(Arc::new(decls.clone()), Some(test));
                    SpannedTyped::new(&arm.x.pattern.span, &t_bool, block)
                };

                let block = ExprX::Block(Arc::new(decls), Some(arm.x.body.clone()));
                let body = SpannedTyped::new(&arm.x.pattern.span, &expr.typ, block);
                if let Some(prev) = if_expr {
                    // if pattern && guard then body else prev
                    let ifx = ExprX::If(test.clone(), body, Some(prev));
                    if_expr = Some(SpannedTyped::new(&test.span, &expr.typ.clone(), ifx));
                } else {
                    // last arm is unconditional
                    if_expr = Some(body);
                }
            }
            if let Some(if_expr) = if_expr {
                let if_expr = if temp_decl.len() != 0 {
                    let block = ExprX::Block(Arc::new(temp_decl), Some(if_expr));
                    SpannedTyped::new(&expr.span, &expr.typ, block)
                } else {
                    if_expr
                };
                Ok(if_expr)
            } else {
                Err(error(&expr.span, "not yet implemented: zero-arm match expressions"))
            }
        }
        ExprX::Ghost { alloc_wrapper: _, tracked: _, expr: expr1 } => Ok(expr1.clone()),
        ExprX::NonSpecClosure {
            params,
            proof_fn_modes,
            body,
            requires,
            ensures,
            ret,
            external_spec,
        } => {
            assert!(external_spec.is_none());

            let closure_var_ident = state.next_temp();
            let closure_var = SpannedTyped::new(
                &expr.span,
                &expr.typ.clone(),
                ExprX::Var(closure_var_ident.clone()),
            );

            let external_spec_expr =
                exec_closure_spec(state, &expr.span, &closure_var, params, ret, requires, ensures)?;
            let external_spec = Some((closure_var_ident, external_spec_expr));

            Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::NonSpecClosure {
                    params: params.clone(),
                    proof_fn_modes: proof_fn_modes.clone(),
                    body: body.clone(),
                    requires: requires.clone(),
                    ensures: ensures.clone(),
                    ret: ret.clone(),
                    external_spec,
                },
            ))
        }
        ExprX::Assign { lhs, rhs, op: Some(op) } => {
            match &lhs.x {
                ExprX::VarLoc(id) => {
                    // convert VarLoc to Var to be used on the RHS
                    let var = SpannedTyped::new(&lhs.span, &lhs.typ, ExprX::Var(id.clone()));
                    let new_rhs = SpannedTyped::new(
                        &expr.span,
                        &lhs.typ,
                        ExprX::Binary(op.clone(), var, rhs.clone()),
                    );
                    Ok(SpannedTyped::new(
                        &expr.span,
                        &expr.typ,
                        ExprX::Assign { lhs: lhs.clone(), rhs: new_rhs, op: None },
                    ))
                }
                _ => Err(error(&lhs.span, "not yet implemented: lhs of compound assignment")),
            }
        }
        _ => Ok(expr.clone()),
    }
}

fn tuple_get_field_expr(
    state: &mut State,
    span: &Span,
    typ: &Typ,
    tuple_expr: &Expr,
    tuple_arity: usize,
    field: usize,
) -> Expr {
    let datatype = state.tuple_type_name(tuple_arity);

    let variant = prefix_tuple_variant(tuple_arity);
    let field = positional_field_ident(field);
    let op = UnaryOpr::Field(FieldOpr {
        datatype,
        variant,
        field,
        get_variant: false,
        check: VariantCheck::None,
    });
    let field_expr = SpannedTyped::new(span, typ, ExprX::UnaryOpr(op, tuple_expr.clone()));
    field_expr
}

fn simplify_one_stmt(ctx: &GlobalCtx, state: &mut State, stmt: &Stmt) -> Result<Vec<Stmt>, VirErr> {
    match &stmt.x {
        StmtX::Decl { pattern, mode: _, init: None, els: None } => match &pattern.x {
            PatternX::Var(PatternBinding {
                by_ref: ByRef::No,
                name: _,
                user_mut: _,
                typ: _,
                copy: _,
            }) => Ok(vec![stmt.clone()]),
            _ => {
                let mut stmts: Vec<Stmt> = Vec::new();
                pattern_to_decls_with_no_initializer(pattern, &mut stmts);
                Ok(stmts)
            }
        },
        StmtX::Decl { pattern, mode: _, init: None, els: Some(_) } => Err(error(
            &pattern.span,
            "Verus Internal Error: Decl with else-block but no initializer",
        )),
        StmtX::Decl { pattern, mode: _, init: Some(_init), els: None }
            if matches!(
                pattern.x,
                PatternX::Var(PatternBinding {
                    by_ref: ByRef::No,
                    name: _,
                    user_mut: _,
                    typ: _,
                    copy: _
                })
            ) =>
        {
            Ok(vec![stmt.clone()])
        }
        StmtX::Decl { pattern, mode: _, init: Some(init), els } => {
            if ctx.new_mut_ref {
                let (mut stmts, place) = place_to_pure_place(state, init);
                let _pattern_check =
                    crate::patterns::pattern_to_exprs(ctx, &place, pattern, false, &mut stmts)?;
                if let Some(_els) = &els {
                    todo!(); // TODO(new_mut_ref)
                }
                Ok(stmts)
            } else {
                let mut decls: Vec<Stmt> = Vec::new();
                let (temp_decl, init) = small_or_temp(state, &place_to_expr(init));
                decls.extend(temp_decl.into_iter());
                let mut decls2: Vec<Stmt> = Vec::new();
                let pattern_check = pattern_to_exprs(ctx, state, &init, &pattern, &mut decls2)?;
                if let Some(els) = &els {
                    let e = ExprX::Unary(UnaryOp::Not, pattern_check.clone());
                    let check = SpannedTyped::new(&pattern_check.span, &pattern_check.typ, e);
                    let ifx = ExprX::If(check.clone(), els.clone(), Some(init.clone()));
                    let init = SpannedTyped::new(&els.span, &init.typ, ifx);
                    let (temp_decl, _) = temp_expr(state, &init);
                    decls.push(temp_decl);
                }
                decls.extend(decls2);
                Ok(decls)
            }
        }
        StmtX::Expr(_) => Ok(vec![stmt.clone()]),
    }
}

fn simplify_one_typ(local: &LocalCtxt, state: &mut State, typ: &Typ) -> Result<Typ, VirErr> {
    match &**typ {
        TypX::Datatype(Dt::Tuple(i), ..) => {
            state.tuple_type_name(*i);
            Ok(typ.clone())
        }
        TypX::AnonymousClosure(_typs, _typ, id) => {
            let path = Dt::Path(state.closure_type_name(*id));
            Ok(Arc::new(TypX::Datatype(path, Arc::new(vec![]), Arc::new(vec![]))))
        }
        TypX::FnDef(fun, _typs, resolved) => {
            state.fndef_typs.insert(fun.clone());
            if let Some(resolved_fun) = resolved {
                state.fndef_typs.insert(resolved_fun.clone());
            }
            Ok(typ.clone())
        }
        TypX::TypParam(x) => {
            if !local.typ_params.contains(&x) {
                return Err(error(
                    &local.span,
                    format!("type parameter {} used before being declared", x),
                ));
            }
            Ok(typ.clone())
        }
        _ => Ok(typ.clone()),
    }
}

// TODO: a lot of this closure stuff could get its own file
// rename to apply to all fn types, not just closure types

fn closure_trait_call_typ_args(state: &mut State, fn_val: &Expr, params: &VarBinders<Typ>) -> Typs {
    let path = state.tuple_type_name(params.len());

    let param_typs: Vec<Typ> = params.iter().map(|p| p.a.clone()).collect();
    let tup_typ = Arc::new(TypX::Datatype(path, Arc::new(param_typs), Arc::new(vec![])));

    Arc::new(vec![fn_val.typ.clone(), tup_typ])
}

fn mk_closure_req_call(
    state: &mut State,
    span: &Span,
    params: &VarBinders<Typ>,
    fn_val: &Expr,
    arg_tuple: &Expr,
) -> Expr {
    let bool_typ = Arc::new(TypX::Bool);
    SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Call(
            CallTarget::BuiltinSpecFun(
                BuiltinSpecFun::ClosureReq,
                closure_trait_call_typ_args(state, fn_val, params),
                Arc::new(vec![]),
            ),
            Arc::new(vec![fn_val.clone(), arg_tuple.clone()]),
            None,
        ),
    )
}

fn mk_closure_ens_call(
    state: &mut State,
    span: &Span,
    params: &VarBinders<Typ>,
    fn_val: &Expr,
    arg_tuple: &Expr,
    ret_arg: &Expr,
    builtin_spec_fun: BuiltinSpecFun,
) -> Expr {
    let bool_typ = Arc::new(TypX::Bool);
    SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Call(
            CallTarget::BuiltinSpecFun(
                builtin_spec_fun,
                closure_trait_call_typ_args(state, fn_val, params),
                Arc::new(vec![]),
            ),
            Arc::new(vec![fn_val.clone(), arg_tuple.clone(), ret_arg.clone()]),
            None,
        ),
    )
}

fn exec_closure_spec_param(
    state: &mut State,
    span: &Span,
    params: &VarBinders<Typ>,
) -> (VarIdent, Expr) {
    let param_typs: Vec<Typ> = params.iter().map(|p| p.a.clone()).collect();
    let tuple_path = state.tuple_type_name(params.len());
    let tuple_typ = Arc::new(TypX::Datatype(tuple_path, Arc::new(param_typs), Arc::new(vec![])));
    let tuple_ident = crate::def::closure_param_var();
    let tuple_var = SpannedTyped::new(span, &tuple_typ, ExprX::Var(tuple_ident.clone()));
    (tuple_ident, tuple_var)
}

fn exec_closure_spec_requires(
    state: &mut State,
    span: &Span,
    closure_var: &Expr,
    params: &VarBinders<Typ>,
    requires: &Exprs,
) -> Result<Expr, VirErr> {
    // For requires:

    // If the closure has `|a0, a1, a2| requires f(a0, a1, a2)`
    // then we emit a spec of the form
    //
    //      forall x :: f(x.0, x.1, x.2) ==> closure.requires(x)
    //
    // with `closure.requires(x)` as the trigger

    // (Since the user doesn't have the option to specify a trigger here,
    // we need to use the most general one, and that means we need to
    // quantify over a tuple.)

    let (tuple_ident, tuple_var) = exec_closure_spec_param(state, span, params);
    let tuple_typ = tuple_var.typ.clone();

    let reqs = conjoin(span, requires);

    // Supply 'let' statements of the form 'let a0 = x.0; let a1 = x.1; ...' etc.

    let mut decls: Vec<Stmt> = Vec::new();
    for (i, p) in params.iter().enumerate() {
        let typ = &p.a;
        let pattern = PatternX::simple_var(p.name.clone(), span, typ);
        let tuple_field = tuple_get_field_expr(state, span, typ, &tuple_var, params.len(), i);
        let decl = StmtX::Decl {
            pattern,
            mode: Some(Mode::Spec),
            init: Some(PlaceX::temporary(tuple_field)),
            els: None,
        };
        decls.push(Spanned::new(span.clone(), decl));
    }

    let reqs_body =
        SpannedTyped::new(&reqs.span, &reqs.typ, ExprX::Block(Arc::new(decls), Some(reqs.clone())));

    let closure_req_call =
        wrap_in_trigger(&mk_closure_req_call(state, span, params, closure_var, &tuple_var));

    let bool_typ = Arc::new(TypX::Bool);
    let req_quant_body = SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Binary(BinaryOp::Implies, reqs_body, closure_req_call.clone()),
    );

    let forall = Quant { quant: air::ast::Quant::Forall };
    let binders = Arc::new(vec![Arc::new(VarBinderX { name: tuple_ident, a: tuple_typ })]);
    let req_forall =
        SpannedTyped::new(span, &bool_typ, ExprX::Quant(forall, binders, req_quant_body));

    Ok(req_forall)
}

fn exec_closure_spec_ensures(
    state: &mut State,
    span: &Span,
    closure_var: &Expr,
    params: &VarBinders<Typ>,
    ret: &VarBinder<Typ>,
    ensures: &Vec<Expr>,
    default_ens: bool,
) -> Result<Expr, VirErr> {
    // For ensures:

    // If the closure has `|a0, a1, a2| ensures |b| f(a0, a1, a2, b)`
    // then we emit a spec of the form
    //
    //      forall x, y :: closure.ensures(x, y) ==> f(x.0, x.1, x.2, y)
    //
    // with `closure.ensures(x)` as the trigger

    let (tuple_ident, tuple_var) = exec_closure_spec_param(state, span, params);
    let tuple_typ = tuple_var.typ.clone();

    let ret_ident = ret.clone();
    let ret_var = SpannedTyped::new(span, &ret.a, ExprX::Var(ret_ident.name.clone()));

    let enss = conjoin(span, ensures);

    // Supply 'let' statements of the form 'let a0 = x.0; let a1 = x.1; ...' etc.

    let mut decls: Vec<Stmt> = Vec::new();
    for (i, p) in params.iter().enumerate() {
        let typ = &p.a;
        let pattern = PatternX::simple_var(p.name.clone(), span, typ);
        let tuple_field = tuple_get_field_expr(state, span, typ, &tuple_var, params.len(), i);
        let decl = StmtX::Decl {
            pattern,
            mode: Some(Mode::Spec),
            init: Some(PlaceX::temporary(tuple_field)),
            els: None,
        };
        decls.push(Spanned::new(span.clone(), decl));
    }

    let enss_body =
        SpannedTyped::new(&enss.span, &enss.typ, ExprX::Block(Arc::new(decls), Some(enss.clone())));

    let closure_ens_call = wrap_in_trigger(&mk_closure_ens_call(
        state,
        span,
        params,
        closure_var,
        &tuple_var,
        &ret_var,
        if default_ens { BuiltinSpecFun::DefaultEns } else { BuiltinSpecFun::ClosureEns },
    ));

    let bool_typ = Arc::new(TypX::Bool);
    let ens_quant_body = SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Binary(BinaryOp::Implies, closure_ens_call.clone(), enss_body),
    );

    let forall = Quant { quant: air::ast::Quant::Forall };
    let binders =
        Arc::new(vec![Arc::new(VarBinderX { name: tuple_ident, a: tuple_typ }), ret.clone()]);
    let ens_forall =
        SpannedTyped::new(span, &bool_typ, ExprX::Quant(forall, binders, ens_quant_body));

    Ok(ens_forall)
}

fn exec_closure_spec(
    state: &mut State,
    span: &Span,
    closure_var: &Expr,
    params: &VarBinders<Typ>,
    ret: &VarBinder<Typ>,
    requires: &Exprs,
    ensures: &Exprs,
) -> Result<Expr, VirErr> {
    let req_forall = exec_closure_spec_requires(state, span, closure_var, params, requires)?;

    if ensures.len() > 0 {
        let ens_forall =
            exec_closure_spec_ensures(state, span, closure_var, params, ret, ensures, false)?;
        Ok(conjoin(span, &vec![req_forall, ens_forall]))
    } else {
        Ok(req_forall)
    }
}

pub(crate) fn need_fndef_axiom(fndef_typs: &HashSet<Fun>, f: &Function) -> bool {
    if fndef_typs.contains(&f.x.name) {
        return true;
    }
    match &f.x.kind {
        FunctionKind::TraitMethodImpl { method, .. } => fndef_typs.contains(method),
        _ => false,
    }
}

fn add_fndef_axioms_to_function(
    _ctx: &GlobalCtx,
    state: &mut State,
    function: &Function,
) -> Result<Function, VirErr> {
    state.reset_for_function();

    let params: Vec<_> = function
        .x
        .params
        .iter()
        .filter(|p| !is_dummy_param_name(&p.x.name))
        .map(|p| Arc::new(VarBinderX { name: p.x.name.clone(), a: p.x.typ.clone() }))
        .collect();
    let params = Arc::new(params);

    let (fun, typ_args, is_trait_method_impl, inherit) = match &function.x.kind {
        FunctionKind::TraitMethodImpl { method, trait_typ_args, inherit_body_from, .. } => {
            (method, trait_typ_args.clone(), true, inherit_body_from.is_some())
        }
        _ => {
            let typ_args: Vec<_> = function
                .x
                .typ_params
                .iter()
                .map(|tp| Arc::new(TypX::TypParam(tp.clone())))
                .collect();
            let typ_args = Arc::new(typ_args);
            (&function.x.name, typ_args, false, false)
        }
    };

    let fndef_singleton = SpannedTyped::new(
        &function.span,
        &Arc::new(TypX::FnDef(fun.clone(), typ_args, None)),
        ExprX::ExecFnByName(fun.clone()),
    );

    let mut fndef_axioms = vec![];

    // Don't need to repeat the 'requires' for a trait impl fn because requires can't change
    if !is_trait_method_impl {
        let req_forall = exec_closure_spec_requires(
            state,
            &function.span,
            &fndef_singleton,
            &params,
            &function.x.require,
        )?;
        fndef_axioms.push(req_forall);
    }

    let ret = Arc::new(VarBinderX {
        name: function.x.ret.x.name.clone(),
        a: function.x.ret.x.typ.clone(),
    });
    let (mut closure_enss, default_enss) = function.x.ensure.clone();
    if inherit {
        assert!(closure_enss.len() + default_enss.len() == 0);
        let (_, tuple_var) = exec_closure_spec_param(state, &function.span, &params);
        let ret_var = SpannedTyped::new(&function.span, &ret.a, ExprX::Var(ret.name.clone()));
        let default_expr = mk_closure_ens_call(
            state,
            &function.span,
            &params,
            &fndef_singleton,
            &tuple_var,
            &ret_var,
            BuiltinSpecFun::DefaultEns,
        );
        closure_enss = Arc::new(vec![default_expr]);
    }
    for (default_ens, enss) in [(false, closure_enss), (true, default_enss)] {
        if enss.len() > 0 {
            let ens_forall = exec_closure_spec_ensures(
                state,
                &function.span,
                &fndef_singleton,
                &params,
                &ret,
                &*enss,
                default_ens,
            )?;
            fndef_axioms.push(ens_forall);
        }
    }

    let mut functionx = function.x.clone();
    assert!(functionx.fndef_axioms.is_none());
    functionx.fndef_axioms = Some(Arc::new(fndef_axioms));
    Ok(Spanned::new(function.span.clone(), functionx))
}

fn simplify_function(
    ctx: &GlobalCtx,
    state: &mut State,
    function: &Function,
) -> Result<Function, VirErr> {
    state.reset_for_function();
    let mut functionx = function.x.clone();

    if let Some(r) = functionx.returns.clone() {
        functionx.returns = None;

        if functionx.ens_has_return {
            let var = SpannedTyped::new(
                &r.span,
                &functionx.ret.x.typ,
                ExprX::Var(functionx.ret.x.name.clone()),
            );
            let eq = mk_eq(&r.span, &var, &r);
            Arc::make_mut(&mut functionx.ensure.0).push(eq);
        } else {
            // For a unit return type, any returns clause is tautological so we
            // can just skip appending to the postconditions.
        }
    }

    let local =
        LocalCtxt { span: function.span.clone(), typ_params: (*functionx.typ_params).clone() };

    let is_trait_impl = matches!(functionx.kind, FunctionKind::TraitMethodImpl { .. });

    // If possible, rename parameters to drop the rustc id
    let mut param_ids: HashSet<Ident> = HashSet::new();
    let mut rename_ok = true;
    for p in functionx.params.iter() {
        let x = &p.x.name.0;
        if param_ids.contains(x) {
            rename_ok = false;
        }
        param_ids.insert(x.clone());
    }
    let mut param_names: Vec<VarIdent> = Vec::new();
    for param in functionx.params.iter() {
        let prev = param.x.name.clone();
        let name = if rename_ok {
            let name = VarIdent(prev.0.clone(), crate::ast::VarIdentDisambiguate::VirParam);
            state.rename_vars.insert(prev, name.clone()).map(|_| panic!("rename params"));
            name
        } else {
            prev
        };
        param_names.push(name);
    }
    let ret_name = if rename_ok && !param_ids.contains(&functionx.ret.x.name.0) {
        let prev = functionx.ret.x.name.clone();
        let name = VarIdent(prev.0.clone(), crate::ast::VarIdentDisambiguate::VirParam);
        state.rename_vars.insert(prev, name.clone()).map(|_| panic!("rename ret"));
        name
    } else {
        functionx.ret.x.name.clone()
    };

    // To simplify the AIR/SMT encoding, add a dummy argument to any function with 0 arguments
    if functionx.typ_params.len() == 0
        && functionx.params.len() == 0
        && !matches!(functionx.item_kind, ItemKind::Const)
        && !matches!(functionx.item_kind, ItemKind::Static)
        && !functionx.attrs.broadcast_forall
        && !is_trait_impl
    {
        let paramx = crate::ast::ParamX {
            name: dummy_param_name(),
            typ: Arc::new(TypX::Int(IntRange::Int)),
            mode: Mode::Spec,
            user_mut: false,
            is_mut: false,
            unwrapped_info: None,
        };
        param_names.push(paramx.name.clone());
        let param = Spanned::new(function.span.clone(), paramx);
        functionx.params = Arc::new(vec![param]);
    }

    let function = Spanned::new(function.span.clone(), functionx);
    let mut map: VisitorScopeMap = ScopeMap::new();
    let function = crate::ast_visitor::map_function_visitor_env(
        &function,
        &mut map,
        state,
        &|state, map, expr| simplify_one_expr(ctx, state, map, expr),
        &|state, _, stmt| simplify_one_stmt(ctx, state, stmt),
        &|state, typ| simplify_one_typ(&local, state, typ),
        &|state, map, place| simplify_one_place(ctx, state, map, place),
    )?;
    let mut functionx = function.x.clone();
    assert!(functionx.params.len() == param_names.len());
    functionx.params = Arc::new(
        functionx
            .params
            .iter()
            .zip(param_names.iter())
            .map(|(p, x)| p.new_x(crate::ast::ParamX { name: x.clone(), ..p.x.clone() }))
            .collect(),
    );
    functionx.ret =
        functionx.ret.new_x(crate::ast::ParamX { name: ret_name, ..functionx.ret.x.clone() });

    Ok(Spanned::new(function.span.clone(), functionx))
}

fn simplify_datatype(state: &mut State, datatype: &Datatype) -> Result<Datatype, VirErr> {
    let mut local = LocalCtxt { span: datatype.span.clone(), typ_params: Vec::new() };
    for (x, _strict_pos) in datatype.x.typ_params.iter() {
        local.typ_params.push(x.clone());
    }
    crate::ast_visitor::map_datatype_visitor_env(datatype, state, &|state, typ| {
        simplify_one_typ(&local, state, typ)
    })
}

fn simplify_trait_impl(state: &mut State, imp: &TraitImpl) -> Result<TraitImpl, VirErr> {
    let mut local = LocalCtxt { span: imp.span.clone(), typ_params: Vec::new() };
    for x in imp.x.typ_params.iter() {
        local.typ_params.push(x.clone());
    }
    crate::ast_visitor::map_trait_impl_visitor_env(imp, state, &|state, typ| {
        simplify_one_typ(&local, state, typ)
    })
}

fn simplify_assoc_type_impl(
    state: &mut State,
    assoc: &AssocTypeImpl,
) -> Result<AssocTypeImpl, VirErr> {
    let mut local = LocalCtxt { span: assoc.span.clone(), typ_params: Vec::new() };
    for x in assoc.x.typ_params.iter() {
        local.typ_params.push(x.clone());
    }
    crate::ast_visitor::map_assoc_type_impl_visitor_env(assoc, state, &|state, typ| {
        simplify_one_typ(&local, state, typ)
    })
}

/*
fn mk_fun_decl(
    span: &Span,
    path: &Path,
    typ_params: &Idents,
    params: &Params,
    ret: &Param,
) -> Function {
    let mut attrs: crate::ast::FunctionAttrsX = Default::default();
    attrs.no_auto_trigger = true;
    Spanned::new(
        span.clone(),
        FunctionX {
            name: Arc::new(FunX { path: path.clone() }),
            visibility: Visibility { owning_module: None, restricted_to: None },
            mode: Mode::Spec,
            fuel: 0,
            typ_params: typ_params.clone(),
            typ_bounds: Arc::new(vec![]),
            params: params.clone(),
            ret: ret.clone(),
            require: Arc::new(vec![]),
            ensure: Arc::new(vec![]),
            decrease: None,
            is_const: false,
            is_abstract: false,
            attrs: Arc::new(attrs),
            body: None,
        },
    )
}
*/

pub fn simplify_krate(ctx: &mut GlobalCtx, krate: &Krate) -> Result<Krate, VirErr> {
    let KrateX {
        functions,
        reveal_groups,
        datatypes,
        opaque_types,
        traits,
        trait_impls,
        assoc_type_impls,
        modules: module_ids,
        external_fns,
        external_types,
        path_as_rust_names,
        arch,
    } = &**krate;
    let mut state = State::new();

    // Always add this because unit values might be added later, after ast_simplify.
    state.tuple_type_name(0);

    let mut datatypes = vec_map_result(&datatypes, |d| simplify_datatype(&mut state, d))?;
    ctx.datatypes = Arc::new(
        datatypes
            .iter()
            .map(|d| (d.x.name.expect_path(), (d.x.typ_params.clone(), d.x.variants.clone())))
            .collect(),
    );
    let functions = vec_map_result(functions, |f| simplify_function(ctx, &mut state, f))?;
    let trait_impls = vec_map_result(&trait_impls, |t| simplify_trait_impl(&mut state, t))?;
    let assoc_type_impls =
        vec_map_result(&assoc_type_impls, |a| simplify_assoc_type_impl(&mut state, a))?;

    let functions = vec_map_result(&functions, |f: &Function| {
        if need_fndef_axiom(&state.fndef_typs, f) {
            add_fndef_axioms_to_function(ctx, &mut state, f)
        } else {
            Ok(f.clone())
        }
    })?;

    // Add a generic datatype to represent each tuple arity
    // Iterate in sorted order to get consistent output
    let mut tuples: Vec<usize> = state.tuple_typs.into_iter().collect();
    tuples.sort();
    for arity in tuples {
        let visibility = Visibility { restricted_to: None };
        let transparency = DatatypeTransparency::WhenVisible(visibility.clone());
        let acc = crate::ast::AcceptRecursiveType::RejectInGround;
        let typ_params = Arc::new((0..arity).map(|i| (prefix_tuple_param(i), acc)).collect());
        let mut fields: Vec<Field> = Vec::new();
        for i in 0..arity {
            let typ = Arc::new(TypX::TypParam(prefix_tuple_param(i)));
            let vis = Visibility { restricted_to: None };
            // Note: the mode is irrelevant at this stage, so we arbitrarily use Mode::Exec
            fields.push(ident_binder(&positional_field_ident(i), &(typ, Mode::Exec, vis)));
        }
        let variant = Variant {
            name: prefix_tuple_variant(arity),
            fields: Arc::new(fields),
            ctor_style: CtorPrintStyle::Tuple,
        };
        let variants = Arc::new(vec![variant]);
        let datatypex = DatatypeX {
            name: Dt::Tuple(arity),
            proxy: None,
            visibility,
            owning_module: None,
            transparency,
            typ_params,
            typ_bounds: Arc::new(vec![]),
            variants,
            mode: Mode::Exec,
            ext_equal: arity > 0,
            user_defined_invariant_fn: None,
            sized_constraint: if arity == 0 {
                None
            } else {
                Some(Arc::new(TypX::TypParam(prefix_tuple_param(arity - 1))))
            },
            destructor: false,
        };
        datatypes.push(Spanned::new(ctx.no_span.clone(), datatypex));
    }

    let mut closures: Vec<_> = state.closure_typs.into_iter().collect();
    closures.sort_by_key(|kv| kv.0);
    for (_id, path) in closures {
        // Right now, we translate the closure type into an a global datatype.
        //
        // However, I'm pretty sure an anonymous closure can't actually be referenced
        // from outside the item that defines it (Rust seems to represent it as an
        // "opaque type" if it escapes through an existential type, which Verus currently
        // doesn't support anyway.)
        // So in principle, we could make the type private to the item and not emit any
        // global declarations for it.
        //
        // Also, note that the closure type doesn't take any type params, although
        // theoretically it depends on any type params of the enclosing item.
        // e.g., if we have
        //      fn foo<T>(...) {
        //          let x = |t: T| { ... };
        //      }
        // Then the closure type is dependent on T.
        // But since the closure type is only referenced from the item, we can consider
        // T to be fixed, so we don't need to define the closure type polymorphically.

        // Also, note that Rust already prohibits a closure type from depending on itself
        // (not even via reference types, which would be allowed for other types).
        // As such, we don't have to worry about any kind of recursion-checking:
        // a closure type cannot possibly be involved in any type cycle.
        // (In principle, the closure should depend negatively on its param and return types,
        // since they are arguments to the 'requires' and 'ensures' predicates, but thanks
        // to Rust's restrictions, we don't have to do any additional checks.)

        let visibility = Visibility { restricted_to: None };
        let transparency = DatatypeTransparency::Never;

        let typ_params = Arc::new(vec![]);
        let variants = Arc::new(vec![]);

        let datatypex = DatatypeX {
            name: Dt::Path(path),
            proxy: None,
            visibility,
            owning_module: None,
            transparency,
            typ_params,
            typ_bounds: Arc::new(vec![]),
            variants,
            mode: Mode::Exec,
            ext_equal: false,
            user_defined_invariant_fn: None,
            sized_constraint: None,
            destructor: false,
        };
        datatypes.push(Spanned::new(ctx.no_span.clone(), datatypex));
    }

    let traits = traits.clone();
    let module_ids = module_ids.clone();
    let external_fns = external_fns.clone();
    let external_types = external_types.clone();
    let krate = Arc::new(KrateX {
        functions,
        reveal_groups: reveal_groups.clone(),
        datatypes,
        opaque_types: opaque_types.clone(),
        traits,
        trait_impls,
        assoc_type_impls,
        modules: module_ids,
        external_fns,
        external_types,
        path_as_rust_names: path_as_rust_names.clone(),
        arch: arch.clone(),
    });
    *ctx = crate::context::GlobalCtx::new(
        &krate,
        ctx.crate_name.clone(),
        ctx.no_span.clone(),
        ctx.rlimit,
        ctx.interpreter_log.clone(),
        ctx.func_call_graph_log.clone(),
        ctx.solver.clone(),
        true,
        ctx.check_api_safety,
        ctx.axiom_usage_info,
        ctx.new_mut_ref,
        ctx.no_bv_simplify,
        ctx.report_long_running,
    )?;
    Ok(krate)
}

pub fn merge_krates(krates: Vec<Krate>) -> Result<Krate, VirErr> {
    let mut krates = krates.into_iter();
    let mut kratex: KrateX = (*krates.next().expect("at least one crate")).clone();
    for k in krates {
        let KrateX {
            functions,
            reveal_groups,
            datatypes,
            opaque_types,
            traits,
            trait_impls,
            assoc_type_impls,
            modules,
            external_fns,
            external_types,
            path_as_rust_names,
            arch,
        } = &*k;
        kratex.functions.extend(functions.clone());
        kratex.reveal_groups.extend(reveal_groups.clone());
        kratex.datatypes.extend(datatypes.clone());
        kratex.opaque_types.extend(opaque_types.clone());
        kratex.traits.extend(traits.clone());
        kratex.trait_impls.extend(trait_impls.clone());
        kratex.assoc_type_impls.extend(assoc_type_impls.clone());
        kratex.modules.extend(modules.clone());
        kratex.external_fns.extend(external_fns.clone());
        kratex.external_types.extend(external_types.clone());
        kratex.path_as_rust_names.extend(path_as_rust_names.clone());
        kratex.arch.word_bits = {
            let word_bits = match (arch.word_bits, kratex.arch.word_bits) {
                (crate::ast::ArchWordBits::Exactly(l), crate::ast::ArchWordBits::Exactly(r)) => {
                    if l != r {
                        return Err(crate::messages::error_bare(
                            "all crates must have compatible arch_word_bits (set via `global size_of usize`",
                        ));
                    } else {
                        crate::ast::ArchWordBits::Exactly(l)
                    }
                }
                (crate::ast::ArchWordBits::Either32Or64, other)
                | (other, crate::ast::ArchWordBits::Either32Or64) => other,
            };
            if let crate::ast::ArchWordBits::Exactly(e) = &word_bits {
                assert!(*e == 32 || *e == 64);
            }
            word_bits
        };
    }
    Ok(Arc::new(kratex))
}
