use crate::ast::{
    CallTarget, CallTargetKind, Expr, ExprX, Fun, Function, FunctionKind, FunctionX, GenericBound,
    GenericBoundX, GenericBounds, Ident, ImplPath, ImplPaths, Krate, Mode, Path, SpannedTyped,
    Trait, TraitImpl, TraitX, Typ, TypX, Typs, VirErr, Visibility, WellKnownItem,
};
use crate::ast_util::path_as_friendly_rust_name;
use crate::ast_visitor::VisitorScopeMap;
use crate::context::Ctx;
use crate::def::Spanned;
use crate::messages::{error, warning, Span, ToAny};
use crate::sst_to_air::typ_to_ids;
use air::ast::{Command, CommandX, Commands, DeclX};
use air::ast_util::{ident_apply, mk_bind_expr, mk_implies, mk_unnamed_axiom, str_typ};
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn get_trait(fun: &Fun) -> Path {
    fun.path.pop_segment()
}

fn demote_one_expr(
    traits: &HashSet<Path>,
    internal_traits: &HashSet<Path>,
    funs: &HashSet<Fun>,
    expr: &Expr,
) -> Result<Expr, VirErr> {
    match &expr.x {
        ExprX::Call(
            CallTarget::Fun(
                CallTargetKind::DynamicResolved {
                    resolved: resolved_fun,
                    typs: resolved_typs,
                    impl_paths,
                    is_trait_default: _,
                },
                fun,
                _typs,
                _impl_paths,
                autospec_usage,
            ),
            args,
        ) if !traits.contains(&get_trait(fun)) || !funs.contains(fun) => {
            let ct = CallTarget::Fun(
                CallTargetKind::Static,
                resolved_fun.clone(),
                resolved_typs.clone(),
                impl_paths.clone(),
                *autospec_usage,
            );
            Ok(expr.new_x(ExprX::Call(ct, args.clone())))
        }
        ExprX::Call(
            CallTarget::Fun(
                CallTargetKind::DynamicResolved {
                    resolved: resolved_fun,
                    typs: _,
                    impl_paths: _,
                    is_trait_default: true,
                },
                fun,
                typs,
                impl_paths,
                autospec_usage,
            ),
            args,
        ) if traits.contains(&get_trait(fun))
            && !internal_traits.contains(&get_trait(fun))
            && funs.contains(fun)
            && !funs.contains(resolved_fun) =>
        {
            // Calls to external trait default functions are considered to be calls
            // to the trait declaration (since we have a spec for the declaration)
            let ct = CallTarget::Fun(
                CallTargetKind::Dynamic,
                fun.clone(),
                typs.clone(),
                impl_paths.clone(),
                *autospec_usage,
            );
            Ok(expr.new_x(ExprX::Call(ct, args.clone())))
        }
        _ => Ok(expr.clone()),
    }
}

// We consider methods for external traits to be static.
pub fn demote_external_traits(
    diagnostics: &impl air::messages::Diagnostics,
    path_to_well_known_item: &HashMap<Path, WellKnownItem>,
    krate: &Krate,
) -> Result<Krate, VirErr> {
    check_no_dupe_impls(krate)?;

    let traits: HashSet<Path> = krate.traits.iter().map(|t| t.x.name.clone()).collect();
    let internal_traits: HashSet<Path> =
        krate.traits.iter().filter(|t| t.x.proxy.is_none()).map(|t| t.x.name.clone()).collect();
    let funs: HashSet<Fun> = krate.functions.iter().map(|f| f.x.name.clone()).collect();

    let mut kratex = (**krate).clone();
    for function in &mut kratex.functions {
        for bound in function.x.typ_bounds.iter() {
            let trait_path = match &**bound {
                GenericBoundX::Trait(path, _) => path,
                GenericBoundX::TypEquality(path, _, _, _) => path,
                GenericBoundX::ConstTyp(..) => continue,
            };
            let our_trait = traits.contains(trait_path);
            if !our_trait {
                diagnostics.report(
                    &warning(
                        &function.span,
                        format!(
                            "cannot use external trait {} as a bound without declaring the trait \
                            (use #[verifier::external_trait_specification] to declare the trait); \
                            this is a warning for now but will eventually be an error",
                            crate::ast_util::path_as_friendly_rust_name(trait_path)
                        ),
                    )
                    .to_any(),
                );
            }
        }

        if let FunctionKind::TraitMethodImpl { method, trait_path, .. } = &function.x.kind {
            let our_trait_method = traits.contains(trait_path) && funs.contains(method);
            let mut functionx = function.x.clone();
            if !our_trait_method {
                if path_to_well_known_item.get(trait_path) == Some(&WellKnownItem::DropTrait) {
                    if !function.x.require.is_empty() {
                        return Err(error(
                            &function.span,
                            "requires are not allowed on the implementation for Drop",
                        ));
                    }
                    if !matches!(&function.x.mask_spec, Some(crate::ast::MaskSpec::InvariantOpens(es)) if es.len() == 0)
                    {
                        return Err(error(
                            &function.span,
                            "the implementation for Drop must be marked opens_invariants none",
                        ));
                    }
                    if !matches!(&function.x.unwind_spec, Some(crate::ast::UnwindSpec::NoUnwind)) {
                        return Err(error(
                            &function.span,
                            "the implementation for Drop must be marked no_unwind",
                        ));
                    }
                }
                check_modes(function, &function.span)?;
                functionx.kind = FunctionKind::Static;
            }
            *function = Spanned::new(function.span.clone(), functionx);
        }

        if let FunctionKind::ForeignTraitMethodImpl {
            method,
            impl_path,
            trait_path,
            trait_typ_args,
        } = &function.x.kind
        {
            let our_trait_method = traits.contains(trait_path) && funs.contains(method);
            let mut functionx = function.x.clone();
            if our_trait_method {
                functionx.kind = FunctionKind::TraitMethodImpl {
                    method: method.clone(),
                    impl_path: impl_path.clone(),
                    trait_path: trait_path.clone(),
                    trait_typ_args: trait_typ_args.clone(),
                    inherit_body_from: None,
                };
            } else {
                check_modes(function, &function.x.proxy.as_ref().unwrap().span)?;
                functionx.kind = FunctionKind::Static;
            }
            *function = Spanned::new(function.span.clone(), functionx);
        }

        let mut map: VisitorScopeMap = ScopeMap::new();
        *function = crate::ast_visitor::map_function_visitor_env(
            &function,
            &mut map,
            &mut (),
            &|_state, _, expr| demote_one_expr(&traits, &internal_traits, &funs, expr),
            &|_state, _, stmt| Ok(vec![stmt.clone()]),
            &|_state, typ| Ok(typ.clone()),
        )?;
    }

    Ok(Arc::new(kratex))
}

pub fn rewrite_one_external_typ(from_path: &Path, to_path: &Path, typ: &Typ) -> Typ {
    match &**typ {
        TypX::Projection { trait_typ_args, trait_path, name } if trait_path == from_path => {
            Arc::new(TypX::Projection {
                trait_typ_args: trait_typ_args.clone(),
                trait_path: to_path.clone(),
                name: name.clone(),
            })
        }
        _ => typ.clone(),
    }
}

pub fn rewrite_external_typ(from_path: &Path, to_path: &Path, typ: &Typ) -> Typ {
    let ft = |t: &Typ| Ok(rewrite_one_external_typ(from_path, to_path, t));
    crate::ast_visitor::map_typ_visitor(typ, &ft).expect("rewrite_external_typ")
}

pub fn rewrite_external_bounds(
    from_path: &Path,
    to_path: &Path,
    bounds: &GenericBounds,
) -> GenericBounds {
    let mut bs: Vec<GenericBound> = Vec::new();
    for bound in bounds.iter() {
        let b = match &**bound {
            GenericBoundX::Trait(path, ts) if path == from_path => {
                Arc::new(GenericBoundX::Trait(to_path.clone(), ts.clone()))
            }
            GenericBoundX::TypEquality(path, ts, x, t) if path == from_path => Arc::new(
                GenericBoundX::TypEquality(to_path.clone(), ts.clone(), x.clone(), t.clone()),
            ),
            _ => bound.clone(),
        };
        bs.push(b);
    }
    let ft = |_: &mut (), t: &Typ| Ok(rewrite_one_external_typ(from_path, to_path, t));
    crate::ast_visitor::map_generic_bounds_visitor(&Arc::new(bs), &mut (), &ft)
        .expect("rewrite_external_bounds")
}

pub fn rewrite_external_function(
    from_path: &Path,
    to_path: &Path,
    function: &Function,
) -> Function {
    let ft = |_: &mut (), t: &Typ| Ok(rewrite_one_external_typ(from_path, to_path, t));
    let mut map: VisitorScopeMap = ScopeMap::new();
    crate::ast_visitor::map_function_visitor_env(
        function,
        &mut map,
        &mut (),
        &|_state, _, expr| Ok(expr.clone()),
        &|_state, _, stmt| Ok(vec![stmt.clone()]),
        &ft,
    )
    .expect("rewrite_external_typ")
}

/*
In Rust, traits can have default implementations of methods.  For example:
    trait T {
        fn f();
        fn g() { Self::f(); Self::g(); }
        fn h();
    }
The simplest way to handle termination checking would be to make a Node::Fun
for the default implementation, following rustc's internal approach, which:
- represents the default implementation as a function T::g
- represents g's calls Self::f() and Self::g() as dynamically dispatched through
  the Self parameter, via the "Self: T" bound.
- represents other calls to T::g as statically bound to T::g (assuming this isn't overridden
  by the impl that is being called through).
However, requiring the "Self: T" be available in T::g would make it hard for impls to use g:
    impl T for bool {
        fn f() {}
        fn h() { Self::g(); }
    }
In this simple encoding, the impl of h can't call it's own inherited copy of g,
because it doesn't yet satisfy the "bool: T" bound (this bound isn't satisfied until
after the impl's f and h are fully defined.)

Instead of using the simple approach described above,
we make termination checking more flexible by creating a Node::Fun for each
inherited copy of a default method, so that there are potentially many Node::Fun values
for a single default method.  In the example above, there is one Node::Fun for the
original T::g in T and one Node::Fun for the copy of T::g inherited by "impl T for bool".
As long as we check termination for all the copies, it is safe to make copies and
to dispatch calls to specific copy for the impl we are calling.
In the example above, h's call to Self::g() calls "impl T for bool"'s copy of g,
not the original g in T.
We treat the inherited copies of default methods just like ordinary methods implemented
in the impl, so that the inherited copy does not require a "Self: T" bound.
This means that the example above is checked as if all the method were implemented
from scratch inside the impl:
    impl T for bool {
        fn f() {}
        fn g() { Self::f(); Self::g(); } // this is our own *copy* of the method inherited from T
        fn h() { Self::g(); }
    }

The function inherit_default_bodies creates these copies of the default implementations.

The function redirect_calls_in_default_methods patches up termination checking for
calls made from the bodies of copied methods, since rustc's resolution of these calls
is in the context of the original trait method, not the context of the inherited copy.
(It might be cleaner to get rustc to make these copies and do its own resolution,
but this isn't so easy for us, since the default method might come from a separate crate,
and in this case rustc wouldn't have the HIR for the method.)

Finally, resolved calls to a default method are reresolved as calls to the appropriate
copy by fn_call_to_vir in the rust_verify crate.  For example:
- remove_self_trait_bound = Some((trait_id, &mut self_trait_impl_path));
- if let Some(vir::ast::ImplPath::TraitImplPath(impl_path)) = self_trait_impl_path {
    f = vir::def::trait_inherit_default_name(&f, &impl_path)
  }
*/
pub fn inherit_default_bodies(krate: &Krate) -> Result<Krate, VirErr> {
    let mut kratex = (**krate).clone();

    let mut trait_map: HashMap<Path, &Trait> = HashMap::new();
    // map trait_path to all default methods in trait
    let mut default_methods: HashMap<Path, Vec<&Function>> = HashMap::new();
    // set of all impl methods (&impl_path, &trait_method_name)
    let mut method_impls: HashSet<(&Path, &Fun)> = HashSet::new();
    for tr in &krate.traits {
        if trait_map.contains_key(&tr.x.name) {
            return Err(crate::well_formed::trait_conflict_error(
                &trait_map[&tr.x.name],
                tr,
                "duplicate specification for",
            ));
        }
        trait_map.insert(tr.x.name.clone(), tr);
        assert!(!default_methods.contains_key(&tr.x.name));
        default_methods.insert(tr.x.name.clone(), Vec::new());
    }
    for f in &krate.functions {
        if let FunctionKind::TraitMethodDecl { trait_path } = &f.x.kind {
            if f.x.body.is_some() {
                default_methods.get_mut(trait_path).expect("trait_path").push(f);
            }
        }
        if let FunctionKind::TraitMethodImpl { impl_path, method, .. } = &f.x.kind {
            let p = (impl_path, method);
            assert!(!method_impls.contains(&p));
            method_impls.insert(p);
        }
    }

    for trait_impl in &krate.trait_impls {
        if !trait_map.contains_key(&trait_impl.x.trait_path) {
            // skip external traits and marker traits
            continue;
        }
        for default_function in &default_methods[&trait_impl.x.trait_path] {
            let impl_path = &trait_impl.x.impl_path;
            let method = &default_function.x.name;
            if !method_impls.contains(&(impl_path, method)) {
                // Create a shell Function for trait_impl, with these purposes:
                // - used as a recursion::Node::Fun in the call graph
                // - for spec functions, used by sst_to_air_func to create a definition axiom
                let inherit_kind = FunctionKind::TraitMethodImpl {
                    method: default_function.x.name.clone(),
                    impl_path: impl_path.clone(),
                    trait_path: trait_impl.x.trait_path.clone(),
                    trait_typ_args: trait_impl.x.trait_typ_args.clone(),
                    inherit_body_from: Some(default_function.x.name.clone()),
                };
                let tr = trait_map[&trait_impl.x.trait_path];
                let mut subst_map: HashMap<Ident, Typ> = HashMap::new();
                assert!(trait_impl.x.trait_typ_args.len() == tr.x.typ_params.len() + 1);
                let tr_params = tr.x.typ_params.iter().map(|(x, _)| x);
                for (x, t) in vec![crate::def::trait_self_type_param()]
                    .iter()
                    .chain(tr_params)
                    .zip(trait_impl.x.trait_typ_args.iter())
                {
                    assert!(!subst_map.contains_key(x));
                    subst_map.insert(x.clone(), t.clone());
                }
                let ft = |_: &mut (), t: &Typ| -> Result<Typ, VirErr> {
                    match &**t {
                        TypX::TypParam(x) => Ok(subst_map[x].clone()),
                        _ => Ok(t.clone()),
                    }
                };
                let params = crate::ast_visitor::map_params_visitor(
                    &default_function.x.params,
                    &mut (),
                    &ft,
                )
                .unwrap();
                let ret =
                    crate::ast_visitor::map_param_visitor(&default_function.x.ret, &mut (), &ft)
                        .unwrap();
                let name =
                    crate::def::trait_inherit_default_name(&default_function.x.name, &impl_path);
                let visibility = Visibility {
                    restricted_to: default_function
                        .x
                        .visibility
                        .restricted_to
                        .clone()
                        .and(trait_impl.x.owning_module.clone()),
                };
                let inherit_functionx = FunctionX {
                    name,
                    proxy: None,
                    kind: inherit_kind,
                    // TODO: we could try to use the impl visibility and owning module for better pruning:
                    visibility,
                    owning_module: trait_impl.x.owning_module.clone(),
                    mode: default_function.x.mode,
                    fuel: 1,
                    typ_params: trait_impl.x.typ_params.clone(),
                    typ_bounds: trait_impl.x.typ_bounds.clone(),
                    params,
                    ret,
                    require: Arc::new(vec![]),
                    ensure: Arc::new(vec![]),
                    decrease: Arc::new(vec![]),
                    decrease_when: None,
                    decrease_by: None,
                    broadcast_forall: None,
                    fndef_axioms: None,
                    mask_spec: None,
                    unwind_spec: None,
                    item_kind: default_function.x.item_kind,
                    publish: default_function.x.publish,
                    attrs: Arc::new(crate::ast::FunctionAttrsX::default()),
                    body: None,
                    extra_dependencies: vec![],
                };
                kratex.functions.push(default_function.new_x(inherit_functionx));
            }
        }
    }

    Ok(Arc::new(kratex))
}

pub(crate) fn redirect_calls_in_default_methods(
    func_map: &HashMap<Fun, Function>,
    trait_impl_map: &HashMap<(Fun, Path), Fun>,
    function: &Function,
    span: &Span,
    callee: Fun,
    ts: Typs,
    impl_paths: ImplPaths,
) -> Result<(Fun, ImplPaths), VirErr> {
    let f2 = &func_map[&callee];
    if let (
        FunctionKind::TraitMethodImpl {
            trait_path: caller_trait,
            impl_path: caller_impl,
            inherit_body_from,
            ..
        },
        FunctionKind::TraitMethodDecl { trait_path: callee_trait, .. },
    ) = (&function.x.kind, &f2.x.kind)
    {
        if callee_trait == caller_trait {
            if let Some(f_trait) = inherit_body_from {
                let f_trait = &func_map[f_trait];
                let trait_typ_args = f_trait
                    .x
                    .typ_params
                    .iter()
                    .map(|x| Arc::new(TypX::TypParam(x.clone())))
                    .collect();
                if crate::ast_util::n_types_equal(&ts, &Arc::new(trait_typ_args)) {
                    // Since we don't have a copy of the default method body
                    // specialized to our impl, we need to do extra work to
                    // redirect calls from the inherited body back to our own impl.
                    // See comments above regarding trait_inherit_default_name.
                    let default_name = crate::def::trait_inherit_default_name(&callee, caller_impl);
                    let callee = if func_map.contains_key(&default_name) {
                        // turn T::f into impl::default-f
                        default_name
                    } else {
                        // turn T::f into impl::f
                        trait_impl_map[&(callee, caller_impl.clone())].clone()
                    };

                    // If we can directly resolve a call from f1 inside impl to f2 inside
                    // the same impl, then we don't try to pass a dictionary for impl from f1 to f2.
                    // This is a useful special case where we can avoid a spurious cyclic dependency
                    // error.
                    let filter = |p: &ImplPath| {
                        let f2 = &func_map[&callee];
                        if let (
                            FunctionKind::TraitMethodImpl { impl_path: caller_impl, .. },
                            FunctionKind::TraitMethodImpl { impl_path: callee_impl, .. },
                        ) = (&function.x.kind, &f2.x.kind)
                        {
                            &ImplPath::TraitImplPath(caller_impl.clone()) != p
                                || &ImplPath::TraitImplPath(callee_impl.clone()) != p
                        } else {
                            true
                        }
                    };
                    let impl_paths = Arc::new(impl_paths.iter().cloned().filter(filter).collect());

                    return Ok((callee, impl_paths));
                } else {
                    // In a normal body, we rely on impl_paths to detect cycles.
                    // Unfortunately, in an inherited body, we don't have impl_paths
                    // specialized to our impl, so we conservatively reject
                    // the call.
                    // (Note: it's not clear that this case is actually possible;
                    // we could consider this to be a panic rather than an Err.)
                    return Err(error(
                        span,
                        "call from trait default method to same trait with different type arguments is not allowed",
                    ));
                }
            }
        }
    }
    Ok((callee, impl_paths))
}

fn check_modes(function: &Function, span: &Span) -> Result<(), VirErr> {
    if function.x.mode != Mode::Exec {
        return Err(error(span, "function for external trait must have mode 'exec'"));
    }
    for param in function.x.params.iter() {
        if param.x.mode != Mode::Exec {
            return Err(error(
                span,
                "function for external trait must have all parameters have mode 'exec'",
            ));
        }
    }
    if function.x.ret.x.mode != Mode::Exec {
        return Err(error(
            span,
            "function for external trait must have all parameters have mode 'exec'",
        ));
    }
    Ok(())
}

pub(crate) fn trait_bounds_to_ast(ctx: &Ctx, span: &Span, typ_bounds: &GenericBounds) -> Vec<Expr> {
    let mut bound_exprs: Vec<Expr> = Vec::new();
    for bound in typ_bounds.iter() {
        let exprx = match &**bound {
            GenericBoundX::Trait(path, typ_args) => {
                if !ctx.trait_map.contains_key(path) {
                    continue;
                }
                let op = crate::ast::NullaryOpr::TraitBound(path.clone(), typ_args.clone());
                ExprX::NullaryOpr(op)
            }
            GenericBoundX::TypEquality(path, typ_args, name, typ) => {
                let op = crate::ast::NullaryOpr::TypEqualityBound(
                    path.clone(),
                    typ_args.clone(),
                    name.clone(),
                    typ.clone(),
                );
                ExprX::NullaryOpr(op)
            }
            GenericBoundX::ConstTyp(t1, t2) => {
                let op = crate::ast::NullaryOpr::ConstTypBound(t1.clone(), t2.clone());
                ExprX::NullaryOpr(op)
            }
        };
        bound_exprs.push(SpannedTyped::new(span, &Arc::new(TypX::Bool), exprx));
    }
    bound_exprs
}

pub(crate) fn trait_bounds_to_sst(
    ctx: &Ctx,
    span: &Span,
    typ_bounds: &GenericBounds,
) -> Vec<crate::sst::Exp> {
    let mut bound_exps: Vec<crate::sst::Exp> = Vec::new();
    for bound in typ_bounds.iter() {
        let expx = match &**bound {
            GenericBoundX::Trait(path, typ_args) => {
                if !ctx.trait_map.contains_key(path) {
                    continue;
                }
                let op = crate::ast::NullaryOpr::TraitBound(path.clone(), typ_args.clone());
                crate::sst::ExpX::NullaryOpr(op)
            }
            GenericBoundX::TypEquality(path, typ_args, name, typ) => {
                let op = crate::ast::NullaryOpr::TypEqualityBound(
                    path.clone(),
                    typ_args.clone(),
                    name.clone(),
                    typ.clone(),
                );
                crate::sst::ExpX::NullaryOpr(op)
            }
            GenericBoundX::ConstTyp(t1, t2) => {
                let op = crate::ast::NullaryOpr::ConstTypBound(t1.clone(), t2.clone());
                crate::sst::ExpX::NullaryOpr(op)
            }
        };
        bound_exps.push(SpannedTyped::new(span, &Arc::new(TypX::Bool), expx));
    }
    bound_exps
}

pub(crate) fn trait_bound_to_air(
    ctx: &Ctx,
    path: &Path,
    typ_args: &Typs,
) -> Option<air::ast::Expr> {
    if !ctx.trait_map.contains_key(path) {
        return None;
    }
    let mut typ_exprs: Vec<air::ast::Expr> = Vec::new();
    for t in typ_args.iter() {
        typ_exprs.extend(typ_to_ids(t));
    }
    Some(ident_apply(&crate::def::trait_bound(path), &typ_exprs))
}

pub(crate) fn typ_equality_bound_to_air(
    _ctx: &Ctx,
    trait_path: &Path,
    typ_args: &Typs,
    name: &Ident,
    typ: &Typ,
) -> air::ast::Expr {
    let mut typ_exprs: Vec<air::ast::Expr> = Vec::new();
    for t in typ_args.iter() {
        typ_exprs.extend(typ_to_ids(t));
    }
    let ids = typ_to_ids(typ);
    assert!(ids.len() == 2);
    let idd = &ids[0];
    let idt = &ids[1];
    let pd = ident_apply(&crate::def::projection(true, trait_path, name), &typ_exprs);
    let pt = ident_apply(&crate::def::projection(false, trait_path, name), &typ_exprs);
    let eqd = air::ast_util::mk_eq(idd, &pd);
    let eqt = air::ast_util::mk_eq(idt, &pt);
    air::ast_util::mk_and(&vec![eqd, eqt])
}

pub(crate) fn const_typ_bound_to_air(ctx: &Ctx, c: &Typ, t: &Typ) -> air::ast::Expr {
    let expr =
        air::ast_util::str_apply(crate::def::CONST_INT, &vec![crate::sst_to_air::typ_to_id(c)]);
    if let Some(inv) = crate::sst_to_air::typ_invariant(ctx, t, &expr) {
        inv
    } else {
        air::ast_util::mk_true()
    }
}

pub(crate) fn trait_bounds_to_air(ctx: &Ctx, typ_bounds: &GenericBounds) -> Vec<air::ast::Expr> {
    let mut bound_exprs: Vec<air::ast::Expr> = Vec::new();
    for bound in typ_bounds.iter() {
        match &**bound {
            GenericBoundX::Trait(path, typ_args) => {
                if let Some(bound) = trait_bound_to_air(ctx, path, typ_args) {
                    bound_exprs.push(bound);
                }
            }
            GenericBoundX::TypEquality(path, typ_args, name, typ) => {
                bound_exprs.push(typ_equality_bound_to_air(ctx, path, typ_args, name, typ));
            }
            GenericBoundX::ConstTyp(c, t) => {
                bound_exprs.push(const_typ_bound_to_air(ctx, c, t));
            }
        }
    }
    bound_exprs
}

pub fn traits_to_air(_ctx: &Ctx, krate: &crate::sst::KrateSst) -> Commands {
    // Axioms about broadcast_forall and spec functions need justification
    // for any trait bounds.
    let mut commands: Vec<Command> = Vec::new();

    // Declare predicates for bounds
    //   (declare-fun tr_bound%T (... Dcr Type ...) Bool)
    for tr in krate.traits.iter() {
        let mut tparams: Vec<air::ast::Typ> = Vec::new();
        tparams.extend(crate::def::types().iter().map(|s| str_typ(s))); // Self
        for _ in tr.x.typ_params.iter() {
            tparams.extend(crate::def::types().iter().map(|s| str_typ(s)));
        }
        let decl_trait_bound = Arc::new(DeclX::Fun(
            crate::def::trait_bound(&tr.x.name),
            Arc::new(tparams),
            air::ast_util::bool_typ(),
        ));
        commands.push(Arc::new(CommandX::Global(decl_trait_bound)));
    }
    Arc::new(commands)
}

pub fn trait_bound_axioms(ctx: &Ctx, traits: &Vec<Trait>) -> Commands {
    // forall typ_params. #[trigger] tr_bound%T(typ_params) ==> typ_bounds
    // Example:
    //   trait T<A: U> where Self: Q<A> {}
    // -->
    //   forall Self, A. tr_bound%T(Self, A) ==> tr_bound%U(A) && tr_bound%Q(Self, A)
    let mut commands: Vec<Command> = Vec::new();
    for tr in traits {
        let mut typ_params: Vec<crate::ast::Ident> =
            (*tr.x.typ_params).iter().map(|(x, _)| x.clone()).collect();
        typ_params.insert(0, crate::def::trait_self_type_param());
        let typ_args: Vec<Typ> =
            typ_params.iter().map(|x| Arc::new(TypX::TypParam(x.clone()))).collect();
        if let Some(tr_bound) = trait_bound_to_air(ctx, &tr.x.name, &Arc::new(typ_args)) {
            let all_bounds =
                tr.x.typ_bounds.iter().chain(tr.x.assoc_typs_bounds.iter()).cloned().collect();
            let typ_bounds = trait_bounds_to_air(ctx, &Arc::new(all_bounds));
            let qname = format!(
                "{}_{}",
                crate::ast_util::path_as_friendly_rust_name(&tr.x.name),
                crate::def::QID_TRAIT_TYPE_BOUNDS
            );
            let trigs = vec![tr_bound.clone()];
            let bind = crate::sst_to_air_func::func_bind_trig(
                ctx,
                qname,
                &Arc::new(typ_params),
                &Arc::new(vec![]),
                &trigs,
                false,
            );
            let imply = air::ast_util::mk_implies(&tr_bound, &air::ast_util::mk_and(&typ_bounds));
            let forall = mk_bind_expr(&bind, &imply);
            let axiom = Arc::new(DeclX::Axiom(air::ast::Axiom { named: None, expr: forall }));
            commands.push(Arc::new(CommandX::Global(axiom)));
        }
    }
    Arc::new(commands)
}

// Consider a trait impl like:
//   impl<A, B: T> U<A, B, B::X> for S { ... }
// This is an impl for U<S, A, B, B::X>.
// Naively, we might generate axioms triggered on U<S, A, B, B::X>.
// However, such a trigger could fail to match U<t0, t1, t2, t3>
// if t3 didn't have exactly the form B::X.
// So it's better to use a trigger that hides the B::X behind a fresh "hole" type parameter H0:
//   U<S, A, B, H0>
// with a restriction inside the axiom that H0 = B::X.
// This function returns a new type with projections replace by holes,
// along with a vector of H = typ equations.
pub(crate) fn hide_projections(typs: &Typs) -> (Typs, Vec<(Ident, Typ)>) {
    use crate::ast_visitor::{Rewrite, TypVisitor};
    struct ProjVisitor {
        holes: Vec<(Ident, Typ)>,
    }
    impl TypVisitor<Rewrite, ()> for ProjVisitor {
        fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, ()> {
            match &**typ {
                TypX::Projection { .. } => {
                    let x = crate::def::proj_param(self.holes.len());
                    self.holes.push((x.clone(), typ.clone()));
                    Ok(Arc::new(TypX::TypParam(x)))
                }
                _ => self.visit_typ_rec(typ),
            }
        }
    }
    let mut visitor = ProjVisitor { holes: Vec::new() };
    let typs = visitor.visit_typs(typs).expect("hide_projections");
    (Arc::new(typs), visitor.holes)
}

pub fn trait_impl_to_air(ctx: &Ctx, imp: &TraitImpl) -> Commands {
    // Axiom for bounds predicates (based on trait impls)
    // forall typ_params. typ_bounds ==> tr_bound%T(...typ_args...)
    // Example:
    //   trait T1 {}
    //   trait T2<A> {}
    //   impl<A: T1> T2<Set<A>> for S<Seq<A>>
    // -->
    //   forall A. tr_bound%T1(A) ==> tr_bound%T2(S<Seq<A>>, Set<A>)
    let (trait_typ_args, holes) = crate::traits::hide_projections(&imp.x.trait_typ_args);
    let (typ_params, eqs) = crate::sst_to_air_func::hide_projections_air(&imp.x.typ_params, holes);
    let tr_bound =
        if let Some(tr_bound) = trait_bound_to_air(ctx, &imp.x.trait_path, &trait_typ_args) {
            tr_bound
        } else {
            return Arc::new(vec![]);
        };
    let name =
        format!("{}_{}", path_as_friendly_rust_name(&imp.x.impl_path), crate::def::QID_TRAIT_IMPL);
    let trigs = vec![tr_bound.clone()];
    let bind = crate::sst_to_air_func::func_bind_trig(
        ctx,
        name,
        &typ_params,
        &Arc::new(vec![]),
        &trigs,
        false,
    );
    let mut req_bounds = trait_bounds_to_air(ctx, &imp.x.typ_bounds);
    req_bounds.extend(eqs);
    let imply = mk_implies(&air::ast_util::mk_and(&req_bounds), &tr_bound);
    let forall = mk_bind_expr(&bind, &imply);
    let axiom = mk_unnamed_axiom(forall);
    Arc::new(vec![Arc::new(CommandX::Global(axiom))])
}

pub fn check_no_dupe_impls(krate: &Krate) -> Result<(), VirErr> {
    let mut paths = HashMap::<Path, TraitImpl>::new();
    for trait_impl in krate.trait_impls.iter() {
        match paths.get(&trait_impl.x.impl_path) {
            Some(prev_trait_impl) => {
                let e = error(
                    &prev_trait_impl.span,
                    "duplicate specification for this trait implementation",
                )
                .primary_span(&trait_impl.span);
                return Err(e);
            }
            None => {
                paths.insert(trait_impl.x.impl_path.clone(), trait_impl.clone());
            }
        }
    }
    Ok(())
}

// Allow multiple external_trait_specification to specify different members of the same trait,
// so that we don't have to specify all of the default members of a trait at once (e.g. Iterator).
// We merge partial specifications together here.
pub fn merge_external_traits(krate: Krate) -> Result<Krate, VirErr> {
    use crate::ast_util::generic_bounds_equal;
    use crate::well_formed::trait_conflict_error;
    let mut kratex = (*krate).clone();
    let mut traits: Vec<Trait> = Vec::new();
    let mut prev_trait_index: HashMap<Path, usize> = HashMap::new();
    for t in &kratex.traits {
        if t.x.proxy.is_some() {
            if let Some(index) = prev_trait_index.get(&t.x.name) {
                let prev = &traits[*index];
                // merge t into prev
                let TraitX {
                    name,
                    proxy,
                    visibility,
                    typ_params,
                    typ_bounds,
                    assoc_typs,
                    assoc_typs_bounds,
                    mut methods,
                } = prev.x.clone();
                assert!(name == t.x.name);
                if visibility != t.x.visibility {
                    return Err(trait_conflict_error(prev, t, "mismatched visibilities"));
                }
                if typ_params != t.x.typ_params {
                    return Err(trait_conflict_error(prev, t, "mismatched type parameters"));
                }
                let mut assoc_typs = (*assoc_typs).clone();
                for assoc_typ in t.x.assoc_typs.iter() {
                    if !assoc_typs.contains(assoc_typ) {
                        assoc_typs.push(assoc_typ.clone());
                    }
                }
                let assoc_typs = Arc::new(assoc_typs);
                let mut typ_bounds = (*typ_bounds).clone();
                for b in t.x.typ_bounds.iter() {
                    if !typ_bounds.iter().any(|b2| generic_bounds_equal(b, b2)) {
                        typ_bounds.push(b.clone());
                    }
                }
                let typ_bounds = Arc::new(typ_bounds);
                let mut assoc_typs_bounds = (*assoc_typs_bounds).clone();
                for b in t.x.assoc_typs_bounds.iter() {
                    if !assoc_typs_bounds.iter().any(|b2| generic_bounds_equal(b, b2)) {
                        assoc_typs_bounds.push(b.clone());
                    }
                }
                let assoc_typs_bounds = Arc::new(assoc_typs_bounds);
                for m in t.x.methods.iter() {
                    if methods.iter().any(|m2| m == m2) {
                        return Err(trait_conflict_error(
                            prev,
                            t,
                            &format!(
                                "duplicate method {}",
                                crate::ast_util::fun_as_friendly_rust_name(m)
                            ),
                        ));
                    }
                }
                methods = Arc::new(methods.iter().chain(t.x.methods.iter()).cloned().collect());
                let prevx = TraitX {
                    name,
                    proxy,
                    visibility,
                    typ_params,
                    typ_bounds,
                    assoc_typs,
                    assoc_typs_bounds,
                    methods,
                };
                traits[*index] = prev.new_x(prevx);
            } else {
                prev_trait_index.insert(t.x.name.clone(), traits.len());
                traits.push(t.clone());
            }
        } else {
            traits.push(t.clone());
        }
    }

    // Also remove any duplicate auto-imported trait impls:
    let mut trait_impls: Vec<TraitImpl> = Vec::new();
    let mut trait_impl_set: HashSet<Path> = HashSet::new();
    for ti in &kratex.trait_impls {
        if ti.x.auto_imported && trait_impl_set.contains(&ti.x.impl_path) {
            continue;
        }
        trait_impls.push(ti.clone());
        trait_impl_set.insert(ti.x.impl_path.clone());
    }

    kratex.traits = traits;
    kratex.trait_impls = trait_impls;
    Ok(Arc::new(kratex))
}
