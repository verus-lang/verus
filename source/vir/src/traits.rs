use crate::ast::{
    CallTarget, CallTargetKind, Expr, ExprX, Fun, Function, FunctionKind, FunctionX, GenericBound,
    GenericBoundX, GenericBounds, Ident, ImplPath, ImplPaths, Krate, Mode, Path, Place, Sizedness,
    SpannedTyped, Trait, TraitId, TraitImpl, TraitX, Typ, TypX, Typs, VirErr, Visibility,
    WellKnownItem,
};
use crate::ast_util::path_as_friendly_rust_name;
use crate::ast_visitor::VisitorScopeMap;
use crate::context::Ctx;
use crate::def::Spanned;
use crate::messages::{Span, ToAny, error, warning};
use crate::sst_to_air::typ_to_ids;
use air::ast::{Command, CommandX, Commands, DeclX};
use air::ast_util::{ident_apply, ident_var, mk_bind_expr, mk_implies, mk_unnamed_axiom, str_typ};
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn get_trait(fun: &Fun) -> Path {
    fun.path.pop_segment()
}

fn demote_one_expr(
    traits: &HashSet<Path>,
    internal_traits: &HashSet<Path>,
    extension_traits: &HashSet<Path>,
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
            post_args,
        ) if !traits.contains(&get_trait(fun)) || !funs.contains(fun) => {
            let ct = CallTarget::Fun(
                CallTargetKind::Static,
                resolved_fun.clone(),
                resolved_typs.clone(),
                impl_paths.clone(),
                *autospec_usage,
            );
            Ok(expr.new_x(ExprX::Call(ct, args.clone(), post_args.clone())))
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
            post_args,
        ) if traits.contains(&get_trait(fun))
            && !internal_traits.contains(&get_trait(fun))
            && funs.contains(fun)
            && !funs.contains(resolved_fun) =>
        {
            // Calls to external trait default functions are considered to be calls
            // to the trait declaration (since we have a spec for the declaration)
            let ct = CallTarget::Fun(
                CallTargetKind::ExternalTraitDefault,
                fun.clone(),
                typs.clone(),
                impl_paths.clone(),
                *autospec_usage,
            );
            Ok(expr.new_x(ExprX::Call(ct, args.clone(), post_args.clone())))
        }
        ExprX::Call(
            CallTarget::Fun(
                CallTargetKind::DynamicResolved {
                    resolved: resolved_fun,
                    typs: _,
                    impl_paths: _,
                    is_trait_default: _,
                },
                fun,
                typs,
                impl_paths,
                autospec_usage,
            ),
            args,
            post_args,
        ) if extension_traits.contains(&get_trait(fun)) => {
            assert!(traits.contains(&get_trait(fun)));
            assert!(funs.contains(fun));
            assert!(!funs.contains(resolved_fun));
            // Extension traits have just one impl (an external blanket impl);
            // calls to this are always dynamic
            let ct = CallTarget::Fun(
                CallTargetKind::Dynamic,
                fun.clone(),
                typs.clone(),
                impl_paths.clone(),
                *autospec_usage,
            );
            Ok(expr.new_x(ExprX::Call(ct, args.clone(), post_args.clone())))
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
    let mut extension_traits: HashSet<Path> = HashSet::new();
    for t in krate.traits.iter() {
        if let Some((extension, _)) = &t.x.external_trait_extension {
            extension_traits.insert(extension.clone());
        }
    }

    let mut kratex = (**krate).clone();
    for function in &mut kratex.functions {
        for bound in function.x.typ_bounds.iter() {
            let trait_path = match &**bound {
                GenericBoundX::Trait(TraitId::Path(path), _) => path,
                GenericBoundX::Trait(TraitId::Sizedness(_), _) => {
                    continue;
                }
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
                            path_as_friendly_rust_name(trait_path)
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
                    if !matches!(&function.x.mask_spec, Some(crate::ast::MaskSpec::InvariantOpens(_span, es)) if es.len() == 0)
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
            &|_state, _, expr| {
                demote_one_expr(&traits, &internal_traits, &extension_traits, &funs, expr)
            },
            &|_state, _, stmt| Ok(vec![stmt.clone()]),
            &|_state, typ| Ok(typ.clone()),
            &|_state, _, place| Ok(place.clone()),
        )?;
    }

    Ok(Arc::new(kratex))
}

fn rewrite_path(from_path: &Path, to_path: &Path, path: &Path) -> Path {
    if path.matches_prefix(from_path) {
        let suffix = path.segments[from_path.segments.len()..].to_vec();
        to_path.push_segments(suffix)
    } else {
        path.clone()
    }
}

pub fn rewrite_fun(from_path: &Path, to_path: &Path, fun: &Fun) -> Fun {
    let path = rewrite_path(from_path, to_path, &fun.path);
    Arc::new(crate::ast::FunX { path })
}

pub fn rewrite_one_external_typ(from_path: &Path, to_path: &Path, typ: &Typ) -> Typ {
    match &**typ {
        TypX::FnDef(fun, typs, None) if fun.path.matches_prefix(from_path) => {
            let fun = rewrite_fun(from_path, to_path, fun);
            Arc::new(TypX::FnDef(fun, typs.clone(), None))
        }
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

pub fn rewrite_one_external_expr(
    from_path: &Path,
    to_path: &Path,
    to_spec_path: &Option<Path>,
    expr: &Expr,
) -> Expr {
    match (&expr.x, to_spec_path) {
        (ExprX::ExecFnByName(fun), _) if fun.path.matches_prefix(from_path) => {
            let fun = rewrite_fun(from_path, to_path, fun);
            expr.new_x(ExprX::ExecFnByName(fun))
        }
        (
            ExprX::Call(CallTarget::Fun(kind, fun, typs, impl_paths, auto), args, post_args),
            Some(to_spec),
        ) => {
            let fun = rewrite_fun(from_path, to_spec, fun);
            let kind = match kind {
                CallTargetKind::Static
                | CallTargetKind::ProofFn(..)
                | CallTargetKind::Dynamic
                | CallTargetKind::ExternalTraitDefault => kind.clone(),
                CallTargetKind::DynamicResolved {
                    resolved,
                    typs,
                    impl_paths,
                    is_trait_default,
                } => CallTargetKind::DynamicResolved {
                    resolved: rewrite_fun(from_path, to_spec, resolved),
                    typs: typs.clone(),
                    impl_paths: impl_paths.clone(),
                    is_trait_default: *is_trait_default,
                },
            };
            expr.new_x(ExprX::Call(
                CallTarget::Fun(kind, fun, typs.clone(), impl_paths.clone(), *auto),
                args.clone(),
                post_args.clone(),
            ))
        }
        _ => expr.clone(),
    }
}

pub fn rewrite_external_bounds(
    from_path: &Path,
    to_path: &Path,
    bounds: &GenericBounds,
) -> GenericBounds {
    let mut bs: Vec<GenericBound> = Vec::new();
    for bound in bounds.iter() {
        let b = match &**bound {
            GenericBoundX::Trait(TraitId::Path(path), ts) if path == from_path => {
                Arc::new(GenericBoundX::Trait(TraitId::Path(to_path.clone()), ts.clone()))
            }
            GenericBoundX::TypEquality(path, ts, x, t) if path == from_path => Arc::new(
                GenericBoundX::TypEquality(to_path.clone(), ts.clone(), x.clone(), t.clone()),
            ),
            GenericBoundX::TypEquality(path, ts, x, t)
                if path == to_path
                    && (match &**t {
                        TypX::Projection { trait_typ_args, trait_path, name } => {
                            name == x
                                && crate::ast_util::n_types_equal(trait_typ_args, ts)
                                && trait_path == from_path
                        }
                        _ => false,
                    }) =>
            {
                // In order to aid Rust type checking of external trait specs,
                // allow external trait specs to match associated types with the real trait via:
                //   Self: T<X = <Self as ExT>::X>
                // which we ignore here
                continue;
            }
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
    to_spec_path: &Option<Path>,
    function: &Function,
) -> Function {
    let mut map: VisitorScopeMap = ScopeMap::new();
    crate::ast_visitor::map_function_visitor_env(
        function,
        &mut map,
        &mut (),
        &|_, _, e| Ok(rewrite_one_external_expr(from_path, to_path, to_spec_path, e)),
        &|_, _, stmt| Ok(vec![stmt.clone()]),
        &|_, t: &Typ| Ok(rewrite_one_external_typ(from_path, to_path, t)),
        &|_, _, p: &Place| Ok(p.clone()),
    )
    .expect("rewrite_external_function")
}

// For T<A1, ..., An>, remove the Self: T<A1, ..., An> bound introduced by rustc
pub fn remove_self_is_itself_bound(
    typ_bounds: &mut GenericBounds,
    trait_path: &Path,
    generics_params: &crate::ast::TypPositives,
) {
    Arc::make_mut(typ_bounds).retain(|gb| {
        match &**gb {
            GenericBoundX::Trait(TraitId::Path(bnd), tp) => {
                if bnd == trait_path {
                    let gp: Vec<_> = Some(crate::def::trait_self_type_param())
                        .into_iter()
                        .chain(generics_params.iter().map(|(p, _)| p.clone()))
                        .map(|p| Some(p))
                        .collect();
                    let tp: Vec<_> = tp
                        .iter()
                        .map(|p| match &**p {
                            TypX::TypParam(p) => Some(p.clone()),
                            _ => None,
                        })
                        .collect();
                    assert_eq!(*tp, *gp);
                    return false;
                }
            }
            GenericBoundX::Trait(TraitId::Sizedness(_), _tp) => {}
            GenericBoundX::TypEquality(..) => {}
            GenericBoundX::ConstTyp(..) => {}
        }
        true
    });
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
        if let FunctionKind::TraitMethodDecl { trait_path, has_default: true } = &f.x.kind {
            default_methods.get_mut(trait_path).expect("trait_path").push(f);
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
        if trait_impl.x.auto_imported {
            // skip external impls
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
                let n_outer = 1 + tr_params.len(); // Self + trait params
                for (x, t) in [crate::def::trait_self_type_param()]
                    .iter()
                    .chain(tr_params)
                    .zip(trait_impl.x.trait_typ_args.iter())
                {
                    assert!(!subst_map.contains_key(x));
                    subst_map.insert(x.clone(), t.clone());
                }
                // Note: Rust won't let tr_params conflict with f_typ_params.
                // However, trait_impl.x.typ_params could have the same names as f_typ_params.
                // So we have to rename f_typ_params.
                let rename_f_typ_param = |x: &Ident| -> Ident {
                    let s = format!("{}{}", crate::def::PREFIX_DEFAULT_TYP_PARAM, x);
                    Arc::new(s)
                };
                let f_typ_params: Vec<Ident> =
                    default_function.x.typ_params.iter().skip(n_outer).cloned().collect();
                for x in &f_typ_params {
                    let r = rename_f_typ_param(x);
                    subst_map.insert(x.clone(), Arc::new(TypX::TypParam(r)));
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
                let f_typ_params = f_typ_params.iter().map(rename_f_typ_param);
                let typ_params: Vec<Ident> =
                    trait_impl.x.typ_params.iter().cloned().chain(f_typ_params).collect();
                let mut f_typ_bounds = default_function.x.typ_bounds.clone();
                remove_self_is_itself_bound(
                    &mut f_typ_bounds,
                    &trait_impl.x.trait_path,
                    &tr.x.typ_params,
                );
                let f_typ_bounds =
                    crate::ast_visitor::map_generic_bounds_visitor(&f_typ_bounds, &mut (), &ft)
                        .expect("map_generic_bounds_visitor");
                let typ_bounds: Vec<GenericBound> =
                    trait_impl.x.typ_bounds.iter().chain(f_typ_bounds.iter()).cloned().collect();
                let inherit_functionx = FunctionX {
                    name,
                    proxy: None,
                    kind: inherit_kind,
                    // TODO: we could try to use the impl visibility and owning module for better pruning:
                    visibility,
                    body_visibility: default_function.x.body_visibility.clone(),
                    opaqueness: default_function.x.opaqueness.clone(),
                    owning_module: trait_impl.x.owning_module.clone(),
                    mode: default_function.x.mode,
                    typ_params: Arc::new(typ_params),
                    typ_bounds: Arc::new(typ_bounds),
                    params,
                    ret,
                    ens_has_return: default_function.x.ens_has_return,
                    require: Arc::new(vec![]),
                    ensure: (Arc::new(vec![]), Arc::new(vec![])),
                    returns: None,
                    decrease: Arc::new(vec![]),
                    decrease_when: None,
                    decrease_by: None,
                    fndef_axioms: None,
                    mask_spec: None,
                    unwind_spec: None,
                    item_kind: default_function.x.item_kind,
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
                    let impl_paths =
                        Arc::new(impl_paths.iter().filter(|p| filter(*p)).cloned().collect());

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
            GenericBoundX::Trait(trait_id, typ_args) => {
                let skip = match trait_id {
                    TraitId::Path(path) => !ctx.trait_map.contains_key(path),
                    TraitId::Sizedness(Sizedness::Sized) => false,
                    // we currently MetaSized and PointeeSized as equivalent (both representing
                    // size that's not known at compile time), so we don't emit a Sized bound
                    TraitId::Sizedness(_) => true,
                };
                if skip {
                    continue;
                }
                let op = crate::ast::NullaryOpr::TraitBound(trait_id.clone(), typ_args.clone());
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

pub(crate) fn trait_bound_to_air(
    ctx: &Ctx,
    trait_id: &TraitId,
    typ_args: &Typs,
) -> Option<air::ast::Expr> {
    if let TraitId::Path(path) = trait_id {
        if !ctx.trait_map.contains_key(path) {
            return None;
        }
    }
    let mut typ_exprs: Vec<air::ast::Expr> = Vec::new();
    for t in typ_args.iter() {
        typ_exprs.extend(typ_to_ids(ctx, t));
    }
    match trait_id {
        TraitId::Path(path) => Some(ident_apply(&crate::def::trait_bound(path), &typ_exprs)),
        // We treat both MetaSized and PointeeSized as unsized in AIR for now.
        // This may have to become more precise at some point in the future, but
        // collapsing the two should be sound since they don't lead to different
        // verification obligations.
        TraitId::Sizedness(Sizedness::MetaSized | Sizedness::PointeeSized) => None,
        TraitId::Sizedness(Sizedness::Sized) => {
            // sized bound only takes decorate param
            let typ_exprs = Arc::new(typ_exprs[0..1].to_vec());
            Some(ident_apply(&crate::def::sized_bound(), &typ_exprs))
        }
    }
}

pub(crate) fn typ_equality_bound_to_air(
    ctx: &Ctx,
    trait_path: &Path,
    typ_args: &Typs,
    name: &Ident,
    typ: &Typ,
) -> air::ast::Expr {
    let mut typ_exprs: Vec<air::ast::Expr> = Vec::new();
    for t in typ_args.iter() {
        typ_exprs.extend(typ_to_ids(ctx, t));
    }
    let ids = typ_to_ids(ctx, typ);
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
    let f = crate::ast_util::const_generic_to_primitive(t);
    let expr = air::ast_util::str_apply(f, &vec![crate::sst_to_air::typ_to_id(ctx, c)]);
    match crate::sst_to_air::typ_invariant(ctx, t, &expr) {
        Some(inv) => inv,
        _ => air::ast_util::mk_true(),
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

pub fn trait_decls_to_air(ctx: &Ctx, krate: &crate::sst::KrateSst) -> Commands {
    // Axioms about broadcast_forall and spec functions need justification
    // for any trait bounds.
    let mut commands: Vec<Command> = Vec::new();

    // Declare predicates for bounds
    //   (declare-fun tr_bound%T (... Dcr Type ...) Bool)
    // Also declare type id and to_dyn
    //   (declare-fun DYN%T (... Dcr Type ...) Type)
    //   (declare-fun to_dyn%T (... Dcr Type ... Poly) Poly)
    for tr in krate.traits.iter() {
        let mut tparams: Vec<air::ast::Typ> = Vec::new();
        let mut iparams: Vec<air::ast::Typ> = Vec::new();
        let mut dparams: Vec<air::ast::Typ> = Vec::new();
        tparams.extend(crate::def::types().iter().map(|s| str_typ(s))); // Self
        dparams.extend(crate::def::types().iter().map(|s| str_typ(s))); // Self
        for _ in tr.x.typ_params.iter() {
            tparams.extend(crate::def::types().iter().map(|s| str_typ(s)));
            iparams.extend(crate::def::types().iter().map(|s| str_typ(s)));
            dparams.extend(crate::def::types().iter().map(|s| str_typ(s)));
        }
        dparams.push(str_typ(crate::def::POLY));

        let decl_trait_bound = Arc::new(DeclX::Fun(
            crate::def::trait_bound(&tr.x.name),
            Arc::new(tparams),
            air::ast_util::bool_typ(),
        ));
        commands.push(Arc::new(CommandX::Global(decl_trait_bound)));

        if ctx.reached_dyn_traits.contains(&tr.x.name) {
            let decl_trait_id = Arc::new(DeclX::fun_or_const(
                crate::def::prefix_dyn_id(&tr.x.name),
                Arc::new(iparams),
                str_typ(crate::def::TYPE),
            ));
            let decl_to_dyn = Arc::new(DeclX::fun_or_const(
                crate::def::to_dyn(&tr.x.name),
                Arc::new(dparams),
                str_typ(crate::def::POLY),
            ));
            commands.push(Arc::new(CommandX::Global(decl_trait_id)));
            commands.push(Arc::new(CommandX::Global(decl_to_dyn)));
        }
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
        if let Some(tr_bound) =
            trait_bound_to_air(ctx, &TraitId::Path(tr.x.name.clone()), &Arc::new(typ_args))
        {
            let all_bounds =
                tr.x.typ_bounds.iter().chain(tr.x.assoc_typs_bounds.iter()).cloned().collect();
            let typ_bounds = trait_bounds_to_air(ctx, &Arc::new(all_bounds));
            let qname = format!(
                "{}_{}",
                path_as_friendly_rust_name(&tr.x.name),
                crate::def::QID_TRAIT_TYPE_BOUNDS
            );
            let trigs = vec![tr_bound.clone()];
            let bind = crate::sst_to_air_func::func_bind_trig(
                ctx,
                qname,
                &Arc::new(typ_params),
                &Arc::new(vec![]),
                &trigs,
                None,
            );
            let imply = air::ast_util::mk_implies(&tr_bound, &air::ast_util::mk_and(&typ_bounds));
            let forall = mk_bind_expr(&bind, &imply);
            let axiom = Arc::new(DeclX::Axiom(air::ast::Axiom { named: None, expr: forall }));
            commands.push(Arc::new(CommandX::Global(axiom)));
        }
    }
    Arc::new(commands)
}

pub(crate) fn dyn_spec_fn_axiom(
    ctx: &Ctx,
    decl_commands: &mut Vec<Command>,
    trait_path: &Path,
    function: &crate::sst::FunctionSst,
) {
    // For spec functions, connect dyn T blanket impl to a specific impl of T:
    //   trait T<A1..Am> { spec fn f(self, x1..xk) }
    //   impl<B1..Bn> T<t1..tm> for t0
    // ==>
    //   (axiom (forall (B1..Bn (self! Poly) x1..xk) (!
    //      (=
    //       (T.f.? $dyn (DYN%T. t1..tm) t1..tm (to_dyn%T t0 t1..tm self!) x1..xk)
    //       (T.f.? $          t0        t1..tm                     self!  x1..xk)
    //      )
    //   )))
    // function.x.pars = self, x1...xk
    // function.x.typ_params = B1..Bn
    // trait_typ_args = t0 t1..tm
    // Note: we don't need anything for exec/proof functions,
    // because dyn T just uses T's requires/ensures.
    use crate::ast_util::LowerUniqueVar;
    let FunctionKind::TraitMethodImpl { method, trait_typ_args, .. } = &function.x.kind else {
        panic!("dyn_spec_fn_axiom expects TraitMethodImpl");
    };
    let mut typ_ids: Vec<air::ast::Expr> = Vec::new();
    let mut lhs_args: Vec<air::ast::Expr> = Vec::new();
    let mut rhs_args: Vec<air::ast::Expr> = Vec::new();
    for (n, targ) in trait_typ_args.iter().enumerate() {
        rhs_args.extend(typ_to_ids(ctx, targ));
        typ_ids.extend(typ_to_ids(ctx, targ));
        if n == 0 {
            let typ_args_no_self = Arc::new(trait_typ_args.iter().skip(1).cloned().collect());
            let dyn_typ =
                Arc::new(TypX::Dyn(trait_path.clone(), typ_args_no_self, Arc::new(vec![])));
            lhs_args.extend(typ_to_ids(ctx, &dyn_typ));
        } else {
            lhs_args.extend(typ_to_ids(ctx, targ));
        }
    }
    for (n, param) in function.x.pars.iter().enumerate() {
        rhs_args.push(ident_var(&param.x.name.lower()));
        if n == 0 {
            let mut to_dyn_args = typ_ids.clone();
            to_dyn_args.push(ident_var(&param.x.name.lower()));
            lhs_args.push(ident_apply(&crate::def::to_dyn(trait_path), &to_dyn_args));
        } else {
            lhs_args.push(ident_var(&param.x.name.lower()));
        }
    }
    let name = crate::def::suffix_global_id(&crate::sst_to_air::fun_to_air_ident(&method));
    let lhs = ident_apply(&name, &Arc::new(lhs_args));
    let rhs = ident_apply(&name, &Arc::new(rhs_args));
    let f_eq = Arc::new(air::ast::ExprX::Binary(air::ast::BinaryOp::Eq, lhs.clone(), rhs));
    let qid = format!("{name}_to_dyn");
    let e_forall = mk_bind_expr(
        &crate::sst_to_air_func::func_bind(
            ctx,
            qid,
            &function.x.typ_params,
            &function.x.pars,
            &lhs,
            None,
        ),
        &f_eq,
    );
    let def_axiom = mk_unnamed_axiom(e_forall);
    decl_commands.push(Arc::new(CommandX::Global(def_axiom)));
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
    use crate::ast_visitor::{AstVisitor, NoScoper, Rewrite};
    struct ProjVisitor {
        holes: Vec<(Ident, Typ)>,
    }
    impl AstVisitor<Rewrite, (), NoScoper> for ProjVisitor {
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
    let (typ_params, eqs) =
        crate::sst_to_air_func::hide_projections_air(ctx, &imp.x.typ_params, holes);
    let tr_bound =
        match trait_bound_to_air(ctx, &TraitId::Path(imp.x.trait_path.clone()), &trait_typ_args) {
            Some(tr_bound) => tr_bound,
            _ => {
                return Arc::new(vec![]);
            }
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
        None,
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
                    is_unsafe,
                    dyn_compatible,
                    external_trait_extension,
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
                    is_unsafe,
                    dyn_compatible: dyn_compatible.clone(),
                    external_trait_extension,
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

pub(crate) fn find_trait_impl_from_extension(
    extension: &TraitImpl,
    candidates: Vec<TraitImpl>,
    origin_trait_path: &Path,
) -> Result<TraitImpl, VirErr> {
    for candidate in candidates.iter() {
        if candidate.x.typ_params == extension.x.typ_params
            && crate::ast_util::n_types_equal(
                &candidate.x.trait_typ_args,
                &extension.x.trait_typ_args,
            )
        {
            return Ok(candidate.clone());
        }
    }
    let mut err = error(
        &extension.span,
        format!(
            "impl for {} must have a matching impl for {}, with the same type parameter names and trait arguments",
            path_as_friendly_rust_name(&extension.x.trait_path),
            path_as_friendly_rust_name(&origin_trait_path),
        ),
    );
    for candidate in candidates.iter() {
        err = err.secondary_span(&candidate.span)
    }
    return Err(err);
}

/// For trait method impls, the 'ens_has_return' should be inherited from the method decl
pub fn fixup_ens_has_return_for_trait_method_impls(krate: Krate) -> Result<Krate, VirErr> {
    let mut krate = krate;
    let kratex = &mut Arc::make_mut(&mut krate);
    let mut fun_map = HashMap::<Fun, Function>::new();
    for function in kratex.functions.iter() {
        if matches!(function.x.kind, FunctionKind::TraitMethodDecl { .. }) {
            fun_map.insert(function.x.name.clone(), function.clone());
        }
    }
    for function in kratex.functions.iter_mut() {
        if let FunctionKind::TraitMethodImpl { method, .. } = &function.x.kind {
            let method = method.clone();
            if !function.x.ens_has_return {
                match fun_map.get(&method) {
                    None => {}
                    Some(f) if f.x.ens_has_return => {
                        let functionx = &mut Arc::make_mut(&mut *function).x;
                        functionx.ens_has_return = true;
                    }
                    Some(_) => {}
                }
            }
            if function.x.returns.is_some() {
                match fun_map.get(&method) {
                    None => {}
                    Some(f) if f.x.returns.is_some() => {
                        return Err(error(
                            &function.span,
                            "a `returns` clause cannot be declared on both a trait method impl and its declaration",
                        ).secondary_span(&f.span));
                    }
                    Some(_) => {}
                }
            }
        }
    }
    Ok(krate)
}

// Is an impl of the form impl<A: ?Sized + ...> T<...> for A
fn is_unsized_blanket_impl(ti: &TraitImpl) -> bool {
    // trait_typ_args[0] is the Self argument
    if let TypX::TypParam(slf) = &*ti.x.trait_typ_args[0] {
        // Self type is just a TypParam, so we have a blanket impl
        for bound in ti.x.typ_bounds.iter() {
            if let GenericBoundX::Trait(TraitId::Sizedness(Sizedness::Sized), targs) = &**bound {
                if targs.len() == 1 {
                    if let TypX::TypParam(p) = &*targs[0] {
                        if p == slf {
                            // we do have a Sized bound; we're not unsized
                            return false;
                        }
                    }
                }
            }
        }
        // If we don't have a Sized bound on slf, we consider it unsized
        true
    } else {
        false
    }
}

// TODO: delete this when https://github.com/rust-lang/rust/issues/57893 is fixed
pub fn get_dyn_traits(krate: &Krate) -> HashSet<Path> {
    use crate::ast_visitor::{AstVisitor, WalkTypVisitorEnv};
    let mut dyn_traits: HashSet<Path> = HashSet::new();
    let ft = &|dyn_traits: &mut HashSet<Path>, typ: &Typ| {
        if let TypX::Dyn(trait_path, _, _) = &**typ {
            dyn_traits.insert(trait_path.clone());
        }
        Ok(())
    };
    let mut visitor = WalkTypVisitorEnv { env: &mut dyn_traits, ft };
    visitor.visit_krate(krate).unwrap();
    dyn_traits
}

// This extends the trait dyn compatibility rules from
// https://doc.rust-lang.org/reference/items/traits.html .
// See https://github.com/verus-lang/verus/discussions/1047 .
fn compute_dyn_compatibility(
    tr_map: &HashMap<Path, Trait>,
    unsized_blanketed_traits: &HashSet<Path>,
    fun_map: &HashMap<Fun, Function>,
    dyn_map: &mut HashMap<Path, Arc<crate::ast::DynCompatible>>,
    tr_path: &Path,
) -> Arc<crate::ast::DynCompatible> {
    use crate::ast::DynCompatible;
    if !tr_map.contains_key(tr_path) {
        panic!("compute_dyn_compatibility: missing trait {:?}", tr_path);
    }
    let tr = &tr_map[tr_path];
    let mut unsized_blanket_super = None;
    for bound in tr.x.typ_bounds.iter() {
        if let GenericBoundX::Trait(TraitId::Path(super_tr), targs) = &**bound {
            if targs.len() >= 1 {
                if let TypX::TypParam(p) = &*targs[0] {
                    if *p == crate::def::trait_self_type_param() {
                        let d = get_dyn_compatibility(
                            tr_map,
                            unsized_blanketed_traits,
                            fun_map,
                            dyn_map,
                            super_tr,
                        );
                        match &*d {
                            DynCompatible::Accept => {}
                            DynCompatible::Reject { reason } => {
                                let reason = format!(
                                    "supertrait {} is not verus-dyn-compatible: {}",
                                    path_as_friendly_rust_name(super_tr),
                                    reason,
                                );
                                return Arc::new(DynCompatible::Reject { reason });
                            }
                            DynCompatible::RejectUnsizedBlanketImpl { .. } => {
                                unsized_blanket_super = Some(d.clone());
                            }
                        }
                    }
                }
            }
        }
    }
    'method: for fun in tr.x.methods.iter() {
        if !fun_map.contains_key(fun) {
            panic!("compute_dyn_compatibility: missing function {:?}", fun);
        }
        let f = &fun_map[fun];
        for bound in f.x.typ_bounds.iter() {
            if let GenericBoundX::Trait(TraitId::Sizedness(Sizedness::Sized), targs) = &**bound {
                if targs.len() == 1 {
                    if let TypX::TypParam(p) = &*targs[0] {
                        if *p == crate::def::trait_self_type_param() {
                            // Self: Sized means an explicitly non-dispatchable function
                            // that can't be called through dyn (because dyn isn't Sized).
                            // So this function has no dyn requirements.
                            continue 'method;
                        }
                    }
                }
            }
        }
        // If we reach here, f must be dispatchable to allow dyn
        // Key property: "self" must be tracked or exec to allow ensures
        // (a "spec" self can be forged, which would would allow unfounded ensures)
        let f_name = path_as_friendly_rust_name(&fun.path);
        if f.x.mode == Mode::Spec {
            // No ensures clauses allowed for spec functions
            if f.x.ensure.0.len() + f.x.ensure.1.len() > 0 {
                let reason = format!("spec fn {f_name} cannot have ensures");
                return Arc::new(DynCompatible::Reject { reason });
            }
        } else {
            if f.x.params.len() == 0 {
                // Rust should already check that there is a self parameter
                let reason = format!("internal Verus error: {f_name} has no self parameter");
                return Arc::new(DynCompatible::Reject { reason });
            }
            let self_param = &f.x.params[0];
            if self_param.x.mode != f.x.mode {
                // self argument must have a mode equal to the function mode
                let m = if f.x.mode == Mode::Exec { "exec" } else { "tracked" };
                let reason = format!("self parameter of function {f_name} must be {m}");
                return Arc::new(DynCompatible::Reject { reason });
            }
        }
    }
    if let Some(d) = unsized_blanket_super {
        d
    } else if unsized_blanketed_traits.contains(tr_path) {
        Arc::new(DynCompatible::RejectUnsizedBlanketImpl { trait_path: tr_path.clone() })
    } else {
        Arc::new(DynCompatible::Accept)
    }
}

fn get_dyn_compatibility(
    tr_map: &HashMap<Path, Trait>,
    unsized_blanketed_traits: &HashSet<Path>,
    fun_map: &HashMap<Fun, Function>,
    dyn_map: &mut HashMap<Path, Arc<crate::ast::DynCompatible>>,
    tr_path: &Path,
) -> Arc<crate::ast::DynCompatible> {
    if dyn_map.contains_key(tr_path) {
        return dyn_map[tr_path].clone();
    } else {
        let d =
            compute_dyn_compatibility(tr_map, unsized_blanketed_traits, fun_map, dyn_map, tr_path);
        assert!(!dyn_map.contains_key(tr_path));
        dyn_map.insert(tr_path.clone(), d.clone());
        d
    }
}

pub fn set_krate_dyn_compatibility(imported: &Vec<Krate>, krate: &mut crate::ast::KrateX) {
    let mut tr_map: HashMap<Path, Trait> = HashMap::new();
    for tr in &krate.traits {
        tr_map.insert(tr.x.name.clone(), tr.clone());
    }
    let mut fun_map: HashMap<Fun, Function> = HashMap::new();
    for f in &krate.functions {
        fun_map.insert(f.x.name.clone(), f.clone());
    }
    let mut unsized_blanketed_traits: HashSet<Path> = HashSet::new();
    for ti in &krate.trait_impls {
        if is_unsized_blanket_impl(ti) {
            unsized_blanketed_traits.insert(ti.x.trait_path.clone());
        }
    }
    let mut dyn_map: HashMap<Path, Arc<crate::ast::DynCompatible>> = HashMap::new();
    for k in imported {
        for tr in &k.traits {
            let d = tr.x.dyn_compatible.as_ref().expect("imported dyn_compatible").clone();
            dyn_map.insert(tr.x.name.clone(), d);
        }
    }
    for tr in &mut krate.traits {
        assert!(tr.x.dyn_compatible.is_none());
        let d = get_dyn_compatibility(
            &tr_map,
            &unsized_blanketed_traits,
            &fun_map,
            &mut dyn_map,
            &tr.x.name,
        );
        Arc::make_mut(tr).x.dyn_compatible = Some(d);
    }
}
