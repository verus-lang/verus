use crate::ast::{
    CallTarget, CallTargetKind, Expr, ExprX, Fun, Function, FunctionKind, FunctionX, GenericBounds,
    Ident, ImplPath, ImplPaths, Krate, Mode, Path, SpannedTyped, Trait, TraitImpl, Typ, TypX, Typs,
    VirErr, Visibility, WellKnownItem,
};
use crate::ast_util::path_as_friendly_rust_name;
use crate::ast_visitor::VisitorScopeMap;
use crate::context::Ctx;
use crate::def::Spanned;
use crate::messages::{error, Span};
use crate::sst_to_air::typ_to_ids;
use air::ast::{Command, CommandX, Commands, DeclX};
use air::ast_util::{ident_apply, mk_bind_expr, mk_implies, str_typ};
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// We currently do not support trait bounds for traits from other crates
// and we consider methods for traits from other crates to be static.
pub fn demote_foreign_traits(
    path_to_well_known_item: &HashMap<Path, WellKnownItem>,
    krate: &Krate,
) -> Result<Krate, VirErr> {
    let traits: HashSet<Path> = krate.traits.iter().map(|t| t.x.name.clone()).collect();

    let mut kratex = (**krate).clone();
    for function in &mut kratex.functions {
        /* TODO: this check was broken in earlier versions of this code, and fixing would break
         * some std_specs declarations (for bounds X: Allocator and X: Debug).
         * In the long run, we should probably reenable this check
         * and allow users to declare external traits in order to satisfy this check.
         * In the meantime, omitting this check doesn't cause any soundness issues.
        for bounds in function.x.typ_bounds.iter() {
            let GenericBoundX::Trait(trait_path, _) = &**bounds;
            let our_trait = traits.contains(trait_path);
           if !our_trait {
                return error(
                    &function.span,
                    format!(
                        "cannot use trait {} from another crate as a bound",
                        crate::ast_util::path_as_friendly_rust_name(trait_path)
                    ),
                );
            }
        }
        */

        if let FunctionKind::TraitMethodImpl { trait_path, .. } = &function.x.kind {
            let our_trait = traits.contains(trait_path);
            let mut functionx = function.x.clone();
            if !our_trait {
                if path_to_well_known_item.get(trait_path) == Some(&WellKnownItem::DropTrait) {
                    if !function.x.require.is_empty() {
                        return Err(error(
                            &function.span,
                            "requires are not allowed on the implementation for Drop",
                        ));
                    }
                    if !matches!(&function.x.mask_spec, crate::ast::MaskSpec::InvariantOpens(es) if es.len() == 0)
                    {
                        return Err(error(
                            &function.span,
                            "the implementation for Drop must be marked opens_invariants none",
                        ));
                    }
                }
                check_modes(function, &function.span)?;
                functionx.kind = FunctionKind::Static;
            }
            *function = Spanned::new(function.span.clone(), functionx);
        }

        if let FunctionKind::ForeignTraitMethodImpl(trait_path) = &function.x.kind {
            let our_trait = traits.contains(trait_path);
            let mut functionx = function.x.clone();
            if our_trait {
                return Err(error(
                    &function.x.proxy.as_ref().unwrap().span,
                    "external_fn_specification can only be used on trait functions when the trait itself is external",
                ));
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
            &|_state, _, expr| demote_one_expr(&traits, expr),
            &|_state, _, stmt| Ok(vec![stmt.clone()]),
            &|_state, typ| Ok(typ.clone()),
        )?;
    }

    Ok(Arc::new(kratex))
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
pub fn inherit_default_bodies(krate: &Krate) -> Krate {
    let mut kratex = (**krate).clone();

    let mut trait_map: HashMap<Path, &Trait> = HashMap::new();
    // map trait_path to all default methods in trait
    let mut default_methods: HashMap<Path, Vec<&Function>> = HashMap::new();
    // set of all impl methods (&impl_path, &trait_method_name)
    let mut method_impls: HashSet<(&Path, &Fun)> = HashSet::new();
    for tr in &krate.traits {
        assert!(!trait_map.contains_key(&tr.x.name));
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
                // - for spec functions, used by func_to_air to create a definition axiom
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
                    mask_spec: crate::ast::MaskSpec::NoSpec,
                    item_kind: default_function.x.item_kind,
                    publish: None,
                    attrs: Arc::new(crate::ast::FunctionAttrsX::default()),
                    body: None,
                    extra_dependencies: vec![],
                };
                kratex.functions.push(default_function.new_x(inherit_functionx));
            }
        }
    }

    Arc::new(kratex)
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

fn get_trait(fun: &Fun) -> Path {
    fun.path.pop_segment()
}

fn demote_one_expr(traits: &HashSet<Path>, expr: &Expr) -> Result<Expr, VirErr> {
    match &expr.x {
        ExprX::Call(
            CallTarget::Fun(
                CallTargetKind::Method(Some((resolved_fun, resolved_typs, impl_paths))),
                fun,
                _typs,
                _impl_paths,
                autospec_usage,
            ),
            args,
        ) if !traits.contains(&get_trait(fun)) => {
            let kind = CallTargetKind::Static;
            let ct = CallTarget::Fun(
                kind,
                resolved_fun.clone(),
                resolved_typs.clone(),
                impl_paths.clone(),
                *autospec_usage,
            );
            Ok(expr.new_x(ExprX::Call(ct, args.clone())))
        }
        _ => Ok(expr.clone()),
    }
}

pub(crate) fn trait_bounds_to_ast(ctx: &Ctx, span: &Span, typ_bounds: &GenericBounds) -> Vec<Expr> {
    let mut bound_exprs: Vec<Expr> = Vec::new();
    for bound in typ_bounds.iter() {
        let crate::ast::GenericBoundX::Trait(path, typ_args) = &**bound;
        if !ctx.trait_map.contains_key(path) || !ctx.bound_traits.contains(path) {
            continue;
        }
        let op = crate::ast::NullaryOpr::TraitBound(path.clone(), typ_args.clone());
        let exprx = ExprX::NullaryOpr(op);
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
        let crate::ast::GenericBoundX::Trait(path, typ_args) = &**bound;
        if !ctx.trait_map.contains_key(path) || !ctx.bound_traits.contains(path) {
            continue;
        }
        let op = crate::ast::NullaryOpr::TraitBound(path.clone(), typ_args.clone());
        let expx = crate::sst::ExpX::NullaryOpr(op);
        bound_exps.push(SpannedTyped::new(span, &Arc::new(TypX::Bool), expx));
    }
    bound_exps
}

pub(crate) fn trait_bound_to_air(
    ctx: &Ctx,
    path: &Path,
    typ_args: &Typs,
) -> Option<air::ast::Expr> {
    if !ctx.trait_map.contains_key(path) || !ctx.bound_traits.contains(path) {
        return None;
    }
    let mut typ_exprs: Vec<air::ast::Expr> = Vec::new();
    for t in typ_args.iter() {
        typ_exprs.extend(typ_to_ids(t));
    }
    Some(ident_apply(&crate::def::trait_bound(path), &typ_exprs))
}

pub(crate) fn trait_bounds_to_air(ctx: &Ctx, typ_bounds: &GenericBounds) -> Vec<air::ast::Expr> {
    let mut bound_exprs: Vec<air::ast::Expr> = Vec::new();
    for bound in typ_bounds.iter() {
        let crate::ast::GenericBoundX::Trait(path, typ_args) = &**bound;
        if let Some(bound) = trait_bound_to_air(ctx, path, typ_args) {
            bound_exprs.push(bound);
        }
    }
    bound_exprs
}

pub fn traits_to_air(ctx: &Ctx, krate: &Krate) -> Commands {
    // Axioms about broadcast_forall and spec functions need justification
    // for any trait bounds.
    let mut commands: Vec<Command> = Vec::new();

    // Declare predicates for bounds
    //   (declare-fun tr_bound%T (... Dcr Type ...) Bool)
    for tr in krate.traits.iter() {
        if ctx.bound_traits.contains(&tr.x.name) {
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
    }
    Arc::new(commands)
}

pub fn trait_impl_to_air(ctx: &Ctx, imp: &TraitImpl) -> Commands {
    // Axiom for bounds predicates (based on trait impls)
    assert!(ctx.bound_traits.contains(&imp.x.trait_path));
    // forall typ_params. typ_bounds ==> tr_bound%T(...typ_args...)
    // Example:
    //   trait T1 {}
    //   trait T2<A> {}
    //   impl<A: T1> T2<Set<A>> for S<Seq<A>>
    // -->
    //   forall A. tr_bound%T1(A) ==> tr_bound%T2(S<Seq<A>>, Set<A>)
    let tr_bound =
        if let Some(tr_bound) = trait_bound_to_air(ctx, &imp.x.trait_path, &imp.x.trait_typ_args) {
            tr_bound
        } else {
            return Arc::new(vec![]);
        };
    let name =
        format!("{}_{}", path_as_friendly_rust_name(&imp.x.impl_path), crate::def::QID_TRAIT_IMPL);
    let trigs = vec![tr_bound.clone()];
    let bind = crate::func_to_air::func_bind_trig(
        ctx,
        name,
        &imp.x.typ_params,
        &Arc::new(vec![]),
        &trigs,
        false,
    );
    let req_bounds = trait_bounds_to_air(ctx, &imp.x.typ_bounds);
    let imply = mk_implies(&air::ast_util::mk_and(&req_bounds), &tr_bound);
    let forall = mk_bind_expr(&bind, &imply);
    let axiom = Arc::new(DeclX::Axiom(forall));
    Arc::new(vec![Arc::new(CommandX::Global(axiom))])
}
