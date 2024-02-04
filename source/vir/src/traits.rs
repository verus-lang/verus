use crate::ast::{
    CallTarget, CallTargetKind, Expr, ExprX, Fun, Function, FunctionKind, FunctionX, GenericBounds,
    Ident, Krate, Mode, Path, SpannedTyped, Trait, TraitImpl, Typ, TypX, Typs, VirErr, Visibility,
    WellKnownItem,
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
