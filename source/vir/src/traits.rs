use crate::ast::{
    CallTarget, CallTargetKind, Expr, ExprX, Fun, Function, FunctionKind, GenericBounds, Krate,
    Mode, Path, SpannedTyped, TypX, Typs, VirErr, WellKnownItem,
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
    path_to_well_known_item: &std::collections::HashMap<Path, WellKnownItem>,
    krate: &Krate,
) -> Result<Krate, VirErr> {
    let traits: HashSet<Path> = krate.traits.iter().map(|t| t.x.name.clone()).collect();
    let func_map: HashMap<Fun, Function> =
        krate.functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();

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

        if let FunctionKind::TraitMethodImpl { method, trait_path, .. } = &function.x.kind {
            let our_trait = traits.contains(trait_path);
            let mut functionx = function.x.clone();
            if our_trait {
                let decl = &func_map[method];
                let mut retx = functionx.ret.x.clone();
                retx.name = decl.x.ret.x.name.clone();
                functionx.ret = Spanned::new(functionx.ret.span.clone(), retx);
            } else {
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

    // Axioms for bounds predicates (based on trait impls)
    for imp in krate.trait_impls.iter() {
        assert!(ctx.bound_traits.contains(&imp.x.trait_path));
        // forall typ_params. typ_bounds ==> tr_bound%T(...typ_args...)
        // Example:
        //   trait T1 {}
        //   trait T2<A> {}
        //   impl<A: T1> T2<Set<A>> for S<Seq<A>>
        // -->
        //   forall A. tr_bound%T1(A) ==> tr_bound%T2(S<Seq<A>>, Set<A>)
        let tr_bound = if let Some(tr_bound) =
            trait_bound_to_air(ctx, &imp.x.trait_path, &imp.x.trait_typ_args)
        {
            tr_bound
        } else {
            continue;
        };
        let name = format!(
            "{}_{}",
            path_as_friendly_rust_name(&imp.x.impl_path),
            crate::def::QID_TRAIT_IMPL
        );
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
        commands.push(Arc::new(CommandX::Global(axiom)));
    }

    Arc::new(commands)
}
