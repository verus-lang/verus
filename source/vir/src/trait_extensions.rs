//! Eliminate `external_trait_extension` traits before ast_simplify.
//!
//! For `#[verifier::external_trait_extension(TSpec via TSpecImpl)]` on a trait `T`,
//! the VIR crate contains:
//! - a trait `TSpec` (whose supertrait is `T`) declaring additional spec functions,
//! - impls of `TSpec` (written by the user as impls of `TSpecImpl`, or synthesized by
//!   `inherit_default_bodies`), each paired with an impl of `T` for the same type,
//! - a blanket impl `impl<A: T> TSpec for A` (marked `external_trait_blanket`).
//!
//! Since `TSpec` and `T` are equivalent (each implies the other),
//! everything after ast_simplify can treat them as a single trait.
//! This pass:
//! - merges `TSpec`'s methods into `T` and removes `TSpec`,
//! - merges each impl of `TSpec` into its paired impl of `T`
//!   (the impl's methods become methods of the paired impl of `T`) and removes the `TSpec` impl,
//! - removes the blanket impl,
//! - replaces all remaining references to `TSpec` with `T`
//!   and all references to impls of `TSpec` with the paired impls of `T`.
//!
//! Note: ast_simplify rebuilds the GlobalCtx (including the call graph) from the crate
//! produced by this pass, so the call graph must come out the same as the call graph
//! built by the earlier GlobalCtx::new, which merges TSpec into T on the fly
//! (see Node replace_with in GlobalCtx::new).
//! One subtlety is the special case in redirect_calls_in_default_methods for calls
//! within a single impl of TSpec (see preserve_intra_impl_calls).

use crate::ast::{
    AssocTypeImpl, AssocTypeImplX, CallTarget, CallTargetKind, Expr, ExprX, Fun, Function,
    FunctionKind, GenericBound, GenericBoundX, ImplPath, ImplPaths, Krate, KrateX, NullaryOpr,
    OpaqueTypeX, Path, Pattern, Place, Stmt, TraitId, TraitImpl, TraitImplX, TraitX, Typ, TypX,
    UnaryOpr, VirErr,
};
use crate::ast_visitor::{AstVisitor, NoScoper, Rewrite, VisitorScopeMap};
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

struct EliminateExtensions {
    /// Map TSpec to T
    extension_to_trait: HashMap<Path, Path>,
    /// Map each impl of TSpec to the paired impl of T
    impl_to_origin: HashMap<Path, Path>,
    /// Blanket impls impl<A: T> TSpec for A
    blanket_impls: HashSet<Path>,
}

impl EliminateExtensions {
    fn trait_path(&self, path: &Path) -> Path {
        self.extension_to_trait.get(path).unwrap_or(path).clone()
    }

    fn trait_id(&self, trait_id: &TraitId) -> TraitId {
        match trait_id {
            TraitId::Path(path) => TraitId::Path(self.trait_path(path)),
            TraitId::Sizedness(_) => trait_id.clone(),
        }
    }

    fn impl_path(&self, path: &Path) -> Path {
        assert!(!self.blanket_impls.contains(path));
        self.impl_to_origin.get(path).unwrap_or(path).clone()
    }

    fn impl_paths(&self, impl_paths: &ImplPaths) -> ImplPaths {
        let mut new_impl_paths: Vec<ImplPath> = Vec::new();
        for impl_path in impl_paths.iter() {
            let impl_path = match impl_path {
                ImplPath::TraitImplPath(path) if self.blanket_impls.contains(path) => continue,
                ImplPath::TraitImplPath(path) => ImplPath::TraitImplPath(self.impl_path(path)),
                ImplPath::FnDefImplPath(_) => impl_path.clone(),
            };
            if !new_impl_paths.contains(&impl_path) {
                new_impl_paths.push(impl_path);
            }
        }
        Arc::new(new_impl_paths)
    }
}

impl AstVisitor<Rewrite, VirErr, NoScoper> for EliminateExtensions {
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        let typ = self.visit_typ_rec(typ)?;
        let typ = match &*typ {
            TypX::Datatype(dt, typs, impl_paths) => {
                Arc::new(TypX::Datatype(dt.clone(), typs.clone(), self.impl_paths(impl_paths)))
            }
            TypX::Dyn(path, typs, impl_paths) => Arc::new(TypX::Dyn(
                self.trait_path(path),
                typs.clone(),
                self.impl_paths(impl_paths),
            )),
            TypX::Projection { trait_typ_args, trait_path, name } => Arc::new(TypX::Projection {
                trait_typ_args: trait_typ_args.clone(),
                trait_path: self.trait_path(trait_path),
                name: name.clone(),
            }),
            _ => typ,
        };
        Ok(typ)
    }

    fn visit_expr(&mut self, expr: &Expr) -> Result<Expr, VirErr> {
        self.visit_expr_rec(expr)
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<Vec<Stmt>, VirErr> {
        Ok(vec![self.visit_stmt_rec(stmt)?])
    }

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<Pattern, VirErr> {
        self.visit_pattern_rec(pattern)
    }

    fn visit_place(&mut self, place: &Place) -> Result<Place, VirErr> {
        self.visit_place_rec(place)
    }

    fn visit_call_target_kind(&mut self, kind: &CallTargetKind) -> Result<CallTargetKind, VirErr> {
        match kind {
            CallTargetKind::DynamicResolved { resolved, typs, impl_paths, is_trait_default } => {
                Ok(CallTargetKind::DynamicResolved {
                    resolved: resolved.clone(),
                    typs: Arc::new(self.visit_typs(typs)?),
                    impl_paths: self.impl_paths(impl_paths),
                    is_trait_default: *is_trait_default,
                })
            }
            CallTargetKind::Static
            | CallTargetKind::ProofFn(..)
            | CallTargetKind::Dynamic
            | CallTargetKind::ExternalTraitDefault => Ok(kind.clone()),
        }
    }

    fn visit_call_target(&mut self, call_target: &CallTarget) -> Result<CallTarget, VirErr> {
        match call_target {
            CallTarget::Fun(kind, fun, typs, impl_paths, attrs) => Ok(CallTarget::Fun(
                self.visit_call_target_kind(kind)?,
                fun.clone(),
                Arc::new(self.visit_typs(typs)?),
                self.impl_paths(impl_paths),
                attrs.clone(),
            )),
            CallTarget::FnSpec(expr) => Ok(CallTarget::FnSpec(self.visit_expr(expr)?)),
            CallTarget::BuiltinSpecFun(bsf, typs, impl_paths) => Ok(CallTarget::BuiltinSpecFun(
                bsf.clone(),
                Arc::new(self.visit_typs(typs)?),
                self.impl_paths(impl_paths),
            )),
            CallTarget::AssumeExternal => Ok(call_target.clone()),
        }
    }

    fn visit_nullary_opr(&mut self, nopr: &NullaryOpr) -> Result<NullaryOpr, VirErr> {
        match nopr {
            NullaryOpr::TraitBound(trait_id, typs) => Ok(NullaryOpr::TraitBound(
                self.trait_id(trait_id),
                Arc::new(self.visit_typs(typs)?),
            )),
            NullaryOpr::TypEqualityBound(path, typs, id, typ) => Ok(NullaryOpr::TypEqualityBound(
                self.trait_path(path),
                Arc::new(self.visit_typs(typs)?),
                id.clone(),
                self.visit_typ(typ)?,
            )),
            NullaryOpr::ConstGeneric(typ) => Ok(NullaryOpr::ConstGeneric(self.visit_typ(typ)?)),
            NullaryOpr::ConstTypBound(t1, t2) => {
                Ok(NullaryOpr::ConstTypBound(self.visit_typ(t1)?, self.visit_typ(t2)?))
            }
        }
    }

    fn visit_unary_opr(&mut self, uopr: &UnaryOpr) -> Result<UnaryOpr, VirErr> {
        match uopr {
            UnaryOpr::ToDyn(t, impl_paths) => {
                Ok(UnaryOpr::ToDyn(self.visit_typ(t)?, self.impl_paths(impl_paths)))
            }
            UnaryOpr::Box(t) => Ok(UnaryOpr::Box(self.visit_typ(t)?)),
            UnaryOpr::Unbox(t) => Ok(UnaryOpr::Unbox(self.visit_typ(t)?)),
            UnaryOpr::HasType(t) => Ok(UnaryOpr::HasType(self.visit_typ(t)?)),
            UnaryOpr::HasResolved(t) => Ok(UnaryOpr::HasResolved(self.visit_typ(t)?)),
            UnaryOpr::IsVariant { .. }
            | UnaryOpr::Field { .. }
            | UnaryOpr::IntegerTypeBound(..)
            | UnaryOpr::CustomErr(..)
            | UnaryOpr::AutoDecreases
            | UnaryOpr::AutoLoopEnsures
            | UnaryOpr::ProofNote(..)
            | UnaryOpr::LoopIsolationBoundary(_) => Ok(uopr.clone()),
        }
    }

    fn visit_generic_bound(&mut self, b: &GenericBound) -> Result<GenericBound, VirErr> {
        let b = match &**b {
            GenericBoundX::Trait(trait_id, typs) => {
                GenericBoundX::Trait(self.trait_id(trait_id), Arc::new(self.visit_typs(typs)?))
            }
            GenericBoundX::TypEquality(path, typs, id, typ) => GenericBoundX::TypEquality(
                self.trait_path(path),
                Arc::new(self.visit_typs(typs)?),
                id.clone(),
                self.visit_typ(typ)?,
            ),
            GenericBoundX::ConstTyp(t1, t2) => {
                GenericBoundX::ConstTyp(self.visit_typ(t1)?, self.visit_typ(t2)?)
            }
        };
        Ok(Arc::new(b))
    }

    fn visit_generic_bounds(
        &mut self,
        bs: &Vec<GenericBound>,
    ) -> Result<Vec<GenericBound>, VirErr> {
        // Replacing TSpec with T may create duplicate bounds (e.g. A: T and A: TSpec);
        // remove the duplicates
        let mut new_bs: Vec<GenericBound> = Vec::new();
        for b in bs.iter() {
            let b = self.visit_generic_bound(b)?;
            if !new_bs.iter().any(|b2| crate::ast_util::generic_bounds_equal(&b, b2)) {
                new_bs.push(b);
            }
        }
        Ok(new_bs)
    }

    fn visit_function_kind(&mut self, kind: &FunctionKind) -> Result<FunctionKind, VirErr> {
        match kind {
            FunctionKind::Static => Ok(kind.clone()),
            FunctionKind::TraitMethodDecl { trait_path, has_default } => {
                Ok(FunctionKind::TraitMethodDecl {
                    trait_path: self.trait_path(trait_path),
                    has_default: *has_default,
                })
            }
            FunctionKind::TraitMethodImpl {
                method,
                impl_path,
                trait_path,
                trait_typ_args,
                inherit_body_from,
            } => Ok(FunctionKind::TraitMethodImpl {
                method: method.clone(),
                impl_path: self.impl_path(impl_path),
                trait_path: self.trait_path(trait_path),
                trait_typ_args: Arc::new(self.visit_typs(trait_typ_args)?),
                inherit_body_from: inherit_body_from.clone(),
            }),
            FunctionKind::ForeignTraitMethodImpl {
                method,
                impl_path,
                trait_path,
                trait_typ_args,
            } => Ok(FunctionKind::ForeignTraitMethodImpl {
                method: method.clone(),
                impl_path: self.impl_path(impl_path),
                trait_path: self.trait_path(trait_path),
                trait_typ_args: Arc::new(self.visit_typs(trait_typ_args)?),
            }),
        }
    }

    fn visit_assoc_type_impl(&mut self, imp: &AssocTypeImpl) -> Result<AssocTypeImpl, VirErr> {
        let AssocTypeImplX {
            name,
            impl_path,
            typ_params,
            typ_bounds,
            trait_path,
            trait_typ_args,
            typ,
            impl_paths,
        } = &imp.x;
        Ok(imp.new_x(AssocTypeImplX {
            name: name.clone(),
            impl_path: self.impl_path(impl_path),
            typ_params: typ_params.clone(),
            typ_bounds: Arc::new(self.visit_generic_bounds(typ_bounds)?),
            trait_path: self.trait_path(trait_path),
            trait_typ_args: Arc::new(self.visit_typs(trait_typ_args)?),
            typ: self.visit_typ(typ)?,
            impl_paths: self.impl_paths(impl_paths),
        }))
    }

    fn visit_trait_impl(&mut self, imp: &TraitImpl) -> Result<TraitImpl, VirErr> {
        let TraitImplX {
            impl_path,
            typ_params,
            typ_bounds,
            trait_path,
            trait_typ_args,
            trait_typ_arg_impls,
            owning_module,
            auto_imported,
            external_trait_blanket,
            is_unsafe,
        } = &imp.x;
        assert!(!*external_trait_blanket);
        assert!(!self.impl_to_origin.contains_key(impl_path));
        assert!(!self.extension_to_trait.contains_key(trait_path));
        Ok(imp.new_x(TraitImplX {
            impl_path: impl_path.clone(),
            typ_params: typ_params.clone(),
            typ_bounds: Arc::new(self.visit_generic_bounds(typ_bounds)?),
            trait_path: trait_path.clone(),
            trait_typ_args: Arc::new(self.visit_typs(trait_typ_args)?),
            trait_typ_arg_impls: trait_typ_arg_impls.new_x(self.impl_paths(&trait_typ_arg_impls.x)),
            owning_module: owning_module.clone(),
            auto_imported: *auto_imported,
            external_trait_blanket: false,
            is_unsafe: *is_unsafe,
        }))
    }
}

/// Within an impl I of TSpec (paired with an impl O of T), rustc resolves calls to TSpec methods
/// to the blanket impl, which we treat as dynamic calls to the TSpec method declaration,
/// with impl_paths that include O.
/// Since I is merged with O, a call from I's method f to TSpec's method g would then
/// create a cycle f --> O --> f in the call graph.
/// redirect_calls_in_default_methods avoids this for calls within a single impl of TSpec
/// by redirecting the call to I's implementation of g and omitting O from the impl_paths.
/// Once I is merged into O, the call graph can no longer recognize these calls,
/// so we encode the redirection directly in the crate:
/// - omit O from the impl_paths of the call
/// - add I's implementation of g to f's extra_dependencies
fn preserve_intra_impl_calls(
    function: &Function,
    impl_to_origin: &HashMap<Path, Path>,
    decl_traits: &HashMap<Fun, Path>,
    trait_impl_map: &HashMap<(Fun, Path), Fun>,
) -> Result<Function, VirErr> {
    let FunctionKind::TraitMethodImpl {
        impl_path: caller_impl,
        trait_path: caller_trait,
        trait_typ_args: caller_trait_typ_args,
        inherit_body_from: None,
        ..
    } = &function.x.kind
    else {
        return Ok(function.clone());
    };
    let Some(origin_impl) = impl_to_origin.get(caller_impl) else {
        return Ok(function.clone());
    };
    let origin_impl = ImplPath::TraitImplPath(origin_impl.clone());
    let mut extra_dependencies: Vec<Fun> = function.x.extra_dependencies.clone();
    let fe = |extra_dependencies: &mut Vec<Fun>, _: &mut VisitorScopeMap, expr: &Expr| {
        let ExprX::Call {
            target: CallTarget::Fun(kind, callee, typs, impl_paths, attrs),
            args,
            post_args,
            body,
        } = &expr.x
        else {
            return Ok(expr.clone());
        };
        if matches!(kind, CallTargetKind::DynamicResolved { .. }) {
            return Ok(expr.clone());
        }
        // We handle only the case where the traits and trait args are the same
        if decl_traits.get(callee) != Some(caller_trait) {
            return Ok(expr.clone());
        }
        assert!(typs.len() >= caller_trait_typ_args.len());
        if !crate::ast_util::n_types_equal(
            &Arc::new(typs[..caller_trait_typ_args.len()].to_vec()),
            caller_trait_typ_args,
        ) {
            return Ok(expr.clone());
        }
        let Some(callee_impl) = trait_impl_map.get(&(callee.clone(), caller_impl.clone())) else {
            return Ok(expr.clone());
        };
        if !extra_dependencies.contains(callee_impl) {
            extra_dependencies.push(callee_impl.clone());
        }
        let impl_paths: ImplPaths =
            Arc::new(impl_paths.iter().filter(|p| **p != origin_impl).cloned().collect());
        let target =
            CallTarget::Fun(kind.clone(), callee.clone(), typs.clone(), impl_paths, attrs.clone());
        Ok(expr.new_x(ExprX::Call {
            target,
            args: args.clone(),
            post_args: post_args.clone(),
            body: body.clone(),
        }))
    };
    let mut map: VisitorScopeMap = ScopeMap::new();
    let function = crate::ast_visitor::map_function_visitor_env(
        function,
        &mut map,
        &mut extra_dependencies,
        &fe,
        &|_, _, stmt| Ok(vec![stmt.clone()]),
        &|_, typ| Ok(typ.clone()),
        &|_, _, place| Ok(place.clone()),
        &|_, _, pat| Ok(pat.clone()),
    )?;
    let mut functionx = function.x.clone();
    functionx.extra_dependencies = extra_dependencies;
    Ok(function.new_x(functionx))
}

pub fn eliminate_trait_extensions(krate: &Krate) -> Result<Krate, VirErr> {
    let mut extension_to_trait: HashMap<Path, Path> = HashMap::new();
    for t in krate.traits.iter() {
        if let Some((extension, _)) = &t.x.external_trait_extension {
            assert!(!extension_to_trait.contains_key(extension));
            extension_to_trait.insert(extension.clone(), t.x.name.clone());
        }
    }
    let has_blanket = krate.trait_impls.iter().any(|ti| ti.x.external_trait_blanket);
    if extension_to_trait.is_empty() && !has_blanket {
        return Ok(krate.clone());
    }

    // Pair each impl of TSpec with an impl of T
    let trait_impl_map: HashMap<Path, TraitImpl> =
        krate.trait_impls.iter().map(|ti| (ti.x.impl_path.clone(), ti.clone())).collect();
    let mut impl_to_origin: HashMap<Path, Path> = HashMap::new();
    let mut blanket_impls: HashSet<Path> = HashSet::new();
    for ti in krate.trait_impls.iter() {
        if ti.x.external_trait_blanket {
            blanket_impls.insert(ti.x.impl_path.clone());
        } else if let Some(t) = extension_to_trait.get(&ti.x.trait_path) {
            // (Any error here has already been reported by GlobalCtx::new)
            let origin = crate::traits::find_trait_impl_from_extension(ti, &trait_impl_map, t)?;
            impl_to_origin.insert(ti.x.impl_path.clone(), origin.x.impl_path.clone());
        }
    }

    // Merge each TSpec into T
    let extension_traits: HashMap<Path, &crate::ast::Trait> = krate
        .traits
        .iter()
        .filter(|t| extension_to_trait.contains_key(&t.x.name))
        .map(|t| (t.x.name.clone(), t))
        .collect();
    let mut traits = Vec::new();
    for t in krate.traits.iter() {
        if extension_to_trait.contains_key(&t.x.name) {
            continue;
        }
        if let Some((extension, _)) = &t.x.external_trait_extension {
            let mut tx: TraitX = t.x.clone();
            if let Some(ext) = extension_traits.get(extension) {
                let names = |tx: &TraitX| tx.typ_params.iter().map(|(x, _)| x.clone()).collect();
                let (t_names, ext_names): (Vec<_>, Vec<_>) = (names(&t.x), names(&ext.x));
                if t_names != ext_names {
                    return Err(crate::messages::internal_error(
                        &ext.span,
                        "external_trait_extension: mismatched type parameters",
                    ));
                }
                let mut methods = (*tx.methods).clone();
                methods.extend(ext.x.methods.iter().cloned());
                tx.methods = Arc::new(methods);
            }
            tx.external_trait_extension = None;
            traits.push(t.new_x(tx));
        } else {
            traits.push(t.clone());
        }
    }

    // Remove the impls of TSpec (they are merged into the impls of T)
    // and the blanket impls
    let trait_impls: Vec<TraitImpl> = krate
        .trait_impls
        .iter()
        .filter(|ti| {
            !blanket_impls.contains(&ti.x.impl_path)
                && !impl_to_origin.contains_key(&ti.x.impl_path)
        })
        .cloned()
        .collect();

    // Encode calls within a single impl of TSpec (see preserve_intra_impl_calls)
    let mut decl_traits: HashMap<Fun, Path> = HashMap::new();
    let mut method_impl_map: HashMap<(Fun, Path), Fun> = HashMap::new();
    for f in krate.functions.iter() {
        match &f.x.kind {
            FunctionKind::TraitMethodDecl { trait_path, .. } => {
                decl_traits.insert(f.x.name.clone(), trait_path.clone());
            }
            FunctionKind::TraitMethodImpl { method, impl_path, .. } => {
                method_impl_map.insert((method.clone(), impl_path.clone()), f.x.name.clone());
            }
            _ => {}
        }
    }
    let mut functions = Vec::new();
    for f in krate.functions.iter() {
        functions.push(preserve_intra_impl_calls(
            f,
            &impl_to_origin,
            &decl_traits,
            &method_impl_map,
        )?);
    }

    let mut kratex: KrateX = (**krate).clone();
    kratex.functions = functions;
    kratex.traits = traits;
    kratex.trait_impls = trait_impls;

    let mut visitor = EliminateExtensions { extension_to_trait, impl_to_origin, blanket_impls };
    let krate = visitor.visit_krate(&Arc::new(kratex))?;
    let mut kratex: KrateX = (*krate).clone();
    let mut opaque_types = Vec::new();
    for o in kratex.opaque_types.iter() {
        let OpaqueTypeX { def_fun, name, typ_params, typ_bounds } = &o.x;
        opaque_types.push(o.new_x(OpaqueTypeX {
            def_fun: def_fun.clone(),
            name: name.clone(),
            typ_params: Arc::new(visitor.visit_typs(typ_params)?),
            typ_bounds: Arc::new(visitor.visit_generic_bounds(typ_bounds)?),
        }));
    }
    kratex.opaque_types = opaque_types;
    Ok(Arc::new(kratex))
}
