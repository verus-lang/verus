use crate::ast::{
    BodyVisibility, CallTarget, CallTargetKind, Constant, Datatype, DatatypeTransparency, Dt, Expr,
    ExprX, FieldOpr, Fun, Function, FunctionKind, Krate, MaskSpec, Mode, MultiOp, Opaqueness, Path,
    Pattern, PatternX, Place, PlaceX, Stmt, StmtX, Trait, Typ, TypX, UnaryOp, UnaryOpr, UnwindSpec,
    VarIdent, VirErr, VirErrAs, Visibility,
};
use crate::ast_util::{
    dt_as_friendly_rust_name, fun_as_friendly_rust_name, is_body_visible_to, is_visible_to_opt,
    path_as_friendly_rust_name, referenced_vars_expr, typ_to_diagnostic_str, types_equal,
    undecorate_typ,
};
use crate::def::user_local_name;
use crate::early_exit_cf::assert_no_early_exit_in_inv_block;
use crate::internal_err;
use crate::messages::{Message, Span, error, error_with_label};
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

struct Ctxt<'a> {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) reveal_groups: HashSet<Fun>,
    pub(crate) dts: HashMap<Path, Datatype>,
    pub(crate) traits: HashMap<Path, Trait>,
    pub(crate) krate: &'a Krate,
    unpruned_krate: &'a Krate,
    no_cheating: bool,
}

trait EmitError {
    fn emit(&mut self, path: Option<Path>, err: VirErrAs);
    fn has_fatal_errors(&self) -> bool;
}

struct EmitErrorState {
    diags: Vec<VirErrAs>,
    diag_map: HashMap<Path, usize>,
}

impl EmitError for EmitErrorState {
    fn emit(&mut self, path: Option<Path>, err: VirErrAs) {
        match path {
            Some(path) => match self.diag_map.get(&path) {
                Some(msg_idx) => self.diags[*msg_idx] = self.diags[*msg_idx].merge(&err),
                None => {
                    self.diag_map.insert(path, self.diags.len());
                    self.diags.push(err);
                }
            },
            None => self.diags.push(err),
        };
    }

    fn has_fatal_errors(&self) -> bool {
        self.diags.iter().any(|err| match err {
            VirErrAs::NonBlockingError(..) => true,
            _ => false,
        })
    }
}

#[warn(unused_must_use)]
fn check_one_typ<Emit: EmitError>(
    ctxt: &Ctxt,
    typ: &Typ,
    span: &crate::messages::Span,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    match &**typ {
        TypX::Datatype(Dt::Path(path), _, _) => {
            let _ = check_path_and_get_datatype(ctxt, path, span, emit)?;
            Ok(())
        }
        TypX::Dyn(path, _, _) => {
            if let Some(tr) = ctxt.traits.get(path) {
                use crate::ast::DynCompatible;
                match &**tr.x.dyn_compatible.as_ref().expect("dyn_compatible should be Some") {
                    DynCompatible::Accept => Ok(()),
                    DynCompatible::Reject { reason } => {
                        let msg = format!("Trait is not Verus dyn-compatible: {}", reason);
                        Err(error(span, msg))
                    }
                    DynCompatible::RejectUnsizedBlanketImpl { trait_path } => {
                        let name = path_as_friendly_rust_name(trait_path);
                        let msg = format!(
                            "Verus disallows dyn for trait {} because it has an unsized blanket impl (see https://github.com/rust-lang/rust/issues/57893 )",
                            name,
                        );
                        Err(error(span, msg))
                    }
                }
            } else {
                Err(error(
                    span,
                    &format!("trait {} not declared to Verus", path_as_friendly_rust_name(path)),
                ))
            }
        }
        TypX::FnDef(fun, _typs, opt_res_fun) => {
            check_function_access(ctxt, fun, None, span, emit)?;
            if let Some(res_fun) = opt_res_fun {
                check_function_access(ctxt, res_fun, None, span, emit)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

#[warn(unused_must_use)]
fn check_typ<Emit: EmitError>(
    ctxt: &Ctxt,
    typ: &Arc<TypX>,
    span: &crate::messages::Span,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    crate::ast_visitor::typ_visitor_check(typ, &mut |t| check_one_typ(ctxt, t, span, emit))
}

// Returns:
// - Ok(Ok(d)) on success
// - Ok(Err(())) to indicate that an error was reported via "emit",
//   but that the caller can proceed with additional checks to try to find additional errors
// - Err(...) to indicate that the caller should abort entirely
#[warn(unused_must_use)]
fn check_path_and_get_datatype<'a, Emit: EmitError>(
    ctxt: &'a Ctxt,
    path: &Path,
    span: &crate::messages::Span,
    emit: &mut Emit,
) -> Result<Result<Datatype, ()>, VirErr> {
    fn is_proxy<'a>(ctxt: &'a Ctxt, path: &Path) -> Option<&'a Dt> {
        for dt in &ctxt.unpruned_krate.datatypes {
            match &dt.x.proxy {
                Some(proxy) => {
                    if &proxy.x == path {
                        return Some(&dt.x.name);
                    }
                }
                None => {}
            }
        }
        return None;
    }

    fn is_known_external<'a>(ctxt: &'a Ctxt, path: &Path) -> bool {
        ctxt.krate.external_types.contains(path)
    }

    match ctxt.dts.get(path) {
        Some(dt) => Ok(Ok(dt.clone())),
        None => {
            if let Some(actual_path) = is_proxy(ctxt, path) {
                return Err(error(
                    span,
                    &format!(
                        "cannot use type `{:}` marked `external_type_specification` directly; use `{:}` instead",
                        path_as_friendly_rust_name(path),
                        dt_as_friendly_rust_name(actual_path),
                    ),
                ));
            } else {
                let path_string = path_as_friendly_rust_name(path);
                let msg = if is_known_external(ctxt, path) {
                    format!(
                        "cannot use type `{path_string:}` which is ignored because it is either declared outside the verus! macro or it is marked as `external`.",
                    )
                } else {
                    format!(
                        "`{path_string:}` is not supported (note: you may be able to add a Verus specification to this type with the `external_type_specification` attribute){:}",
                        if path.is_rust_std_path() {
                            " (note: the vstd library provides some specification for the Rust std library, but it is currently limited)"
                        } else {
                            ""
                        },
                    )
                };
                let err: VirErrAs =
                    VirErrAs::NonBlockingError(error(span, msg), Some(path.clone()));
                emit.emit(Some(path.clone()), err);

                Ok(Err(()))
            }
        }
    }
}

// Returns:
// - Ok(Ok(f)) on success
// - Ok(Err(())) to indicate that an error was reported via "emit",
//   but that the caller can proceed with additional checks to try to find additional errors
// - Err(...) to indicate that the caller should abort entirely
fn check_path_and_get_function<'a, Emit: EmitError>(
    ctxt: &'a Ctxt,
    x: &Fun,
    disallow_private_access: Option<(&Visibility, &str)>,
    span: &crate::messages::Span,
    emit: &mut Emit,
) -> Result<Result<Function, ()>, VirErr> {
    fn is_proxy<'a>(ctxt: &'a Ctxt, path: &Path) -> Option<&'a Path> {
        // Linear scan, but this only happens if this uncommon error message triggers
        for function in &ctxt.unpruned_krate.functions {
            match &function.x.proxy {
                Some(proxy) => {
                    if &proxy.x == path {
                        return Some(&function.x.name.path);
                    }
                }
                None => {}
            }
        }
        return None;
    }

    let f = match ctxt.funs.get(x) {
        Some(f) => Ok(f.clone()),
        None => {
            if let Some(actual_path) = is_proxy(ctxt, &x.path) {
                return Err(error(
                    span,
                    &format!(
                        "cannot call function `{:}` which is an artificial function for `assume_specification`; call `{:}` instead",
                        path_as_friendly_rust_name(&x.path),
                        path_as_friendly_rust_name(actual_path),
                    ),
                ));
            } else {
                let locally_defined = match ctxt.krate.external_fns.iter().find(|info| *info == x) {
                    Some(_) => true,
                    _ => false,
                };
                let path_string = path_as_friendly_rust_name(&x.path);
                let err_str = if locally_defined {
                    format!(
                        "cannot use function `{:}` which is ignored because it is either declared outside the verus! macro or it is marked as `external`.",
                        path_string
                    )
                } else {
                    format!(
                        "`{path_string:}` is not supported (note: you may be able to add a Verus specification to this function with `assume_specification`){:}",
                        if x.path.is_rust_std_path() {
                            " (note: the vstd library provides some specification for the Rust std library, but it is currently limited)"
                        } else {
                            ""
                        },
                    )
                };
                emit.emit(
                    Some(x.path.clone()),
                    VirErrAs::NonBlockingError(error(span, &err_str), Some(x.path.clone())),
                );
                Err(())
            }
        }
    };

    if let (Some((required_vis, reason)), Ok(f)) = (disallow_private_access, &f) {
        if !required_vis.at_least_as_restrictive_as(&f.x.visibility) {
            let kind = f.x.item_kind.to_string();
            let msg = format!("in {reason:}, cannot refer to private {kind:}");
            return Err(error(&span, msg));
        }
    }

    Ok(f)
}

fn check_datatype_access<Emit: EmitError>(
    ctxt: &Ctxt,
    path: &Path,
    disallow_private_access: Option<(&Visibility, &str)>,
    my_module: &Option<Path>,
    span: &Span,
    access_type: &str,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    let dt = check_path_and_get_datatype(ctxt, path, span, emit)?;
    let Ok(dt) = dt else {
        // Found an error resolving dt; skip this and proceed to find more errors
        assert!(emit.has_fatal_errors());
        return Ok(());
    };
    match &dt.x.transparency {
        DatatypeTransparency::Never => {
            // This can only happen if the datatype is 'external_body'
            return Err(error_with_label(
                span,
                format!("disallowed: {:} for an opaque datatype", access_type),
                format!("this {:} is disallowed", access_type),
            )
            .secondary_label(
                &dt.span,
                "Verus treats this datatype as 'opaque' because it is marked 'external_body'",
            ));
        }
        DatatypeTransparency::WhenVisible(vis) => {
            let required_vis = if let Some((required_vis, _reason)) = disallow_private_access {
                required_vis.clone()
            } else {
                if my_module.is_none() {
                    return Ok(());
                }
                Visibility { restricted_to: my_module.clone() }
            };

            // Is the datatype *name* visible throughout the entire required area?
            if !required_vis.at_least_as_restrictive_as(&dt.x.visibility) {
                let visibility_module = dt.x.visibility.restricted_to.clone().unwrap();
                let mut er = error_with_label(
                    span,
                    format!("disallowed: {:} for a non-visible datatype", access_type),
                    format!("this {:} is disallowed because of non-visibility", access_type),
                )
                .secondary_label(
                    &dt.span,
                    format!(
                        "this datatype is only visible to `{:}`",
                        path_as_friendly_rust_name(&visibility_module)
                    ),
                );

                if let Some((_required_vis, reason)) = disallow_private_access {
                    let required_vis_str = match &required_vis.restricted_to {
                        None => "everywhere".to_string(),
                        Some(module) if module.segments.len() == 0 => format!(
                            "everywhere in the crate `{:}`",
                            path_as_friendly_rust_name(module)
                        ),
                        Some(module) => format!(
                            "everywhere in the module `{:}`",
                            path_as_friendly_rust_name(module)
                        ),
                    };
                    er = er.help(
                        format!("note that because this is a {:}, this {:} must be well-formed {:}, which is wider than `{:}`",
                            reason,
                            access_type,
                            required_vis_str,
                            path_as_friendly_rust_name(&visibility_module),
                        )
                    );
                }

                return Err(er);
            }

            // Is the datatype *transparent* throughout the entire required area?
            // (i.e., is the datatype body visible?)
            if !required_vis.at_least_as_restrictive_as(vis) {
                let transp_module = vis.restricted_to.clone().unwrap();
                let mut er = error_with_label(
                    span,
                    format!("disallowed: {:} for an opaque datatype", access_type),
                    format!("this {:} is disallowed because of datatype opaqueness", access_type),
                ).secondary_label(
                    &dt.span,
                    format!("Verus treats this datatype as 'opaque' outside `{:}` (note that Verus always considers the most restrictive field for determining this)",
                            path_as_friendly_rust_name(&transp_module))
                );

                if let Some((_required_vis, reason)) = disallow_private_access {
                    let required_vis_str = match &required_vis.restricted_to {
                        None => "everywhere".to_string(),
                        Some(module) if module.segments.len() == 0 => format!(
                            "everywhere in the crate `{:}`",
                            path_as_friendly_rust_name(module)
                        ),
                        Some(module) => format!(
                            "everywhere in the module `{:}`",
                            path_as_friendly_rust_name(module)
                        ),
                    };
                    er = er.help(
                        format!("note that because this is a {:}, this {:} must be well-formed {:}, which is wider than `{:}`",
                            reason,
                            access_type,
                            required_vis_str,
                            path_as_friendly_rust_name(&transp_module),
                        )
                    );
                }

                return Err(er);
            }
        }
    }

    Ok(())
}

fn check_function_access<'a, Emit: EmitError>(
    ctxt: &'a Ctxt,
    x: &Fun,
    disallow_private_access: Option<(&Visibility, &str)>,
    span: &crate::messages::Span,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    let _ = check_path_and_get_function(ctxt, x, disallow_private_access, span, emit)?;
    Ok(())
}

fn check_one_expr<Emit: EmitError>(
    ctxt: &Ctxt,
    function: &Function,
    expr: &Expr,
    disallow_private_access: Option<(&Visibility, &str)>,
    area: Area,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    match &expr.x {
        ExprX::Var(x) => {
            check_var(function, &expr.span, area, x)?;
        }
        ExprX::ConstVar(x, _) => {
            check_function_access(ctxt, x, disallow_private_access, &expr.span, emit)?;
        }
        ExprX::Call(CallTarget::Fun(kind, x, _, _, _), args, _post_args) => {
            let f =
                check_path_and_get_function(ctxt, x, disallow_private_access, &expr.span, emit)?;
            let Ok(f) = f else {
                // Found an error resolving f; skip this and proceed to find more errors
                assert!(emit.has_fatal_errors());
                return Ok(());
            };
            match kind {
                CallTargetKind::Static => {}
                CallTargetKind::ProofFn(..) => {}
                CallTargetKind::Dynamic => {}
                CallTargetKind::DynamicResolved { resolved: resolved_fun, .. } => {
                    check_function_access(
                        ctxt,
                        resolved_fun,
                        disallow_private_access,
                        &expr.span,
                        emit,
                    )?;
                }
                CallTargetKind::ExternalTraitDefault => {}
            }
            if f.x.attrs.is_decrease_by {
                // a decreases_by function isn't a real function;
                // it's just a container for proof code that goes in the corresponding spec function
                return Err(error(
                    &expr.span,
                    "cannot call a decreases_by/recommends_by function directly",
                ));
            }
            if f.x.attrs.broadcast_forall && f.x.params.len() == 0 {
                // REVIEW: this is a rather arbitrary restriction due to ast_simplify's treatment of 0-argument functions.
                // When we generalize broadcast_forall, this restriction should be removed.
                return Err(error(
                    &expr.span,
                    "cannot call a broadcast_forall function with 0 arguments directly",
                ));
            }
            for (_param, arg) in f.x.params.iter().zip(args.iter()).filter(|(p, _)| p.x.is_mut) {
                fn is_ok(e: &Expr) -> bool {
                    match &e.x {
                        ExprX::VarLoc(_) => true,
                        ExprX::Unary(UnaryOp::CoerceMode { .. }, e1) => is_ok(e1),
                        ExprX::UnaryOpr(UnaryOpr::Field { .. }, base) => is_ok(base),
                        ExprX::Block(stmts, Some(e1)) if stmts.len() == 0 => is_ok(e1),
                        ExprX::Ghost { alloc_wrapper: false, tracked: true, expr: e1 } => is_ok(e1),
                        _ => false,
                    }
                }
                let arg_x = match &arg.x {
                    // Tracked(&mut x) and Ghost(&mut x) arguments appear as
                    // Expr::Ghost { ... Expr::Loc ... }
                    ExprX::Ghost { alloc_wrapper: true, tracked: _, expr: e } => &e.x,
                    e => e,
                };
                let is_ok = match &arg_x {
                    ExprX::Loc(l) => is_ok(l),
                    _ => false,
                };
                if !is_ok {
                    return Err(error(
                        &arg.span,
                        "complex arguments to &mut parameters are currently unsupported",
                    ));
                }
            }
        }
        ExprX::Ctor(Dt::Path(path), _variant, _fields, _update) => {
            check_datatype_access(
                ctxt,
                path,
                disallow_private_access,
                &function.x.owning_module,
                &expr.span,
                "constructor",
                emit,
            )?;
        }
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), e) => {
            if !crate::ast_util::type_is_bool(&e.typ) {
                return Err(error(
                    &expr.span,
                    "`custom_err` attribute only makes sense for bool expressions",
                ));
            }
        }
        ExprX::UnaryOpr(
            UnaryOpr::Field(FieldOpr {
                datatype: Dt::Path(path),
                variant: _,
                field: _,
                get_variant: _,
                check: _,
            }),
            _,
        ) => {
            check_datatype_access(
                ctxt,
                path,
                disallow_private_access,
                &function.x.owning_module,
                &expr.span,
                "field expression",
                emit,
            )?;
        }
        ExprX::Multi(MultiOp::Chained(ops), _) => {
            if ops.len() < 1 {
                return Err(error(
                    &expr.span,
                    "chained inequalities must have at least one inequality",
                ));
            }
        }
        ExprX::OpenInvariant(_inv, _binder, body, _atomicity) => {
            assert_no_early_exit_in_inv_block(&body.span, body)?;
        }
        ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
            if function.x.attrs.nonlinear {
                return Err(error(
                    &expr.span,
                    "assert_by_query not allowed in #[verifier::nonlinear] functions",
                ));
            }

            let mut referenced = HashSet::new();
            for r in requires.iter() {
                referenced.extend(referenced_vars_expr(r).into_iter());
            }
            for r in ensures.iter() {
                referenced.extend(referenced_vars_expr(r).into_iter());
            }

            crate::ast_visitor::ast_visitor_check_with_scope_map(
                proof,
                &mut crate::ast_visitor::VisitorScopeMap::new(),
                &mut (),
                &mut |_, scope_map, e| match &e.x {
                    ExprX::Var(x) | ExprX::VarLoc(x)
                        if !scope_map.contains_key(&x) && !referenced.contains(x) =>
                    {
                        Err(error(
                            &e.span,
                            format!("variable {} not mentioned in requires/ensures", x).as_str(),
                        ))
                    }
                    _ => Ok(()),
                },
                &mut |_, _, _| Ok(()),
                &mut |_, _, _| Ok(()),
                &mut |_, _, _, _| Ok(()),
                &mut |_, scope_map, p| match &p.x {
                    PlaceX::Local(x) if !scope_map.contains_key(&x) && !referenced.contains(x) => {
                        Err(error(
                            &p.span,
                            format!("variable {} not mentioned in requires/ensures", x).as_str(),
                        ))
                    }
                    _ => Ok(()),
                },
            )?;
        }
        ExprX::AssertAssume { is_assume, .. } => {
            if ctxt.no_cheating && *is_assume {
                return Err(error(&expr.span, "assume/admit not allowed with --no-cheating"));
            }
        }
        ExprX::AssertBy { ensure, vars, .. } => match &ensure.x {
            ExprX::Binary(crate::ast::BinaryOp::Implies, _, _) => {
                if !vars.is_empty() {
                    emit.emit(None, VirErrAs::Warning(
                        error(&expr.span, "using ==> in `assert forall` does not currently assume the antecedent in the body; consider using `implies` instead of `==>`")
                            .help("If you didn't mean to assume the antecedent, we're very curious to hear why! To tell us, please open an issue on the Verus issue tracker on github with the title `Don't always make assert forall assume the antecedent`. If no one opens such an issue, we'll soon change the behavior of Verus to always assume the antecedent of the outermost implication")
                    ));
                }
            }
            _ => {}
        },
        ExprX::NonSpecClosure { params: _, ret: _, proof_fn_modes, .. } => {
            crate::closures::check_closure_well_formed(expr, proof_fn_modes.is_some())?;
        }
        ExprX::Fuel(f, fuel, is_broadcast_use) => {
            if ctxt.reveal_groups.contains(f) && *fuel == 1 {
                return Ok(());
            }
            let f = check_path_and_get_function(ctxt, f, None, &expr.span, emit)?;
            let Ok(f) = f else {
                // Found an error resolving f; skip this and proceed to find more errors
                assert!(emit.has_fatal_errors());
                return Ok(());
            };
            if *is_broadcast_use {
                if !f.x.attrs.broadcast_forall {
                    return Err(error(
                        &expr.span,
                        &format!("`broadcast use` statements require a broadcast proof fn",),
                    ));
                }
            } else {
                if f.x.mode != Mode::Spec {
                    return Err(error(
                        &expr.span,
                        &format!(
                            "reveal/fuel statements require a spec-mode function, got {:}-mode function",
                            f.x.mode
                        ),
                    ));
                }
                if *fuel > 1 && (f.x.mode != Mode::Spec || f.x.decrease.is_empty()) {
                    return Err(error(
                        &expr.span,
                        "reveal_with_fuel statements require a spec function with a decreases clause",
                    ));
                }
                if let Some(my_module) = &function.x.owning_module {
                    if !is_body_visible_to(&f.x.body_visibility, my_module) {
                        return Err(error(
                            &expr.span,
                            format!(
                                "reveal/fuel statement is not allowed here because the function `{:}` is marked 'closed' and thus its body is not visible here. (Note: 'reveal' statements are intended for functions that are opaque, not functions that are closed)",
                                path_as_friendly_rust_name(&f.x.name.path),
                            ),
                        ));
                    }
                }
            }
        }
        ExprX::ExecFnByName(fun) => {
            let func =
                check_path_and_get_function(ctxt, fun, disallow_private_access, &expr.span, emit)?;
            let Ok(func) = func else {
                // Found an error resolving f; skip this and proceed to find more errors
                assert!(emit.has_fatal_errors());
                return Ok(());
            };
            for param in func.x.params.iter() {
                if param.x.is_mut {
                    return Err(error(
                        &expr.span,
                        "not supported: using a function that takes '&mut' params as a value",
                    ));
                }
            }
        }
        ExprX::ProofInSpec(_) => {
            // At the moment, spec termination checking is the only place set up to handle
            // proofs properly.
            // Recommendation checks could also handle proof blocks in the future,
            // but they are not ready yet since ast_to_sst doesn't generate,
            // for example, assertions for "assert" for recommends.
            // (see https://github.com/verus-lang/verus/issues/692 )
            match (area, function.x.mode, function.x.decrease.len()) {
                (Area::Body, Mode::Spec, dec) if dec > 0 => {}
                _ => {
                    return Err(error(
                        &expr.span,
                        "proof blocks inside spec code is currently supported only for spec functions with decreases",
                    ));
                }
            }
        }
        ExprX::Header(header) => {
            return Err(error(
                &expr.span,
                format!(
                    "This kind of statement should go at the {:}",
                    header.location_for_diagnostic()
                ),
            ));
        }
        ExprX::Unary(UnaryOp::MutRefFinal, _) => {
            return Err(error(
                &expr.span,
                "The result of `fin` must be dereferenced (e.g., `*fin(x)`)",
            ));
        }
        ExprX::Match(_place, arms) => {
            for arm in arms.iter() {
                // Error if the arm contains more than 1 of these 3 nontrivial features:
                let has_guard = !matches!(&arm.x.guard.x, ExprX::Const(Constant::Bool(true)));
                let has_or = crate::patterns::pattern_has_or(&arm.x.pattern);
                let has_ref_mut_binding = crate::patterns::pattern_find_mut_binding(&arm.x.pattern);

                if has_guard && has_or {
                    // This is nontrivial because we might need to evaluate the guard condition more than once
                    return Err(error(
                        &arm.x.pattern.span,
                        "Not supported: pattern containing both an or-pattern (|) and an if-guard",
                    ));
                }
                if let Some(span) = has_ref_mut_binding {
                    if has_or {
                        // This probably isn't that bad
                        return Err(error(
                            &span,
                            "Not supported: pattern containing both an or-pattern (|) and a binding by mutable reference",
                        ));
                    }
                    if has_guard {
                        // This is complicated because we need to create a mutable borrow to evaluate
                        // the test condition, but the mutable borrow is immutable until it ends
                        return Err(error(
                            &span,
                            "Not supported: pattern containing both an if-guard and a binding by mutable reference",
                        ));
                    }
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn check_one_stmt(_ctxt: &Ctxt, stmt: &Stmt) -> Result<(), VirErr> {
    match &stmt.x {
        StmtX::Decl { pattern, .. } => {
            let has_ref_mut_binding = crate::patterns::pattern_find_mut_binding(&pattern);
            if let Some(span) = has_ref_mut_binding {
                let has_or = crate::patterns::pattern_has_or(&pattern);
                if has_or {
                    return Err(error(
                        &span,
                        "Not supported: pattern containing both an or-pattern (|) and a binding by mutable reference",
                    ));
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn check_one_place<Emit: EmitError>(
    ctxt: &Ctxt,
    function: &Function,
    place: &Place,
    disallow_private_access: Option<(&Visibility, &str)>,
    area: Area,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    match &place.x {
        PlaceX::Local(x) => {
            check_var(function, &place.span, area, x)?;
        }
        PlaceX::Field(
            FieldOpr { datatype: Dt::Path(path), variant: _, field: _, get_variant: _, check: _ },
            _,
        ) => {
            check_datatype_access(
                ctxt,
                path,
                disallow_private_access,
                &function.x.owning_module,
                &place.span,
                "field expression",
                emit,
            )?;
        }
        _ => {}
    }
    Ok(())
}

fn check_var(function: &Function, span: &Span, area: Area, x: &VarIdent) -> Result<(), VirErr> {
    if let Area::PreState(clause_name) = area {
        for param in function.x.params.iter().filter(|p| p.x.is_mut) {
            if *x == param.x.name {
                return Err(error(
                    span,
                    format!(
                        "in {}, use `old({})` to refer to the pre-state of an &mut variable",
                        clause_name,
                        crate::def::user_local_name(&param.x.name)
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn check_one_pattern<Emit: EmitError>(
    ctxt: &Ctxt,
    function: &Function,
    pattern: &Pattern,
    disallow_private_access: Option<(&Visibility, &str)>,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    match &pattern.x {
        PatternX::Constructor(Dt::Path(path), _id, _binders) => {
            check_datatype_access(
                ctxt,
                path,
                disallow_private_access,
                &function.x.owning_module,
                &pattern.span,
                "pattern constructor",
                emit,
            )?;
            Ok(())
        }
        _ => Ok(()),
    }
}

#[derive(Clone, Copy)]
enum Area {
    PreState(&'static str),
    PostState,
    Body,
}

fn check_expr<Emit: EmitError>(
    ctxt: &Ctxt,
    function: &Function,
    expr: &Expr,
    disallow_private_access: Option<(&Visibility, &str)>,
    area: Area,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    let check_result = crate::ast_visitor::ast_visitor_check(
        expr,
        emit,
        &mut |emit, _scope_map, expr: &Arc<crate::ast::SpannedTyped<ExprX>>| {
            check_one_expr(ctxt, function, expr, disallow_private_access, area, emit)
        },
        &mut |_emit, _scope_map, stmt| check_one_stmt(ctxt, stmt),
        &mut |emit, _scope_map, pattern: &Arc<crate::ast::SpannedTyped<PatternX>>| {
            check_one_pattern(ctxt, function, pattern, disallow_private_access, emit)
        },
        &mut |emit, _scope_map, typ, span| check_one_typ(ctxt, typ, span, emit),
        &mut |emit, _scope_map, place| {
            check_one_place(ctxt, function, place, disallow_private_access, area, emit)
        },
    );

    check_result
}

fn check_function<Emit: EmitError>(
    ctxt: &Ctxt,
    function: &Function,
    emit: &mut Emit,
    _no_verify: bool,
) -> Result<(), VirErr> {
    if let FunctionKind::TraitMethodImpl { method, .. } = &function.x.kind {
        if function.x.require.len() > 0 {
            return Err(error(
                &function.span,
                "trait method implementation cannot declare requires clauses; these can only be inherited from the trait declaration",
            ));
        }
        if function.x.mask_spec.is_some() {
            return Err(error(
                &function.span,
                "trait method implementation cannot declare an opens_invariants spec; this can only be inherited from the trait declaration",
            ));
        }
        if function.x.unwind_spec.is_some() {
            return Err(error(
                &function.span,
                "trait method implementation cannot declare an unwind specification; this can only be inherited from the trait declaration",
            ));
        }

        let orig_decl = ctxt.funs.get(method).ok_or_else(|| {
            error(&function.span, "implementing a trait method that doesn't exist")
        })?;

        if matches!(orig_decl.x.body_visibility, BodyVisibility::Uninterpreted) {
            return Err(error(
                &function.span,
                "trait method implementation cannot be marked as `uninterp`",
            )
            .secondary_span(&orig_decl.span));
        }
    } else {
    }
    if let FunctionKind::TraitMethodDecl { has_default: false, .. } = &function.x.kind {
        if function.x.attrs.exec_allows_no_decreases_clause {
            return Err(error(
                &function.span,
                "trait method declaration cannot declare exec_allows_no_decreases_clause",
            ));
        }
    }

    if function.x.attrs.is_decrease_by {
        match function.x.kind {
            FunctionKind::Static => {}
            FunctionKind::TraitMethodDecl { .. }
            | FunctionKind::TraitMethodImpl { .. }
            | FunctionKind::ForeignTraitMethodImpl { .. } => {
                return Err(error(
                    &function.span,
                    "decreases_by/recommends_by function cannot be a trait method",
                ));
            }
        }
        if function.x.mode != Mode::Proof {
            return Err(error(
                &function.span,
                "decreases_by/recommends_by function must have mode proof",
            ));
        }

        if function.x.mode != Mode::Exec && matches!(*function.x.ret.x.typ, TypX::Opaque { .. }) {
            return Err(error(
                &function.x.ret.span,
                format!("Opaque type is not supported in {} mode", function.x.mode),
            ));
        }

        if function.x.decrease.len() != 0 {
            return Err(error(
                &function.span,
                "decreases_by/recommends_by function cannot have its own decreases clause",
            ));
        }
        if function.x.require.len() != 0 {
            return Err(error(
                &function.span,
                "decreases_by/recommends_by function cannot have requires clauses (use decreases_when in the spec function instead)",
            ));
        }
        if function.x.ensure.0.len() + function.x.ensure.1.len() != 0 {
            return Err(error(
                &function.span,
                "decreases_by/recommends_by function cannot have ensures clauses",
            ));
        }
        if function.x.returns.is_some() {
            return Err(error(
                &function.span,
                "decreases_by/recommends_by function cannot have ensures clauses",
            ));
        }
        if function.x.ens_has_return {
            return Err(error(
                &function.span,
                "decreases_by/recommends_by function cannot have a return value",
            ));
        }
    }

    if function.x.decrease_by.is_some() {
        if function.x.mode != Mode::Spec {
            return Err(error(
                &function.span,
                "only spec functions can use decreases_by/recommends_by",
            ));
        }
    }

    let ret_name = user_local_name(&function.x.ret.x.name);
    for p in function.x.params.iter() {
        check_typ(ctxt, &p.x.typ, &p.span, emit)?;
        if user_local_name(&p.x.name) == ret_name {
            return Err(error(
                &p.span,
                "parameter name cannot be the same as the return value name",
            ));
        }
    }
    check_typ(ctxt, &function.x.ret.x.typ, &function.x.ret.span, emit)?;

    if function.x.attrs.inline {
        if function.x.mode != Mode::Spec {
            return Err(error(&function.span, "'inline' is only allowed for 'spec' functions"));
        }
        // make sure we don't leak private bodies by inlining
        if BodyVisibility::Visibility(function.x.visibility.clone()) != function.x.body_visibility {
            // TODO error message could be improved
            return Err(error(
                &function.span,
                "'inline' is only allowed for private or 'open spec' functions",
            ));
        }
        if function.x.decrease.len() != 0 {
            return Err(error(&function.span, "'inline' functions cannot be recursive"));
        }
        if function.x.body.is_none() {
            return Err(error(&function.span, "'inline' functions must have a body"));
        }
    }

    if function.x.attrs.atomic {
        if function.x.mode != Mode::Exec {
            return Err(error(&function.span, "'atomic' only makes sense on an 'exec' function"));
        }
        match function.x.kind {
            FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. } => {
                return Err(error(&function.span, "'atomic' not supported for trait functions"));
            }
            FunctionKind::Static | FunctionKind::ForeignTraitMethodImpl { .. } => {
                // ok
            }
        }
    }
    if function.x.mask_spec.is_some() && function.x.mode == Mode::Spec {
        return Err(error(&function.span, "invariants cannot be opened in spec functions"));
    }
    if function.x.unwind_spec.is_some() && function.x.mode != Mode::Exec {
        return Err(error(
            &function.span,
            "an 'unwind' specification can only be given on exec functions",
        ));
    }
    if function.x.attrs.broadcast_forall {
        if function.x.mode != Mode::Proof {
            return Err(error(&function.span, "broadcast function must be declared as proof"));
        }
        if function.x.ens_has_return {
            return Err(error(&function.span, "broadcast function cannot have return type"));
        }
        for param in function.x.params.iter() {
            if param.x.mode != Mode::Spec {
                return Err(error(&function.span, "broadcast function must have spec parameters"));
            }
            if param.x.is_mut {
                return Err(error(
                    &function.span,
                    "broadcast function cannot have &mut parameters",
                ));
            }
        }
    }

    if (function.x.attrs.bit_vector
        && (function.x.attrs.nonlinear || function.x.attrs.integer_ring))
        || (!function.x.attrs.bit_vector
            && function.x.attrs.nonlinear
            && function.x.attrs.integer_ring)
    {
        return Err(error(
            &function.span,
            "Select at most one verifier attribute: integer_ring, non_linear, bit_vector",
        ));
    }

    if function.x.attrs.bit_vector {
        if function.x.mode != Mode::Proof {
            return Err(error(
                &function.span,
                "bit-vector function mode must be declared as proof",
            ));
        }
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |_scope_map, expr| {
                match &expr.x {
                    ExprX::Block(_, _) => {}
                    _ => {
                        return Err(error(
                            &function.span,
                            "bit-vector function mode cannot have a body",
                        ));
                    }
                }
                Ok(())
            })?;
        }
        for p in function.x.params.iter() {
            match *p.x.typ {
                TypX::Bool | TypX::Int(_) | TypX::Boxed(_) => {}
                _ => {
                    return Err(error(
                        &p.span,
                        "bit-vector function mode cannot have a datatype other than Integer/Boolean",
                    ));
                }
            }
        }
    }

    #[cfg(not(feature = "singular"))]
    if function.x.attrs.integer_ring && !_no_verify {
        return Err(error(
            &function.span,
            "Please cargo build with `--features singular` to use integer_ring attribute",
        ));
    }

    if function.x.attrs.exec_assume_termination && ctxt.no_cheating {
        return Err(error(
            &function.span,
            "#[verifier::assume_termination] not allowed with --no-cheating",
        ));
    }

    #[cfg(feature = "singular")]
    if function.x.attrs.integer_ring {
        let _ = match std::env::var("VERUS_SINGULAR_PATH") {
            Ok(_) => {}
            Err(_) => {
                return Err(error(
                    &function.span,
                    "Please provide VERUS_SINGULAR_PATH to use integer_ring attribute",
                ));
            }
        };

        if function.x.mode != Mode::Proof {
            return Err(error(&function.span, "integer_ring mode must be declared as proof"));
        }
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |_scope_map, expr| {
                match &expr.x {
                    ExprX::Block(_, _) => {}
                    _ => {
                        return Err(error(&function.span, "integer_ring mode cannot have a body"));
                    }
                }
                Ok(())
            })?;
        }
        for p in function.x.params.iter() {
            match *undecorate_typ(&p.x.typ) {
                TypX::Int(crate::ast::IntRange::Int) => {}
                TypX::Boxed(_) => {}
                _ => {
                    return Err(error(
                        &p.span,
                        "integer_ring proof's parameters should all be int type",
                    ));
                }
            }
        }
        if function.x.ens_has_return {
            return Err(error(
                &function.span,
                "integer_ring mode function cannot have a return value",
            ));
        }
        for req in function.x.require.iter() {
            crate::ast_visitor::expr_visitor_check(req, &mut |_scope_map, expr| {
                match *undecorate_typ(&expr.typ) {
                    TypX::Int(crate::ast::IntRange::Int) => {}
                    TypX::Int(_) => {
                        if let ExprX::Const(..) = &expr.x {
                            return Ok(());
                        } else {
                            return Err(error(
                                &req.span,
                                "integer_ring mode's expressions should be int/bool type",
                            ));
                        }
                    }
                    TypX::Bool => {}
                    TypX::Boxed(_) => {}
                    _ => {
                        return Err(error(
                            &req.span,
                            "integer_ring mode's expressions should be int/bool type",
                        ));
                    }
                }
                Ok(())
            })?;
        }
        for ens in function.x.ensure.0.iter().chain(function.x.ensure.1.iter()) {
            crate::ast_visitor::expr_visitor_check(ens, &mut |_scope_map, expr| {
                match *undecorate_typ(&expr.typ) {
                    TypX::Int(crate::ast::IntRange::Int) => {}
                    TypX::Int(_) => {
                        if let ExprX::Const(..) = &expr.x {
                            return Ok(());
                        } else {
                            return Err(error(
                                &ens.span,
                                "integer_ring mode's expressions should be int/bool type",
                            ));
                        }
                    }
                    TypX::Bool => {}
                    TypX::Boxed(_) => {}
                    _ => {
                        return Err(error(
                            &ens.span,
                            "integer_ring mode's expressions should be int/bool type",
                        ));
                    }
                }
                Ok(())
            })?;
        }
        if let Some(r) = &function.x.returns {
            return Err(error(&r.span, "integer_ring should not have a `returns` clause"));
        }
    }

    if function.x.is_main() && function.x.mode != Mode::Exec {
        return Err(error(&function.span, "`main` function should be #[verifier::exec]"));
    }

    // These should be true by construction in Rust->VIR; sanity check them here.
    if let crate::ast::BodyVisibility::Visibility(vis) = &function.x.body_visibility {
        if !vis.at_least_as_restrictive_as(&function.x.visibility) {
            crate::internal_err!(
                function.span.clone(),
                "the function body is more public than the function itself"
            );
        }
        match &function.x.opaqueness {
            Opaqueness::Opaque => {}
            Opaqueness::Revealed { visibility } => {
                if !visibility.at_least_as_restrictive_as(vis) {
                    crate::internal_err!(
                        function.span.clone(),
                        "the function reveal scope is more public the function body"
                    );
                }
            }
        }
    }

    for req in function.x.require.iter() {
        let msg = "'requires' clause of public function";
        let disallow_private_access = Some((&function.x.visibility, msg));
        check_expr(ctxt, function, req, disallow_private_access, Area::PreState("requires"), emit)?;
    }
    for ens in function.x.ensure.0.iter().chain(function.x.ensure.1.iter()) {
        let msg = "'ensures' clause of public function";
        let disallow_private_access = Some((&function.x.visibility, msg));
        check_expr(ctxt, function, ens, disallow_private_access, Area::PostState, emit)?;
    }
    if let Some(r) = &function.x.returns {
        if matches!(*function.x.ret.x.typ, TypX::Opaque { .. }) {
            return Err(error(
                &r.span,
                "`returns` clause is not allowed for function that returns opaque type",
            )
            .secondary_label(
                &function.span,
                format!("this function returns `{}`", typ_to_diagnostic_str(&function.x.ret.x.typ)),
            ));
        }

        if !types_equal(&undecorate_typ(&r.typ), &undecorate_typ(&function.x.ret.x.typ)) {
            return Err(error(
                &r.span,
                "type of `returns` clause does not match function return type",
            )
            .secondary_label(
                &function.span,
                format!("this function returns `{}`", typ_to_diagnostic_str(&function.x.ret.x.typ)),
            )
            .secondary_label(
                &r.span,
                format!("the `returns` clause has type `{}`", typ_to_diagnostic_str(&r.typ)),
            ));
        }

        let msg = "'requires' clause of public function";
        let disallow_private_access = Some((&function.x.visibility, msg));
        check_expr(ctxt, function, r, disallow_private_access, Area::PreState("returns"), emit)?;
    }
    match &function.x.mask_spec {
        None => {}
        Some(MaskSpec::InvariantOpens(_span, es) | MaskSpec::InvariantOpensExcept(_span, es)) => {
            for expr in es.iter() {
                let msg = "'opens_invariants' clause of public function";
                let disallow_private_access = Some((&function.x.visibility, msg));
                check_expr(
                    ctxt,
                    function,
                    expr,
                    disallow_private_access,
                    Area::PreState("opens_invariants clause"),
                    emit,
                )?;
            }
        }
        Some(MaskSpec::InvariantOpensSet(expr)) => {
            let msg = "'opens_invariants' clause of public function";
            let disallow_private_access = Some((&function.x.visibility, msg));
            check_expr(
                ctxt,
                function,
                expr,
                disallow_private_access,
                Area::PreState("opens_invariants clause"),
                emit,
            )?
        }
    }
    match &function.x.unwind_spec {
        None | Some(UnwindSpec::MayUnwind | UnwindSpec::NoUnwind) => {}
        Some(UnwindSpec::NoUnwindWhen(expr)) => {
            let msg = "unwind clause of public function";
            let disallow_private_access = Some((&function.x.visibility, msg));
            check_expr(
                ctxt,
                function,
                expr,
                disallow_private_access,
                Area::PreState("opens_invariants clause"),
                emit,
            )?;
        }
    }
    for expr in function.x.decrease.iter() {
        let msg = "'decreases' clause of public function";
        let disallow_private_access = Some((&function.x.visibility, msg));
        check_expr(
            ctxt,
            function,
            expr,
            disallow_private_access,
            Area::PreState("decreases clause"),
            emit,
        )?;
    }
    if let Some(expr) = &function.x.decrease_when {
        let msg = "'when' clause of public function";
        let disallow_private_access = Some((&function.x.visibility, msg));
        if function.x.mode != Mode::Spec {
            return Err(error(
                &function.span,
                "only spec functions can use decreases_when (use requires for proof/exec functions)",
            ));
        }
        if function.x.decrease.len() == 0 {
            return Err(error(
                &function.span,
                "decreases_when can only be used when there is a decreases clause (use recommends(...) for nonrecursive functions)",
            ));
        }
        check_expr(
            ctxt,
            function,
            expr,
            disallow_private_access,
            Area::PreState("when clause"),
            emit,
        )?;
    }

    if function.x.mode == Mode::Exec
        && (function.x.decrease.len() > 0 || function.x.decrease_by.is_some())
        && (function.x.attrs.exec_assume_termination
            || function.x.attrs.exec_allows_no_decreases_clause)
    {
        emit.emit(
            None,
            VirErrAs::Warning(error(
                &function.span,
                "if exec_allows_no_decreases_clause is set, decreases checks in exec functions do not guarantee termination of functions with loops",
            )),
        );
    }

    if let Some(body) = &function.x.body {
        let BodyVisibility::Visibility(body_visibility) = &function.x.body_visibility else {
            internal_err!(function.span.clone(), "an uninterpreted function cannot have a body");
        };
        // Check that public, non-abstract spec function bodies don't refer to private items:
        let disallow_private_access = if function.x.mode == Mode::Spec {
            let msg = "pub open spec function";
            Some((body_visibility, msg))
        } else {
            None
        };
        check_expr(ctxt, function, body, disallow_private_access, Area::Body, emit)?;
    }

    if function.x.attrs.is_type_invariant_fn {
        if function.x.mode != Mode::Spec {
            return Err(error(
                &function.span,
                "#[verifier::type_invariant] function must be `spec`",
            ));
        }
        if !matches!(&*function.x.ret.x.typ, TypX::Bool) {
            return Err(error(
                &function.span,
                "#[verifier::type_invariant] function must return bool",
            ));
        }
        if !matches!(function.x.kind, FunctionKind::Static) {
            return Err(error(
                &function.span,
                "#[verifier::type_invariant] function cannot be a trait function",
            ));
        }

        // Not strictly needed, but probably a mistake on the user's part
        if function.x.decrease_when.is_some() {
            return Err(error(
                &function.span,
                "#[verifier::type_invariant] function should not have a 'when' clause (consider adding it as a conjunct in the body)",
            ));
        }
        if function.x.require.len() > 0 {
            return Err(error(
                &function.span,
                "#[verifier::type_invariant] function should not have a 'recommends' clause (consider adding it as a conjunct in the body)",
            ));
        }
    }

    if ctxt.no_cheating && (function.x.attrs.is_external_body || function.x.proxy.is_some()) {
        match &function.x.owning_module {
            // Allow external_body/assume_specification inside vstd
            Some(path) if path.is_vstd_path() => {}
            _ => {
                return Err(error(
                    &function.span,
                    "external_body/assume_specification not allowed with --no-cheating",
                ));
            }
        }
    }

    Ok(())
}

fn check_datatype<Emit: EmitError>(
    ctxt: &Ctxt,
    dt: &Datatype,
    emit: &mut Emit,
) -> Result<(), VirErr> {
    for variant in dt.x.variants.iter() {
        for field in variant.fields.iter() {
            let typ = &field.a.0;
            check_typ(ctxt, typ, &dt.span, emit)?;
        }
    }

    if dt.x.user_defined_invariant_fn.is_some() {
        if dt.x.proxy.is_some() {
            return Err(error(
                &dt.span,
                "#[verifier::type_invariant] cannot be applied to a datatype that uses #[verifier::external_type_specification]",
            ));
        }
        match &dt.x.transparency {
            DatatypeTransparency::Never => {}
            DatatypeTransparency::WhenVisible(vis) => {
                if vis.is_public() {
                    return Err(error(
                        &dt.span,
                        "#[verifier::type_invariant]: a struct with a type invariant cannot have any fields public to the crate",
                    ));
                }
            }
        }
    }

    // I actually think it's impossible to trigger this, at least when the datatype's public
    // signature is well-formed (i.e., Verus recognizes all trait bounds, etc.)
    // See the notes in `get_sized_constraint` in rust_to_vir_adts.rs.
    if let Some(sized_constraint) = &dt.x.sized_constraint {
        match check_typ(ctxt, sized_constraint, &dt.span, emit) {
            Ok(()) => {}
            Err(e) => {
                let typ_args = Arc::new(
                    dt.x.typ_params
                        .iter()
                        .map(|(id, _)| Arc::new(TypX::TypParam(id.clone())))
                        .collect::<Vec<_>>(),
                );
                let t = Arc::new(TypX::Datatype(dt.x.name.clone(), typ_args, Arc::new(vec![])));
                let e = e.help(format!(
                    "this type appears in the implicit trait bound, `{:}: Sized where {:}: Sized`",
                    typ_to_diagnostic_str(&t),
                    typ_to_diagnostic_str(sized_constraint)
                ));
                return Err(e);
            }
        }
    }

    Ok(())
}

fn check_functions_match(
    msg: &str,
    check_names: bool,
    check_modes: bool,
    check_return: bool,
    f1: &Function,
    f2: &Function,
) -> Result<(), VirErr> {
    if f1.x.typ_params.len() != f2.x.typ_params.len() {
        return Err(crate::messages::error(
            &f1.span,
            format!("{msg} function should have the same type parameters"),
        )
        .secondary_span(&f2.span));
    }
    if f1.x.typ_bounds.len() != f2.x.typ_bounds.len() {
        return Err(crate::messages::error(
            &f1.span,
            format!("{msg} function should have the same type bounds"),
        )
        .secondary_span(&f2.span));
    }
    for (x1, x2) in f1.x.typ_params.iter().zip(f2.x.typ_params.iter()) {
        if x1 != x2 {
            return Err(crate::messages::error(
                &f1.span,
                format!("{msg} function should have the same type bounds"),
            )
            .secondary_span(&f2.span));
        }
    }
    for (b1, b2) in f1.x.typ_bounds.iter().zip(f2.x.typ_bounds.iter()) {
        if !crate::ast_util::generic_bounds_equal(&b1, &b2) {
            return Err(crate::messages::error(
                &f1.span,
                format!("{msg} function should have the same type bounds"),
            )
            .secondary_span(&f2.span));
        }
    }
    if f1.x.params.len() != f2.x.params.len() {
        return Err(crate::messages::error(
            &f1.span,
            format!("{msg} function should have the same number of parameters"),
        )
        .secondary_span(&f2.span));
    }
    for (pp, fp) in f1.x.params.iter().zip(f2.x.params.iter()) {
        if !crate::ast_util::params_equal_opt(&pp, &fp, check_names, check_modes) {
            return Err(crate::messages::error(
                &pp.span,
                format!("{msg} function should have the same parameters"),
            )
            .secondary_span(&fp.span));
        }
    }
    if check_return {
        if !crate::ast_util::params_equal_opt(&f1.x.ret, &f2.x.ret, check_names, check_modes) {
            return Err(crate::messages::error(
                &f1.x.ret.span,
                format!("{msg} function should have the same return types"),
            )
            .secondary_span(&f2.x.ret.span));
        }
    }
    Ok(())
}

/// Construct an error message for when our Krate has two functions of the same name.
/// If this happen it's probably either:
///  (i) an issue with our conversion from rust paths to VIR paths not being injective
///  (ii) the user's use of external_fn_specification/assume_specification resulting in overlap
///  (iii) an existing issue related to traits
fn func_conflict_error(function1: &Function, function2: &Function) -> Message {
    let add_label = |err: Message, function: &Function| match &function.x.proxy {
        Some(proxy) => {
            err.primary_label(&proxy.span, "specification declared via `assume_specification`")
        }
        None => err.primary_label(&function.span, "declared here (and not marked as `external`)"),
    };

    let err = crate::messages::error_bare(format!(
        "duplicate specification for `{:}`",
        crate::ast_util::path_as_friendly_rust_name(&function1.x.name.path)
    ));
    let err = add_label(err, function1);
    let err = add_label(err, function2);
    err
}

/// Similar to above, for datatypes
fn datatype_conflict_error(dt1: &Datatype, dt2: &Datatype) -> Message {
    let add_label = |err: Message, dt: &Datatype| match &dt.x.proxy {
        Some(proxy) => err
            .primary_label(&proxy.span, "specification declared via `external_type_specification`"),
        None => err.primary_label(&dt.span, "declared here (and not marked as `external`)"),
    };

    let err = crate::messages::error_bare(format!(
        "duplicate specification for `{:}`",
        crate::ast_util::dt_as_friendly_rust_name(&dt1.x.name)
    ));
    let err = add_label(err, dt1);
    let err = add_label(err, dt2);
    err
}

pub(crate) fn trait_conflict_error(tr1: &Trait, tr2: &Trait, msg: &str) -> Message {
    let add_label = |err: Message, tr: &Trait| match &tr.x.proxy {
        Some(proxy) => err.primary_label(
            &proxy.span,
            "specification declared via `external_trait_specification`",
        ),
        None => err.primary_label(&tr.span, "declared here (and not marked as `external`)"),
    };

    let err = crate::messages::error_bare(format!(
        "{msg} `{:}`",
        crate::ast_util::path_as_friendly_rust_name(&tr1.x.name)
    ));
    let err = add_label(err, tr1);
    let err = add_label(err, tr2);
    err
}

// Pre-merge check.
// TODO: We should probably be doing all the checks on the just the pre-merged crate declarations,
// even if we need to perform lookups from the merged crate.
pub fn check_one_crate(krate: &Krate) -> Result<(), VirErr> {
    let mut reveal_group_default = None;
    for group in krate.reveal_groups.iter() {
        if group.x.broadcast_use_by_default_when_this_crate_is_imported.is_some() {
            if let Some(prev) = reveal_group_default {
                let err = error(
                    &group.span,
                    "only one broadcast_use_by_default_when_this_crate_is_imported is allowed",
                );
                let err = err.primary_span(&prev);
                return Err(err);
            }
            reveal_group_default = Some(group.span.clone());
        }
    }
    Ok(())
}

pub fn check_crate(
    krate: &Krate,
    unpruned_krate: &Krate,
    diags: &mut Vec<VirErrAs>,
    no_verify: bool,
    no_cheating: bool,
) -> Result<(), VirErr> {
    let mut funs: HashMap<Fun, Function> = HashMap::new();
    for function in krate.functions.iter() {
        match funs.get(&function.x.name) {
            Some(other_function) => {
                return Err(func_conflict_error(function, other_function));
            }
            None => {}
        }
        funs.insert(function.x.name.clone(), function.clone());
    }
    let mut dts: HashMap<Path, Datatype> = HashMap::new();
    for datatype in krate.datatypes.iter() {
        let path = match &datatype.x.name {
            Dt::Path(p) => p,
            Dt::Tuple(_) => {
                panic!("Verus Internal Error: Dt::Tuple not expected in well_formed.rs")
            }
        };
        match dts.get(path) {
            Some(other_datatype) => {
                return Err(datatype_conflict_error(datatype, other_datatype));
            }
            None => {}
        }
        dts.insert(path.clone(), datatype.clone());
    }
    let mut traits: HashMap<Path, Trait> = HashMap::new();
    for tr in krate.traits.iter() {
        match traits.get(&tr.x.name) {
            Some(other_tr) => {
                return Err(trait_conflict_error(tr, other_tr, "duplicate specification for"));
            }
            None => {}
        }
        traits.insert(tr.x.name.clone(), tr.clone());
    }
    let reveal_groups: HashSet<Fun> =
        krate.reveal_groups.iter().map(|g| g.x.name.clone()).collect();

    // Check connections between decreases_by specs and proofs
    let mut decreases_by_proof_to_spec: HashMap<Fun, Fun> = HashMap::new();
    for function in krate.functions.iter() {
        if let Some(proof_fun) = &function.x.decrease_by {
            let proof_function = if let Some(proof_function) = funs.get(proof_fun) {
                proof_function
            } else {
                return Err(error(
                    &function.span,
                    "cannot find function referred to in decreases_by/recommends_by",
                ));
            };
            if !proof_function.x.attrs.is_decrease_by {
                return Err(error(
                    &proof_function.span,
                    "proof function must be marked #[verifier::decreases_by] or #[verifier::recommends_by] to be used as decreases_by/recommends_by",
                )
                .secondary_span(&function.span));
            }
            if let Some(prev) = decreases_by_proof_to_spec.get(proof_fun) {
                return Err(error(
                    &proof_function.span,
                    "same proof function used for two different decreases_by/recommends_by",
                )
                .secondary_span(&funs[prev].span)
                .secondary_span(&function.span));
            }
            if proof_fun.path.pop_segment() != function.x.name.path.pop_segment() {
                return Err(error(
                    &proof_function.span,
                    "a decreases_by function must be in the same module as the function definition",
                )
                .secondary_span(&function.span));
            }

            if proof_function.x.mode != Mode::Proof {
                return Err(error(
                    &proof_function.span,
                    "decreases_by/recommends_by function must have mode proof",
                ));
            }

            decreases_by_proof_to_spec.insert(proof_fun.clone(), function.x.name.clone());
            check_functions_match(
                "decreases_by/recommends_by",
                true,
                true,
                false,
                &proof_function,
                &function,
            )?;
        }
        if let Some(spec_fun) = &function.x.attrs.autospec {
            let spec_function = if let Some(spec_function) = funs.get(spec_fun) {
                spec_function
            } else {
                return Err(error(
                    &function.span,
                    format!(
                        "cannot find function referred to in when_used_as_spec: {}",
                        fun_as_friendly_rust_name(spec_fun),
                    ),
                ));
            };
            if function.x.mode != Mode::Exec || spec_function.x.mode != Mode::Spec {
                return Err(error(
                    &spec_function.span,
                    "when_used_as_spec must point from an exec function to a spec function",
                )
                .secondary_span(&function.span));
            }
            match (&function.x.kind, &spec_function.x.kind) {
                (
                    FunctionKind::TraitMethodDecl { trait_path: p1, .. },
                    FunctionKind::TraitMethodDecl { trait_path: p2, .. },
                ) if p1 == p2 => {}
                (FunctionKind::TraitMethodDecl { .. }, _) => {
                    return Err(error(
                        &spec_function.span,
                        "when_used_as_spec on trait declaration must refer to a spec function in the same trait",
                    )
                    .secondary_span(&function.span));
                }
                (_, FunctionKind::Static) => {}
                (_, _) => {
                    // We can't yet handle FunctionKind::TraitMethodImpl because we don't
                    // have the corresponding Dynamic info (typs, impl_paths) in general.
                    return Err(error(
                        &spec_function.span,
                        "when_used_as_spec must point to a non-trait spec function",
                    )
                    .secondary_span(&function.span));
                }
            }
            if !is_visible_to_opt(&spec_function.x.visibility, &function.x.visibility.restricted_to)
            {
                return Err(error(
                    &function.span,
                    "when_used_as_spec refers to function which is more private",
                ));
            }

            check_functions_match(
                "when_used_as_spec",
                false,
                false,
                true,
                &spec_function,
                &function,
            )?;
        }
        if function.x.ensure.1.len() > 0
            && !matches!(&function.x.kind, FunctionKind::TraitMethodDecl { .. })
        {
            return Err(error(&function.span, "default_ensures not allowed here"));
        }
        if let FunctionKind::TraitMethodDecl { .. } = &function.x.kind {
            if function.x.body.is_some() {
                if function.x.decrease.len() > 0 {
                    return Err(error(
                        &function.span,
                        "trait default methods do not yet support recursion and decreases",
                    ));
                }
            }
        }
        if function.x.attrs.broadcast_forall {
            use crate::ast_visitor::{VisitorControlFlow, VisitorScopeMap};
            let mut f_find_trigger = |_: &mut VisitorScopeMap, expr: &Expr| match &expr.x {
                ExprX::WithTriggers { .. } => VisitorControlFlow::Stop(()),
                ExprX::Unary(UnaryOp::Trigger(..), _) => VisitorControlFlow::Stop(()),
                ExprX::Quant(..) => VisitorControlFlow::Return,
                _ => VisitorControlFlow::Recurse,
            };
            let mut found_trigger = false;
            for expr in function
                .x
                .require
                .iter()
                .chain(function.x.ensure.0.iter())
                .chain(function.x.ensure.1.iter())
                .chain(function.x.returns.iter())
            {
                let control = crate::ast_visitor::expr_visitor_dfs(
                    expr,
                    &mut air::scope_map::ScopeMap::new(),
                    &mut f_find_trigger,
                );
                if control == VisitorControlFlow::Stop(()) {
                    found_trigger = true;
                }
            }
            if !found_trigger {
                diags.push(VirErrAs::Warning(error(
                    &function.span,
                    "broadcast functions should have explicit #[trigger] or #![trigger ...]",
                )));
            }
        }
    }
    for function in krate.functions.iter() {
        if function.x.attrs.is_decrease_by
            && !decreases_by_proof_to_spec.contains_key(&function.x.name)
        {
            return Err(error(
                &function.span,
                "function cannot be marked #[verifier::decreases_by] or #[verifier::recommends_by] unless it is used in some decreases_by/recommends_by",
            ));
        }
    }

    for module in krate.modules.iter() {
        if let Some(reveals) = &module.x.reveals {
            for reveal in reveals.x.iter() {
                if let Some(function) = funs.get(reveal) {
                    if !function.x.attrs.broadcast_forall {
                        return Err(error(
                            &reveals.span,
                            format!(
                                "{} is not a broadcast proof fn",
                                fun_as_friendly_rust_name(reveal)
                            ),
                        ));
                    }
                } else {
                    assert!(reveal_groups.contains(reveal));
                }
            }
        }
    }

    for reveal_group in krate.reveal_groups.iter() {
        for member in reveal_group.x.members.iter() {
            if let Some(function) = funs.get(member) {
                if !function.x.attrs.broadcast_forall {
                    return Err(error(
                        &reveal_group.span,
                        format!(
                            "{} is not a broadcast proof fn",
                            fun_as_friendly_rust_name(member)
                        ),
                    ));
                }
            }
        }
    }

    let diag_map: HashMap<Path, usize> = HashMap::new();
    let new_diags: Vec<VirErrAs> = Vec::new();
    let mut emit = EmitErrorState { diag_map, diags: new_diags };
    let ctxt = Ctxt { funs, reveal_groups, dts, traits, krate, unpruned_krate, no_cheating };
    // TODO remove once `uninterp` is enforced for uninterpreted functions
    for function in krate.functions.iter() {
        check_function(&ctxt, function, &mut emit, no_verify)?;
    }
    for dt in krate.datatypes.iter() {
        check_datatype(&ctxt, dt, &mut emit)?;
    }
    for tr_impl in krate.trait_impls.iter() {
        for typ in tr_impl.x.trait_typ_args.iter() {
            check_typ(&ctxt, typ, &tr_impl.span, &mut emit)?;
        }
    }
    for assoc_type_impl in krate.assoc_type_impls.iter() {
        for typ in assoc_type_impl.x.trait_typ_args.iter() {
            check_typ(&ctxt, typ, &assoc_type_impl.span, &mut emit)?;
        }
        check_typ(&ctxt, &assoc_type_impl.x.typ, &assoc_type_impl.span, &mut emit)?;
    }

    diags.append(&mut emit.diags);
    // There is no point in checking for well-founded types if we already have a fatal error:
    if diags.iter().any(|x| matches!(x, VirErrAs::NonBlockingError(..))) {
        return Ok(());
    }
    crate::recursive_types::check_recursive_types(krate)?;
    Ok(())
}
