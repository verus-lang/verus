use crate::context::{BodyCtxt, Context};
use crate::verus_items::RustItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyKind;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    Arm, AutospecUsage, BinaryOp, BodyVisibility, CallTarget, CallTargetAttrs, CallTargetKind,
    CrateId, Expr, ExprX, FieldOpr, Fun, Function, FunctionAttrsX, FunctionKind, FunctionStub,
    FunctionStubX, FunctionX, GenericBounds, Idents, ImplPaths, ItemKind, Mode, Opaqueness, ParamX,
    Path, Place, PlaceX, SpannedTyped, Typ, TypX, UnaryOpr, VarIdent, VirErr, VirErrAs, Visibility,
};
use vir::ast_util::bool_typ;
use vir::messages::WarningAllow;

/// Traits with special handling
#[derive(Clone, Copy, Debug)]
pub enum SpecialTrait {
    Clone,
    //PartialEq,
}

/// What to do for a given automatically-derived trait impl
#[derive(Debug, Clone, Copy)]
pub enum AutomaticDeriveAction {
    Special(SpecialTrait),
    VerifyAsIs,
    /// Ignore, optionally providing a warning
    Ignore,
}

pub fn get_action(rust_item: Option<RustItem>) -> AutomaticDeriveAction {
    match rust_item {
        Some(RustItem::PartialEq | RustItem::Eq) => AutomaticDeriveAction::Ignore,
        Some(RustItem::Clone) => AutomaticDeriveAction::Special(SpecialTrait::Clone),

        Some(RustItem::Copy) => AutomaticDeriveAction::VerifyAsIs,

        Some(RustItem::Hash)
        | Some(RustItem::Default)
        | Some(RustItem::Debug)
        | Some(RustItem::Ord)
        | Some(RustItem::PartialOrd) => AutomaticDeriveAction::Ignore,

        Some(_) | None => AutomaticDeriveAction::VerifyAsIs,
    }
}

pub fn is_automatically_derived(attrs: &[rustc_hir::Attribute]) -> bool {
    for attr in attrs.iter() {
        match attr {
            rustc_hir::Attribute::Unparsed(item) => match &item.path.segments[..] {
                [segment] => {
                    if segment.as_str() == "automatically_derived" {
                        return true;
                    }
                }
                _ => {}
            },
            rustc_hir::Attribute::Parsed(rustc_hir::attrs::AttributeKind::AutomaticallyDerived) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// Called when creating the FunctionStub for an automatically-derived function,
/// before the body is processed.
/// If the derived function needs an auxiliary spec function (see `clone_add_post_condition`),
/// this creates the FunctionStub for that auxiliary function up front
/// (and adjusts the stub of the derived function as necessary).
/// The full auxiliary Function is created later, by `modify_derived_item`.
pub(crate) fn make_aux_function_stub<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    action: AutomaticDeriveAction,
    function: &mut FunctionStubX,
    def_id: DefId,
) -> Result<Option<FunctionStub>, VirErr> {
    let AutomaticDeriveAction::Special(special) = action else {
        return Ok(None);
    };
    match special {
        SpecialTrait::Clone => {
            if function.name.path.last_segment().is_name("clone") && function.params.len() >= 1 {
                let module_path = function.name.path.pop_segment().pop_segment();
                let spec_fn_name = vir::def::clone_spec_fn_name(&function.name.path.pop_segment());
                let other_ident = vir::ast_util::air_unique_var(vir::def::OTHER_PARAM_VALUE);
                let (datatype_visibility, datatype_body_visibility) =
                    get_visibilities(ctxt, span, def_id)?;
                // TODO: Right now trait functions are always public, but the datatype might be
                // private, so it's impossible to make the ensures clause well-formed.
                // So we fix the visibility here, but really,
                // we should find a general solution that works for all trait functions.
                function.visibility = datatype_visibility.clone();
                let stub = mk_spec_function_stub(
                    &ctxt.spans.to_air_span(span),
                    spec_fn_name,
                    datatype_visibility,
                    datatype_body_visibility,
                    &module_path,
                    &function.typ_params,
                    &function.typ_bounds,
                    &function.params[0].x.typ,
                    &function.params[0].x.name,
                    &other_ident,
                );
                return Ok(Some(stub));
            }
        }
    }
    Ok(None)
}

/// Called after the body of the automatically-derived function is processed.
/// `aux_stub` should be the stub returned by `make_aux_function_stub`;
/// if it is `Some`, this always returns the corresponding full auxiliary Function.
pub(crate) fn modify_derived_item<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    id: rustc_span::def_id::DefId,
    inputs: &Vec<rustc_middle::ty::Ty>,
    span: Span,
    action: AutomaticDeriveAction,
    function: &mut FunctionX,
    aux_stub: Option<&FunctionStub>,
) -> Result<Option<Function>, VirErr> {
    let mut aux_body = None;
    if let AutomaticDeriveAction::Special(special) = action {
        match special {
            SpecialTrait::Clone => {
                if function.name.path.last_segment().is_name("clone") {
                    aux_body =
                        clone_add_post_condition(bctx, id, inputs, span, function, aux_stub)?;
                }
            }
        }
    }
    match aux_stub {
        Some(aux_stub) => {
            // If we didn't end up needing the auxiliary function, we still need to
            // produce a Function for the stub; if aux_body == None, this will just
            // create a function with an uninterpreted body.
            Ok(Some(stub_to_spec_function(aux_stub, aux_body)))
        }
        None => {
            assert!(aux_body.is_none());
            Ok(None)
        }
    }
}

/// Returns the body for the auxiliary spec function, if it's needed
fn clone_add_post_condition<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    mut id: rustc_span::def_id::DefId,
    inputs: &Vec<rustc_middle::ty::Ty>,
    span: Span,
    functionx: &mut FunctionX,
    aux_stub: Option<&FunctionStub>,
) -> Result<Option<Expr>, VirErr> {
    if inputs.len() >= 1 {
        use rustc_middle::ty::{AdtDef, TyKind};
        if let TyKind::Ref(_, t, _) = inputs[0].kind() {
            if let TyKind::Adt(AdtDef(adt_def_data), _) = t.kind() {
                // It's more convenient to put verifier::allow on the datatype than on the function
                id = adt_def_data.did;
            }
        }
    }
    let warn = |msg: &str| {
        crate::attributes::warning_maybe(
            bctx.ctxt.tcx,
            id,
            span,
            &WarningAllow::AutoderiveCloneWithoutSpec,
            || msg,
            |msg| bctx.ctxt.diagnostics.borrow_mut().push(VirErrAs::Warning(msg)),
        );
    };
    let warn_unexpected = || {
        warn(
            "autoderive `Clone` impl does not take the form Verus expects; continuing, but without adding a specification for the derived Clone impl",
        )
    };

    let Some(body) = &functionx.body else {
        return Ok(None);
    };

    let uses_copy;
    let self_var;

    match &body.x {
        ExprX::Block(_stmts, Some(last_expr)) => match &last_expr.x {
            ExprX::ReadPlace(pl, _) => match &pl.x {
                PlaceX::Local(id) if &*id.0 == "self" => {
                    uses_copy = true;
                    self_var = Some(last_expr.clone());
                }
                _ => {
                    uses_copy = false;
                    self_var = None;
                }
            },
            _ => {
                uses_copy = false;
                self_var = None;
            }
        },
        _ => {
            warn_unexpected();
            return Ok(None);
        }
    }

    if functionx.ensure.0.len() != 0 {
        warn_unexpected();
        return Ok(None);
    }

    if uses_copy {
        // Add `ensures ret == self`
        let self_var = self_var.unwrap();
        let ret_var = SpannedTyped::new(
            &self_var.span,
            &self_var.typ,
            ExprX::Var(functionx.inner_ret.x.name.clone()),
        );
        let eq_expr = SpannedTyped::new(
            &self_var.span,
            &vir::ast_util::bool_typ(),
            ExprX::Binary(BinaryOp::Eq(Mode::Spec), ret_var.clone(), self_var.clone()),
        );

        let eq_expr = cleanup_span_ids(bctx, span, &eq_expr);
        functionx.ensure.0 = Arc::new(vec![eq_expr]);
        Ok(None)
    } else {
        // for a struct `S { x: X, y: Y }`, the clone function looks like
        //   `S { x: self.x.clone(), y: self.y.clone() }`.
        // Basically we want the ensures clause to be something like:
        //   strictly_cloned(self.x, out.x) && strictly_cloned(self.y, out.y)
        // However, some of the fields might be private.
        // So we factor the ensures clause out into a separate spec function where we can
        // configure the body visibility.
        // So we end up with:
        //
        // spec fn helper_clone_fn(self: S, other: S) -> bool {
        //   strictly_cloned(self.x, out.x) && strictly_cloned(self.y, out.y)
        // }
        //
        // impl Clone for S {
        //     fn clone(&self) -> (out: self)
        //         ensures helper_clone_fn(self, out)
        //     { ... }
        // }
        //
        // For enums, it's similar, but there's a match statement to handle.

        let Some(aux_stub) = aux_stub else {
            warn_unexpected();
            return Ok(None);
        };
        let ExprX::Block(_, Some(expr)) = &body.x else { unreachable!() };
        let other_ident = aux_stub.x.params[1].x.name.clone();
        let other_var = SpannedTyped::new(
            &expr.span,
            &functionx.params[0].x.typ,
            ExprX::Var(other_ident.clone()),
        );
        let rel = match to_relation(expr, &other_var) {
            Ok(rel) => rel,
            Err(()) => {
                warn_unexpected();
                return Ok(None);
            }
        };
        let rel = cleanup_span_ids(bctx, span, &rel);

        let typ_args: Vec<_> = functionx
            .typ_params
            .iter()
            .map(|param| Arc::new(TypX::TypParam(param.clone())))
            .collect();
        let ct = CallTarget::Fun(
            CallTargetKind::Static,
            aux_stub.x.name.clone(),
            Arc::new(typ_args),
            Arc::new(vec![]),
            CallTargetAttrs {
                autospec: AutospecUsage::Final,
                const_var: false,
                assume_external_allowed: false,
            },
        );
        let self_var = SpannedTyped::new(
            &expr.span,
            &functionx.params[0].x.typ,
            ExprX::Var(functionx.params[0].x.name.clone()),
        );
        let ret_var = SpannedTyped::new(
            &expr.span,
            &functionx.outer_ret.x.typ,
            ExprX::Var(functionx.inner_ret.x.name.clone()),
        );
        let args = Arc::new(vec![self_var, ret_var]);
        let ens_expr = SpannedTyped::new(
            &expr.span,
            &bool_typ(),
            ExprX::Call { target: ct, args, body: None, post_args: None },
        );

        let ens_expr = cleanup_span_ids(bctx, span, &ens_expr);
        functionx.ensure.0 = Arc::new(vec![ens_expr]);
        Ok(Some(rel))
    }
}

/// Turn
///   `match scrutinee { pat => Struct { field: arg.clone() , ... }, ... }`
/// into:
///   `match scrutinee { pat => vstd::pervasive::strictly_cloned(arg, out.field) && ..., ... }`
fn to_relation(expr: &Expr, output: &Expr) -> Result<Expr, ()> {
    match &expr.x {
        ExprX::Match(scrutinee, arms, assert_irrefutable) => {
            let mut new_arms: Vec<Arm> = vec![];
            for mut arm in arms.iter().cloned() {
                let armx = Arc::make_mut(&mut arm);
                armx.x.body = to_relation(&armx.x.body, output)?;
                new_arms.push(arm);
            }
            Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Match(scrutinee.clone(), Arc::new(new_arms), *assert_irrefutable),
            ))
        }
        ExprX::Ctor(dt, variant_ident, binders, None) => {
            let mut conjuncts = vec![SpannedTyped::new(
                &expr.span,
                &bool_typ(),
                ExprX::UnaryOpr(
                    UnaryOpr::IsVariant { datatype: dt.clone(), variant: variant_ident.clone() },
                    output.clone(),
                ),
            )];
            for binder in binders.iter() {
                let field_of_output = SpannedTyped::new(
                    &expr.span,
                    &binder.a.typ,
                    ExprX::UnaryOpr(
                        UnaryOpr::Field(FieldOpr {
                            datatype: dt.clone(),
                            variant: variant_ident.clone(),
                            field: binder.name.clone(),
                            get_variant: true,
                            check: vir::ast::VariantCheck::None,
                        }),
                        output.clone(),
                    ),
                );
                let (clonee, impl_paths, clone_typ_arg) = match &binder.a.x {
                    ExprX::Call {
                        target:
                            CallTarget::Fun(
                                CallTargetKind::DynamicResolved { .. } | CallTargetKind::Dynamic,
                                fun,
                                typs,
                                impl_paths,
                                _call_target_attrs,
                            ),
                        args,
                        body: None,
                        post_args: None,
                    } if fun == &vir::fun!(CrateId::Core => "clone", "Clone"; "clone") => {
                        assert!(args.len() == 1);
                        (args[0].clone(), impl_paths.clone(), typs[0].clone())
                    }
                    _ => {
                        return Err(());
                    }
                };
                conjuncts.push(strictly_cloned_call(
                    &clonee,
                    &field_of_output,
                    clone_typ_arg,
                    impl_paths,
                ));
            }
            Ok(vir::ast_util::conjoin(&expr.span, &conjuncts))
        }
        _ => Err(()),
    }
}

fn strictly_cloned_call(e1: &Expr, e2: &Expr, typ: Typ, impl_paths: ImplPaths) -> Expr {
    let fun = vir::fun!(CrateId::Vstd => "pervasive"; "strictly_cloned");
    let ct = CallTarget::Fun(
        CallTargetKind::Static,
        fun,
        Arc::new(vec![typ]),
        impl_paths,
        CallTargetAttrs {
            autospec: AutospecUsage::Final,
            const_var: false,
            assume_external_allowed: false,
        },
    );
    let args = Arc::new(vec![e1.clone(), e2.clone()]);
    SpannedTyped::new(
        &e1.span,
        &bool_typ(),
        ExprX::Call { target: ct, args, body: None, post_args: None },
    )
}

fn mk_spec_function_stub(
    span: &vir::messages::Span,
    spec_fn_name: Fun,
    datatype_visibility: Visibility,
    datatype_body_visibility: Visibility,
    module: &Path,
    typ_params: &Idents,
    typ_bounds: &GenericBounds,
    self_typ: &Typ,
    self_param_name: &VarIdent,
    other_param_name: &VarIdent,
) -> FunctionStub {
    let self_param = vir::def::Spanned::new(
        span.clone(),
        ParamX {
            name: self_param_name.clone(),
            typ: self_typ.clone(),
            mode: Mode::Spec,
            unwrapped_info: None,
            user_mut: false,
        },
    );
    let other_param = vir::def::Spanned::new(
        span.clone(),
        ParamX {
            name: other_param_name.clone(),
            typ: self_typ.clone(),
            mode: Mode::Spec,
            unwrapped_info: None,
            user_mut: false,
        },
    );
    let ret_param = vir::def::Spanned::new(
        span.clone(),
        ParamX {
            name: vir::ast_util::air_unique_var(vir::def::RETURN_VALUE),
            typ: bool_typ(),
            mode: Mode::Spec,
            unwrapped_info: None,
            user_mut: false,
        },
    );
    vir::def::Spanned::new(
        span.clone(),
        FunctionStubX {
            name: spec_fn_name,
            proxy: None,
            kind: FunctionKind::Static,
            visibility: datatype_visibility,
            body_visibility: BodyVisibility::Visibility(datatype_body_visibility.clone()),
            opaqueness: Opaqueness::Revealed { visibility: datatype_body_visibility.clone() },
            owning_module: Some(module.clone()),
            mode: Mode::Spec,
            typ_params: typ_params.clone(),
            typ_bounds: typ_bounds.clone(),
            params: Arc::new(vec![self_param, other_param]),
            outer_ret: ret_param,
            returns: false,
            decreases_len: 0,
            item_kind: ItemKind::Function,
            attrs: Arc::new(FunctionAttrsX {
                uses_ghost_blocks: true,
                inline: false,
                broadcast_forall: false,
                broadcast_forall_only: false,
                no_auto_trigger: false,
                auto_ext_equal: vir::ast::AutoExtEqual {
                    assert: false,
                    assert_by: false,
                    ensures: false,
                    invariant: false,
                },
                autospec: None,
                bit_vector: false,
                atomic: false,
                integer_ring: false,
                is_decrease_by: false,
                check_recommends: false,
                nonlinear: false,
                spinoff_prover: false,
                memoize: false,
                rlimit: None,
                print_zero_args: false,
                print_as_method: false,
                prophecy_dependent: false,
                size_of_broadcast_proof: false,
                is_type_invariant_fn: false,
                is_external_body: false,
                is_unsafe: false,
                exec_assume_termination: false,
                exec_allows_no_decreases_clause: false,
                tracked_swap: false,
                tracked_take_option: false,
                is_async: false,
                impls_cannot_extend_spec: false,
                is_drop: false,
                create_open_invariant_credit: false,
            }),
        },
    )
}

fn stub_to_spec_function(stub: &FunctionStub, body: Option<Expr>) -> Function {
    let FunctionStubX {
        name,
        proxy,
        kind,
        visibility,
        body_visibility,
        opaqueness,
        owning_module,
        mode,
        typ_params,
        typ_bounds,
        params,
        outer_ret,
        item_kind,
        attrs,
        returns,
        decreases_len,
    } = stub.x.clone();
    assert!(!returns);
    assert!(decreases_len == 0);
    vir::def::Spanned::new(
        stub.span.clone(),
        FunctionX {
            name,
            proxy,
            kind,
            visibility,
            body_visibility,
            opaqueness,
            owning_module,
            mode,
            typ_params,
            typ_bounds,
            params,
            inner_ret: outer_ret.clone(),
            outer_ret,
            require: Arc::new(vec![]),
            ensure: (Arc::new(vec![]), Arc::new(vec![])),
            returns: None,
            decrease: Arc::new(vec![]),
            decrease_when: None,
            decrease_by: None,
            fndef_axioms: None,
            mask_spec: None,
            unwind_spec: None,
            item_kind,
            attrs,
            body: body,
            extra_dependencies: vec![],
            atomic_update: None,
            hidden: Arc::new(vec![]),
            return_opaque_type_eqs: Arc::new(vec![]),
        },
    )
}

/// Given the DefId of the clone impl, returns:
/// (i) visiblity of the datatype
/// (ii) visiblity of the interior of the datatype
fn get_visibilities<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    def_id: DefId,
) -> Result<(Visibility, Visibility), VirErr> {
    let fn_sig = ctxt.tcx.fn_sig(def_id).skip_binder();
    let self_ty = fn_sig.output().skip_binder();
    let adt_def = match self_ty.kind() {
        TyKind::Adt(adt_def, _args) => adt_def,
        _ => {
            return crate::util::err_span(
                span,
                "Verus Internal Error: handling auto-derive Clone, expected TyKind::Adt",
            );
        }
    };
    let datatype_vis = crate::rust_to_vir_base::mk_visibility(ctxt, adt_def.did());
    let mut inner_vis = datatype_vis.clone();
    for variant_def in adt_def.variants().iter() {
        for field_def in variant_def.fields.iter() {
            let vis = crate::rust_to_vir_base::mk_visibility_from_vis(ctxt, field_def.vis);
            inner_vis = inner_vis.join(&vis);
        }
    }
    Ok((datatype_vis, inner_vis))
}

/// Give each node a unique ID. This inserts 'None' for every var into the local_hir_vir_ids
/// list, so it's only safe for pure expressions (e.g., in asserts or signatures).
fn cleanup_span_ids<'tcx>(bctx: &BodyCtxt<'tcx>, span: Span, expr: &Expr) -> Expr {
    vir::ast_visitor::map_expr_place_visitor(
        expr,
        &|e: &Expr| {
            let e = bctx.ctxt.spans.spanned_typed_new(span, &e.typ, e.x.clone());
            if matches!(&e.x, ExprX::Var(..) | ExprX::VarAt(..)) {
                let mut erasure_info = bctx.erasure_info.borrow_mut();
                erasure_info.local_hir_vir_ids.push((None, e.span.id));
            }
            Ok(e)
        },
        &|p: &Place| {
            let p = bctx.ctxt.spans.spanned_typed_new(span, &p.typ, p.x.clone());
            if matches!(&p.x, PlaceX::Local(..)) {
                let mut erasure_info = bctx.erasure_info.borrow_mut();
                erasure_info.local_hir_vir_ids.push((None, p.span.id));
            }
            Ok(p)
        },
    )
    .unwrap()
}
