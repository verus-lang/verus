use crate::context::Context;
use crate::verus_items::RustItem;
use rustc_hir::HirId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    BinaryOp, Expr, ExprX, FunctionX, Mode, Place, PlaceX, SpannedTyped, VirErr, VirErrAs,
    CallTarget, CallTargetKind, TypX, CallTargetAttrs, AutospecUsage, Arm, UnaryOpr, FieldOpr, Typ, ImplPaths, CrateId, Fun, Visibility, Path, GenericBounds, Idents,
    Function, ParamX, FunctionKind, BodyVisibility, Opaqueness, ItemKind, FunctionAttrsX,
    VarIdent,
};
use vir::ast_util::{bool_typ};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyKind;

/// Traits with special handling
#[derive(Clone, Copy, Debug)]
pub enum SpecialTrait {
    Clone,
    //PartialEq,
}

/// What to do for a given automatically-derived trait impl
#[derive(Debug)]
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
            rustc_hir::Attribute::Parsed(
                rustc_hir::attrs::AttributeKind::AutomaticallyDerived(_),
            ) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

pub fn modify_derived_item<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    hir_id: HirId,
    action: &AutomaticDeriveAction,
    function: &mut FunctionX,
    def_id: DefId,
) -> Result<Option<Function>, VirErr> {
    let AutomaticDeriveAction::Special(special) = action else {
        return Ok(None);
    };
    match special {
        SpecialTrait::Clone => {
            if &*function.name.path.last_segment() == "clone" {
                return clone_add_post_condition(ctxt, span, hir_id, function, def_id);
            }
        }
    }
    Ok(None)
}

fn clone_add_post_condition<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    hir_id: HirId,
    functionx: &mut FunctionX,
    def_id: DefId,
) -> Result<Option<Function>, VirErr> {
    let warn = |msg: &str| {
        ctxt.diagnostics
            .borrow_mut()
            .push(VirErrAs::Warning(crate::util::err_span_bare(span, msg.to_string())));
    };
    let warn_unexpected = || {
        warn(
            "Internal error processing this auto-derived Clone impl; Verus is not adding a specification to the clone function",
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
            ExprX::Var(functionx.ret.x.name.clone()),
        );
        let eq_expr = SpannedTyped::new(
            &self_var.span,
            &vir::ast_util::bool_typ(),
            ExprX::Binary(BinaryOp::Eq(Mode::Spec), ret_var.clone(), self_var.clone()),
        );

        let eq_expr = cleanup_span_ids(ctxt, span, hir_id, &eq_expr);
        functionx.ensure.0 = Arc::new(vec![eq_expr]);
        Ok(None)
    } else {
        let ExprX::Block(_, Some(expr)) = &body.x else { unreachable!() };
        let module_path = functionx.name.path.pop_segment().pop_segment();
        let spec_fn_name = vir::def::clone_spec_fn_name(&functionx.name.path.pop_segment());
        let other_ident = vir::ast_util::air_unique_var(vir::def::OTHER_PARAM_VALUE);
        let other_var = SpannedTyped::new(
            &expr.span,
            &functionx.params[0].x.typ,
            ExprX::Var(other_ident.clone()));
        let rel = match to_relation(expr, &other_var) {
            Ok(rel) => rel,
            Err(()) => { warn_unexpected(); return Ok(None); }
        };
        let rel = cleanup_span_ids(ctxt, span, hir_id, &rel);
        let (datatype_visibility, datatype_body_visibility) = get_visibilities(&expr.span, ctxt, def_id)?;
        let function = mk_spec_function(&expr.span,
            spec_fn_name,
            datatype_visibility.clone(),
            datatype_body_visibility,
            &module_path,
            &functionx.typ_params,
            &functionx.typ_bounds,
            &functionx.params[0].x.typ,
            &functionx.params[0].x.name,
            &other_ident,
            &rel);

        let typ_args: Vec<_> = functionx.typ_params.iter()
            .map(|param| { Arc::new(TypX::TypParam(param.clone())) })
            .collect();
        let ct = CallTarget::Fun(CallTargetKind::Static, function.x.name.clone(),
            Arc::new(typ_args), Arc::new(vec![]), CallTargetAttrs { autospec: AutospecUsage::Final, const_var: false, assume_external_allowed: false });
        let self_var = SpannedTyped::new(
            &expr.span,
            &functionx.params[0].x.typ,
            ExprX::Var(functionx.params[0].x.name.clone()));
        let ret_var = SpannedTyped::new(
            &expr.span,
            &functionx.ret.x.typ,
            ExprX::Var(functionx.ret.x.name.clone()));
        let args = Arc::new(vec![self_var, ret_var]);
        let ens_expr = SpannedTyped::new(&expr.span, &bool_typ(), ExprX::Call(ct, args, None));
        
        let ens_expr = cleanup_span_ids(ctxt, span, hir_id, &ens_expr);
        functionx.ensure.0 = Arc::new(vec![ens_expr]);
        // TODO: Right now trait functions are always public, but the datatype might be private,
        // so it's impossible to make this well-formed. So we fix the visibility here, but really,
        // this should be fixed for all trait functions.
        functionx.visibility = datatype_visibility;
        Ok(Some(function))
    }
}

fn to_relation(expr: &Expr, output: &Expr) -> Result<Expr, ()> {
    match &expr.x {
        ExprX::Match(scrutinee, arms) => {
            let mut new_arms: Vec<Arm> = vec![];
            for mut arm in arms.iter().cloned() {
                let armx = Arc::make_mut(&mut arm);
                armx.x.body = to_relation(&armx.x.body, output)?;
                new_arms.push(arm);
            }
            Ok(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Match(scrutinee.clone(), Arc::new(new_arms))))
        }
        ExprX::Ctor(dt, variant_ident, binders, None) => {
            let mut conjuncts = vec![
                SpannedTyped::new(&expr.span, &bool_typ(), ExprX::UnaryOpr(
                    UnaryOpr::IsVariant { datatype: dt.clone(), variant: variant_ident.clone() },
                    output.clone())),
            ];
            for binder in binders.iter() {
                let field_of_output = SpannedTyped::new(
                    &expr.span, &binder.a.typ, ExprX::UnaryOpr(UnaryOpr::Field(FieldOpr {
                        datatype: dt.clone(),
                        variant: variant_ident.clone(),
                        field: binder.name.clone(),
                        get_variant: true,
                        check: vir::ast::VariantCheck::None,
                    }), output.clone()));
                let (clonee, impl_paths, clone_typ_arg) = match &binder.a.x {
                    ExprX::Call(CallTarget::Fun(
                        CallTargetKind::DynamicResolved { .. } | CallTargetKind::Dynamic,
                        fun, typs, impl_paths, _call_target_attrs
                    ), args, None) if fun == &vir::fun!(CrateId::Core => "clone", "Clone", "clone") =>
                    {
                        assert!(args.len() == 1);
                        (args[0].clone(), impl_paths.clone(), typs[0].clone())
                    }
                    _ => { return Err(()); }
                };
                conjuncts.push(strictly_cloned_call(
                    &clonee, &field_of_output, clone_typ_arg, impl_paths));
            }
            Ok(vir::ast_util::conjoin(&expr.span, &conjuncts))
        }
        _ => { Err(()) }
    }
}

fn strictly_cloned_call(e1: &Expr, e2: &Expr, typ: Typ, impl_paths: ImplPaths) -> Expr {
    let fun = vir::fun!(CrateId::Vstd => "pervasive", "strictly_cloned");
    let ct = CallTarget::Fun(CallTargetKind::Static, fun, Arc::new(vec![typ]), impl_paths,
        CallTargetAttrs { autospec: AutospecUsage::Final, const_var: false, assume_external_allowed: false });
    let args = Arc::new(vec![e1.clone(), e2.clone()]);
    SpannedTyped::new(&e1.span, &bool_typ(), ExprX::Call(ct, args, None))
}

fn mk_spec_function(
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
    body: &Expr,
) -> Function {
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
    vir::def::Spanned::new(span.clone(), FunctionX {
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
        ret: ret_param,
        ens_has_return: false,
        require: Arc::new(vec![]),
        ensure: (Arc::new(vec![]), Arc::new(vec![])),
        returns: None,
        decrease: Arc::new(vec![]),
        decrease_when: None,
        decrease_by: None,
        fndef_axioms: None,
        mask_spec: None,
        unwind_spec: None,
        item_kind: ItemKind::Function,
        attrs: Arc::new(FunctionAttrsX {
            uses_ghost_blocks: true,
            inline: false,
            hidden: Arc::new(vec![]),
            broadcast_forall: false,
            broadcast_forall_only: false,
            no_auto_trigger: false,
            auto_ext_equal: vir::ast::AutoExtEqual { assert: false, assert_by: false, ensures: false, invariant: false },
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
        }),
        body: Some(body.clone()),
        extra_dependencies: vec![],
        async_ret: None,
    })
}

/// Given the DefId of the clone impl, returns:
/// (i) visiblity of the datatype
/// (ii) visiblity of the interior of the datatype
fn get_visibilities<'tcx>(span: &vir::messages::Span, ctxt: &Context<'tcx>, def_id: DefId) -> Result<(Visibility, Visibility), VirErr> {
    let fn_sig = ctxt.tcx.fn_sig(def_id).skip_binder();
    let self_ty = fn_sig.output().skip_binder();
    let adt_def = match self_ty.kind() {
        TyKind::Adt(adt_def, _args) => adt_def,
        _ => {
            return Err(vir::messages::error(span, "Verus Internal Error: handling auto-derive Clone, expected TyKind::Adt"));
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

// TODO better place for this
fn cleanup_span_ids<'tcx>(ctxt: &Context<'tcx>, span: Span, hir_id: HirId, expr: &Expr) -> Expr {
    vir::ast_visitor::map_expr_place_visitor(
        expr,
        &|e: &Expr| {
            let e = ctxt.spans.spanned_typed_new(span, &e.typ, e.x.clone());
            let mut erasure_info = ctxt.erasure_info.borrow_mut();
            erasure_info.hir_vir_ids.push((hir_id, e.span.id));
            Ok(e)
        },
        &|p: &Place| {
            let p = ctxt.spans.spanned_typed_new(span, &p.typ, p.x.clone());
            let mut erasure_info = ctxt.erasure_info.borrow_mut();
            erasure_info.hir_vir_ids.push((hir_id, p.span.id));
            Ok(p)
        },
    )
    .unwrap()
}
