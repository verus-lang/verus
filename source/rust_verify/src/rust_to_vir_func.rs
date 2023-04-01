use crate::attributes::{
    get_fuel, get_mode, get_publish, get_ret_mode, get_var_mode, get_verifier_attrs,
};
use crate::context::{BodyCtxt, Context};
use crate::rust_to_vir_base::{
    check_generics_bounds_fun, def_id_to_vir_path, foreign_param_to_var, mid_ty_to_vir,
};
use crate::rust_to_vir_expr::{expr_to_vir, pat_to_mut_var, ExprModifier};
use crate::util::{err_span_str, err_span_string, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{
    def::Res, Body, BodyId, Crate, FnDecl, FnHeader, FnRetTy, FnSig, Generics, ImplicitSelfKind,
    MaybeOwner, MutTy, Param, PrimTy, QPath, Ty, TyKind, Unsafety,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::{Ident, Symbol};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{
    Fun, FunX, FunctionAttrsX, FunctionKind, FunctionX, GenericBoundX, KrateX, MaskSpec, Mode,
    ParamX, Typ, TypX, VirErr,
};
use vir::def::RETURN_VALUE;

pub(crate) fn autospec_fun(path: &vir::ast::Path, method_name: String) -> vir::ast::Path {
    // turn a::b::c into a::b::method_name
    let mut pathx = (**path).clone();
    let mut segments = (*pathx.segments).clone();
    *segments.last_mut().expect("empty path") = Arc::new(method_name);
    pathx.segments = Arc::new(segments);
    Arc::new(pathx)
}

pub(crate) fn body_to_vir<'tcx>(
    ctxt: &Context<'tcx>,
    id: &BodyId,
    body: &Body<'tcx>,
    mode: Mode,
    external_body: bool,
) -> Result<vir::ast::Expr, VirErr> {
    let def = rustc_middle::ty::WithOptConstParam::unknown(id.hir_id.owner.def_id);
    let types = ctxt.tcx.typeck_opt_const_arg(def);
    let bctx =
        BodyCtxt { ctxt: ctxt.clone(), types, mode, external_body, in_ghost: mode != Mode::Exec };
    expr_to_vir(&bctx, &body.value, ExprModifier::REGULAR)
}

fn check_fn_decl<'tcx>(
    tcx: TyCtxt<'tcx>,
    decl: &'tcx FnDecl<'tcx>,
    attrs: &[Attribute],
    mode: Mode,
    output_ty: rustc_middle::ty::Ty<'tcx>,
) -> Result<Option<(Typ, Mode)>, VirErr> {
    let FnDecl { inputs: _, output, c_variadic, implicit_self, lifetime_elision_allowed: _ } = decl;
    unsupported_unless!(!c_variadic, "c_variadic");
    match implicit_self {
        rustc_hir::ImplicitSelfKind::None => {}
        rustc_hir::ImplicitSelfKind::Imm => {}
        rustc_hir::ImplicitSelfKind::ImmRef => {}
        rustc_hir::ImplicitSelfKind::MutRef => {}
        _ => unsupported!("implicit_self"),
    }
    match output {
        rustc_hir::FnRetTy::DefaultReturn(_) => Ok(None),
        // REVIEW: there's no attribute syntax on return types,
        // so we always return the default mode.
        // The current workaround is to return a struct if the default doesn't work.
        rustc_hir::FnRetTy::Return(_ty) => {
            let typ = mid_ty_to_vir(tcx, &output_ty, false);
            Ok(Some((typ, get_ret_mode(mode, attrs))))
        }
    }
}

fn sig_uses_self_param<'tcx>(sig: &'tcx FnSig<'tcx>) -> bool {
    match &sig.decl.implicit_self {
        ImplicitSelfKind::None => false,
        ImplicitSelfKind::Imm
        | ImplicitSelfKind::Mut
        | ImplicitSelfKind::ImmRef
        | ImplicitSelfKind::MutRef => true,
    }
}

pub(crate) fn find_body_krate<'tcx>(
    krate: &'tcx Crate<'tcx>,
    body_id: &BodyId,
) -> &'tcx Body<'tcx> {
    let owner = krate.owners[body_id.hir_id.owner.def_id];
    if let MaybeOwner::Owner(owner) = owner {
        if let Some(body) = owner.nodes.bodies.get(&body_id.hir_id.local_id) {
            return body;
        }
    }
    panic!("Body not found");
}

fn find_body<'tcx>(ctxt: &Context<'tcx>, body_id: &BodyId) -> &'tcx Body<'tcx> {
    find_body_krate(ctxt.krate, body_id)
}

fn check_new_strlit<'tcx>(ctx: &Context<'tcx>, sig: &'tcx FnSig<'tcx>) -> Result<(), VirErr> {
    let (decl, span) = match sig {
        FnSig { decl, span, .. } => (decl, span),
    };

    let sig_span = span;
    let expected_input_num = 1;

    if decl.inputs.len() != expected_input_num {
        return err_span_string(*sig_span, format!("Expected one argument to new_strlit"));
    }

    let (kind, span) = match &decl.inputs[0].kind {
        TyKind::Ref(_, MutTy { ty, mutbl }) => (&ty.kind, ty.span),
        _ => {
            dbg!(&decl.inputs[0]);
            return err_span_string(decl.inputs[0].span, format!("expected a str"));
        }
    };

    let (res, span) = match kind {
        TyKind::Path(QPath::Resolved(_, path)) => (path.res, path.span),
        _ => return err_span_string(span, format!("expected str")),
    };

    if res != Res::PrimTy(PrimTy::Str) {
        return err_span_string(span, format!("expected a str"));
    }

    let (kind, span) = match decl.output {
        FnRetTy::Return(Ty { hir_id: _, kind, span }) => (kind, span),
        _ => return err_span_string(*sig_span, format!("expected a return type of StrSlice")),
    };

    let (res, span) = match kind {
        TyKind::Path(QPath::Resolved(_, path)) => (path.res, path.span),
        _ => return err_span_string(*span, format!("expected a StrSlice")),
    };

    let id = match res {
        Res::Def(_, id) => id,
        _ => return err_span_string(span, format!("")),
    };

    if !ctx.tcx.is_diagnostic_item(Symbol::intern("pervasive::string::StrSlice"), id) {
        return err_span_string(span, format!("expected a StrSlice"));
    }
    Ok(())
}

pub(crate) fn check_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    id: rustc_span::def_id::DefId,
    kind: FunctionKind,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    sig: &'tcx FnSig<'tcx>,
    trait_path: Option<vir::ast::Path>,
    // (impl generics, impl def_id)
    self_generics: Option<(&'tcx Generics, rustc_span::def_id::DefId)>,
    generics: &'tcx Generics,
    body_id: &BodyId,
) -> Result<Option<Fun>, VirErr> {
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = Arc::new(FunX { path: path.clone(), trait_path: trait_path.clone() });

    let vattrs = get_verifier_attrs(attrs)?;

    if vattrs.external {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        erasure_info.external_functions.push(name);
        return Ok(None);
    }

    let is_new_strlit =
        ctxt.tcx.is_diagnostic_item(Symbol::intern("pervasive::string::new_strlit"), id);

    let mode = get_mode(Mode::Exec, attrs);

    let self_typ_params = if let Some((cg, impl_def_id)) = self_generics {
        Some(check_generics_bounds_fun(ctxt.tcx, cg, impl_def_id)?)
    } else {
        None
    };

    let fn_sig = ctxt.tcx.fn_sig(id);
    // REVIEW: rustc docs refer to skip_binder as "dangerous"
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs();

    let ret_typ_mode = match sig {
        FnSig {
            header: FnHeader { unsafety, constness: _, asyncness: _, abi: _ },
            decl,
            span: _,
        } => {
            unsupported_err_unless!(*unsafety == Unsafety::Normal, sig.span, "unsafe");
            check_fn_decl(ctxt.tcx, decl, attrs, mode, fn_sig.output())?
        }
    };

    if is_new_strlit {
        check_new_strlit(&ctxt, sig)?;
    }

    if is_new_strlit {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        unsupported_err_unless!(
            vattrs.external_body,
            sig.span,
            "StrSlice::new must be external_body"
        );

        erasure_info.ignored_functions.push((id, sig.span.data()));
        erasure_info.external_functions.push(name);
        return Ok(None);
    }

    let sig_typ_bounds = check_generics_bounds_fun(ctxt.tcx, generics, id)?;
    let fuel = get_fuel(&vattrs);

    let body = find_body(ctxt, body_id);
    let Body { params, value: _, generator_kind } = body;
    let mut vir_params: Vec<(vir::ast::Param, Option<Mode>)> = Vec::new();

    assert!(params.len() == inputs.len());
    for (param, input) in params.iter().zip(inputs.iter()) {
        let Param { hir_id, pat, ty_span: _, span } = param;

        // is_mut_var: means a parameter is like `mut x: X` (unsupported)
        // is_mut: means a parameter is like `x: &mut X` or `x: Tracked<&mut X>`

        let (is_mut_var, name) = pat_to_mut_var(pat);
        if is_mut_var {
            return err_span_string(
                *span,
                format!(
                    "Verus does not support `mut` arguments (try writing `let mut param = param;` in the body of the function)"
                ),
            );
        }

        let name = Arc::new(name);
        let param_mode = get_var_mode(mode, ctxt.tcx.hir().attrs(*hir_id));
        let is_ref_mut = is_mut_ty(ctxt, *input);
        if is_ref_mut.is_some() && mode == Mode::Spec {
            return err_span_string(
                *span,
                format!("&mut argument not allowed for #[verifier::spec] functions"),
            );
        }

        let typ = mid_ty_to_vir(ctxt.tcx, is_ref_mut.map(|(t, _)| t).unwrap_or(input), false);

        let is_mut = is_ref_mut.is_some();

        let vir_param = ctxt.spanned_new(
            *span,
            ParamX { name, typ, mode: param_mode, is_mut, unwrapped_info: None },
        );
        vir_params.push((vir_param, is_ref_mut.map(|(_, m)| m).flatten()));
    }

    match generator_kind {
        None => {}
        _ => {
            unsupported_err!(sig.span, "generator_kind", generator_kind);
        }
    }

    let mut vir_body = body_to_vir(ctxt, body_id, body, mode, vattrs.external_body)?;

    let header = vir::headers::read_header(&mut vir_body)?;
    match (&kind, header.no_method_body) {
        (FunctionKind::TraitMethodDecl { .. }, true) => {}
        (FunctionKind::TraitMethodDecl { .. }, false) => {
            return err_span_str(
                sig.span,
                "trait method declaration body must end with call to no_method_body()",
            );
        }
        (_, false) => {}
        (_, true) => {
            return err_span_str(
                sig.span,
                "no_method_body can only appear in trait method declarations",
            );
        }
    }
    if mode == Mode::Spec && (header.require.len() + header.ensure.len()) > 0 {
        return err_span_str(sig.span, "spec functions cannot have requires/ensures");
    }
    if mode != Mode::Spec && header.recommend.len() > 0 {
        return err_span_str(sig.span, "non-spec functions cannot have recommends");
    }
    if header.ensure.len() > 0 {
        match (&header.ensure_id_typ, ret_typ_mode.as_ref()) {
            (None, None) => {}
            (None, Some(_)) => {
                return err_span_str(sig.span, "ensures clause must be a closure");
            }
            (Some(_), None) => {
                return err_span_str(sig.span, "ensures clause cannot be a closure");
            }
            (Some((_, typ)), Some((ret_typ, _))) => {
                if !vir::ast_util::types_equal(&typ, &ret_typ) {
                    return err_span_string(
                        sig.span,
                        format!(
                            "return type is {:?}, but ensures expects type {:?}",
                            &ret_typ, &typ
                        ),
                    );
                }
            }
        }
    }

    use vir::ast::UnwrapParameter;
    let mut all_param_names: Vec<vir::ast::Ident> = Vec::new();
    let mut all_param_name_set: HashSet<vir::ast::Ident> = HashSet::new();
    let mut unwrap_param_map: HashMap<vir::ast::Ident, UnwrapParameter> = HashMap::new();
    for unwrap in header.unwrap_parameters.iter() {
        all_param_names.push(unwrap.inner_name.clone());
        unwrap_param_map.insert(unwrap.outer_name.clone(), unwrap.clone());
    }
    for (param, unwrap_mut) in vir_params.iter_mut() {
        all_param_names.push(param.x.name.clone());
        if let Some(unwrap) = unwrap_param_map.get(&param.x.name) {
            if mode != Mode::Exec {
                return err_span_str(
                    sig.span,
                    "only exec functions can use Ghost(x) or Tracked(x) parameters",
                );
            }
            let mut paramx = param.x.clone();
            paramx.name = unwrap.inner_name.clone();
            paramx.unwrapped_info = Some((unwrap.mode, unwrap.outer_name.clone()));
            *param = vir::def::Spanned::new(param.span.clone(), paramx);
        } else if unwrap_mut.is_some() {
            return err_span_string(
                sig.span,
                format!("parameter {} must be unwrapped", &param.x.name),
            );
        }
    }
    for name in all_param_names.iter() {
        if all_param_name_set.contains(name) {
            return err_span_string(sig.span, format!("duplicate parameter name {}", name));
        }
        all_param_name_set.insert(name.clone());
    }
    let params: vir::ast::Params = Arc::new(vir_params.into_iter().map(|(p, _)| p).collect());

    let (ret_name, ret_typ, ret_mode) = match (header.ensure_id_typ, ret_typ_mode) {
        (None, None) => {
            (Arc::new(RETURN_VALUE.to_string()), Arc::new(TypX::Tuple(Arc::new(vec![]))), mode)
        }
        (None, Some((typ, mode))) => (Arc::new(RETURN_VALUE.to_string()), typ, mode),
        (Some((x, _)), Some((typ, mode))) => (x, typ, mode),
        _ => panic!("internal error: ret_typ"),
    };
    let ret = ctxt.spanned_new(
        sig.span,
        ParamX {
            name: ret_name,
            typ: ret_typ,
            mode: ret_mode,
            is_mut: false,
            unwrapped_info: None,
        },
    );
    let typ_bounds = {
        let mut typ_bounds: Vec<(vir::ast::Ident, vir::ast::GenericBound)> = Vec::new();
        if let FunctionKind::TraitMethodDecl { .. } = kind {
            let bound = GenericBoundX::Traits(vec![]);
            typ_bounds.push((vir::def::trait_self_type_param(), Arc::new(bound)));
        }
        if let Some(self_typ_params) = self_typ_params {
            typ_bounds.append(&mut (*self_typ_params).clone());
        }
        typ_bounds.extend_from_slice(&sig_typ_bounds[..]);
        Arc::new(typ_bounds)
    };
    let publish = get_publish(&vattrs);
    let autospec = vattrs.autospec.map(|method_name| {
        let path = autospec_fun(&path, method_name.clone());
        Arc::new(FunX { path, trait_path: trait_path.clone() })
    });

    if vattrs.nonlinear && vattrs.spinoff_prover {
        return err_span_str(
            sig.span,
            "#[verifier(spinoff_prover)] is implied for assert by nonlinear_arith",
        );
    }
    let fattrs = FunctionAttrsX {
        uses_ghost_blocks: vattrs.verus_macro,
        inline: vattrs.inline,
        hidden: Arc::new(header.hidden),
        custom_req_err: vattrs.custom_req_err,
        no_auto_trigger: vattrs.no_auto_trigger,
        broadcast_forall: vattrs.broadcast_forall,
        bit_vector: vattrs.bit_vector,
        autoview: vattrs.autoview,
        autospec,
        atomic: vattrs.atomic,
        integer_ring: vattrs.integer_ring,
        is_decrease_by: vattrs.decreases_by,
        check_recommends: vattrs.check_recommends,
        nonlinear: vattrs.nonlinear,
        spinoff_prover: vattrs.spinoff_prover,
        memoize: vattrs.memoize,
    };

    let mut recommend: Vec<vir::ast::Expr> = (*header.recommend).clone();
    if let Some(decrease_when) = &header.decrease_when {
        // Automatically add decrease_when to recommends
        recommend.push(decrease_when.clone());
    }

    // This function is marked 'private' at the source level to prevent the user from
    // calling it. But we translate things to point to it internally, so we need to
    // mark it non-private in order to avoid errors down the line.
    let mut visibility = visibility;
    if path == vir::def::exec_nonstatic_call_path(&ctxt.vstd_crate_name) {
        visibility.restricted_to = None;
    }

    if trait_path.is_some() && sig_uses_self_param(sig) {
        let self_mode = params[0].x.mode;
        if mode != self_mode {
            // It's hard for erase.rs to support mode != param_mode (we'd have to erase self),
            // so we currently disallow it:
            return err_span_str(
                sig.span,
                &format!(
                    "self has mode {}, function has mode {} -- these cannot be different",
                    self_mode, mode
                ),
            );
        }
    }

    let func = FunctionX {
        name: name.clone(),
        kind,
        visibility,
        mode,
        fuel,
        typ_bounds,
        params,
        ret,
        require: if mode == Mode::Spec { Arc::new(recommend) } else { header.require },
        ensure: header.ensure,
        decrease: header.decrease,
        decrease_when: header.decrease_when,
        decrease_by: header.decrease_by,
        broadcast_forall: None,
        mask_spec: header.invariant_mask,
        is_const: false,
        publish,
        attrs: Arc::new(fattrs),
        body: if vattrs.external_body || header.no_method_body { None } else { Some(vir_body) },
        extra_dependencies: header.extra_dependencies,
    };

    let function = ctxt.spanned_new(sig.span, func);
    vir.functions.push(function);
    Ok(Some(name))
}

// &mut T => Some(T, None)
// Ghost<&mut T> => Some(T, Some(Spec))
// Tracked<&mut T> => Some(T, Some(Proof))
// _ => None
fn is_mut_ty<'tcx>(
    ctxt: &Context<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<(&'tcx rustc_middle::ty::Ty<'tcx>, Option<Mode>)> {
    use rustc_middle::ty::*;
    match ty.kind() {
        TyKind::Ref(_, tys, rustc_ast::Mutability::Mut) => Some((tys, None)),
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let did = adt_def_data.did;
            let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(ctxt.tcx, did));
            let is_ghost = def_name == "builtin::Ghost" && args.len() == 1;
            let is_tracked = def_name == "builtin::Tracked" && args.len() == 1;
            if is_ghost || is_tracked {
                if let subst::GenericArgKind::Type(t) = args[0].unpack() {
                    if let Some((inner, None)) = is_mut_ty(ctxt, t) {
                        let mode = if is_ghost { Mode::Spec } else { Mode::Proof };
                        return Some((inner, Some(mode)));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

pub(crate) fn check_item_const<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    span: Span,
    id: rustc_span::def_id::DefId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    typ: &Typ,
    body_id: &BodyId,
) -> Result<(), VirErr> {
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = Arc::new(FunX { path, trait_path: None });
    let mode = get_mode(Mode::Exec, attrs);
    let vattrs = get_verifier_attrs(attrs)?;
    let fuel = get_fuel(&vattrs);
    if vattrs.external {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        erasure_info.external_functions.push(name);
        return Ok(());
    }
    let body = find_body(ctxt, body_id);
    let vir_body = body_to_vir(ctxt, body_id, body, mode, vattrs.external_body)?;

    let ret_name = Arc::new(RETURN_VALUE.to_string());
    let ret = ctxt.spanned_new(
        span,
        ParamX { name: ret_name, typ: typ.clone(), mode, is_mut: false, unwrapped_info: None },
    );
    let func = FunctionX {
        name,
        kind: FunctionKind::Static,
        visibility,
        mode: Mode::Spec, // the function has mode spec; the mode attribute goes into ret.x.mode
        fuel,
        typ_bounds: Arc::new(vec![]),
        params: Arc::new(vec![]),
        ret,
        require: Arc::new(vec![]),
        ensure: Arc::new(vec![]),
        decrease: Arc::new(vec![]),
        decrease_when: None,
        decrease_by: None,
        broadcast_forall: None,
        mask_spec: MaskSpec::NoSpec,
        is_const: true,
        publish: get_publish(&vattrs),
        attrs: Default::default(),
        body: if vattrs.external_body { None } else { Some(vir_body) },
        extra_dependencies: vec![],
    };
    let function = ctxt.spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}

pub(crate) fn check_foreign_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    id: rustc_span::def_id::DefId,
    span: Span,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    decl: &'tcx FnDecl<'tcx>,
    idents: &[Ident],
    generics: &'tcx Generics,
) -> Result<(), VirErr> {
    let mode = get_mode(Mode::Exec, attrs);

    let fn_sig = ctxt.tcx.fn_sig(id);
    // REVIEW: rustc docs refer to skip_binder as "dangerous"
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs();

    let ret_typ_mode = check_fn_decl(ctxt.tcx, decl, attrs, mode, fn_sig.output())?;
    let typ_bounds = check_generics_bounds_fun(ctxt.tcx, generics, id)?;
    let vattrs = get_verifier_attrs(attrs)?;
    let fuel = get_fuel(&vattrs);
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();

    assert!(idents.len() == inputs.len());
    for (param, input) in idents.iter().zip(inputs.iter()) {
        let name = Arc::new(foreign_param_to_var(param));
        let is_mut = is_mut_ty(ctxt, *input);
        let typ = mid_ty_to_vir(ctxt.tcx, is_mut.map(|(t, _)| t).unwrap_or(input), false);
        // REVIEW: the parameters don't have attributes, so we use the overall mode
        let vir_param = ctxt.spanned_new(
            param.span,
            ParamX { name, typ, mode, is_mut: is_mut.is_some(), unwrapped_info: None },
        );
        vir_params.push(vir_param);
    }
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = Arc::new(FunX { path, trait_path: None });
    let params = Arc::new(vir_params);
    let (ret_typ, ret_mode) = match ret_typ_mode {
        None => (Arc::new(TypX::Tuple(Arc::new(vec![]))), mode),
        Some((typ, mode)) => (typ, mode),
    };
    let ret_param = ParamX {
        name: Arc::new(RETURN_VALUE.to_string()),
        typ: ret_typ,
        mode: ret_mode,
        is_mut: false,
        unwrapped_info: None,
    };
    let ret = ctxt.spanned_new(span, ret_param);
    let func = FunctionX {
        name,
        kind: FunctionKind::Static,
        visibility,
        fuel,
        mode,
        typ_bounds,
        params,
        ret,
        require: Arc::new(vec![]),
        ensure: Arc::new(vec![]),
        decrease: Arc::new(vec![]),
        decrease_when: None,
        decrease_by: None,
        broadcast_forall: None,
        mask_spec: MaskSpec::NoSpec,
        is_const: false,
        publish: None,
        attrs: Default::default(),
        body: None,
        extra_dependencies: vec![],
    };
    let function = ctxt.spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}
