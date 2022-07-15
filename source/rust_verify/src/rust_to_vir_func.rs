use crate::attributes::{
    get_fuel, get_mode, get_publish, get_ret_mode, get_var_mode, get_verifier_attrs,
};
use crate::context::{BodyCtxt, Context};
use crate::rust_to_vir_base::{
    check_generics_bounds_fun, def_id_to_vir_path, ident_to_var, ty_to_vir,
};
use crate::rust_to_vir_expr::{expr_to_vir, pat_to_var, ExprModifier};
use crate::util::{err_span_str, err_span_string, spanned_new, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{Body, BodyId, FnDecl, FnHeader, FnSig, Generics, Param, TyKind, Unsafety, QPath, PrimTy, def::Res, FnRetTy, Ty};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::{Ident, Symbol};
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    Fun, FunX, FunctionAttrsX, FunctionKind, FunctionX, GenericBoundX, KrateX, MaskSpec, Mode,
    ParamX, Typ, TypX, VirErr,
};
use vir::def::RETURN_VALUE;

pub(crate) fn body_to_vir<'tcx>(
    ctxt: &Context<'tcx>,
    id: &BodyId,
    body: &Body<'tcx>,
    mode: Mode,
    external_body: bool,
) -> Result<vir::ast::Expr, VirErr> {
    let def = rustc_middle::ty::WithOptConstParam::unknown(id.hir_id.owner);
    let types = ctxt.tcx.typeck_opt_const_arg(def);
    let bctx = BodyCtxt { ctxt: ctxt.clone(), types, mode, external_body };
    expr_to_vir(&bctx, &body.value, ExprModifier::REGULAR)
}

fn is_self_or_self_ref(span: Span, ty: &rustc_hir::Ty) -> Result<bool, VirErr> {
    match ty.kind {
        rustc_hir::TyKind::Rptr(_, rustc_hir::MutTy { ty: rty, mutbl: _, .. }) => {
            is_self_or_self_ref(span, rty)
        }
        rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(None, path)) => match path.res {
            rustc_hir::def::Res::SelfTy(Some(_), _impl_def_id) => Ok(true),
            rustc_hir::def::Res::SelfTy(None, _) => Ok(true),
            _ => Ok(false),
        },
        _ => Ok(false),
    }
}

fn check_fn_decl<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_span: &Span,
    decl: &'tcx FnDecl<'tcx>,
    self_typ: Option<Typ>,
    attrs: &[Attribute],
    mode: Mode,
) -> Result<Option<(Typ, Mode)>, VirErr> {
    let FnDecl { inputs: _, output, c_variadic, implicit_self } = decl;
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
        rustc_hir::FnRetTy::Return(ty) => {
            let typ = if is_self_or_self_ref(*sig_span, &ty)? {
                self_typ.expect("a param is Self, so this must be an impl")
            } else {
                ty_to_vir(tcx, ty)
            };
            Ok(Some((typ, get_ret_mode(mode, attrs))))
        }
    }
}

fn find_body<'tcx>(ctxt: &Context<'tcx>, body_id: &BodyId) -> &'tcx Body<'tcx> {
    let owner = ctxt.krate.owners[body_id.hir_id.owner].as_ref();
    if let Some(owner) = owner {
        if let Some(body) = owner.nodes.bodies.get(&body_id.hir_id.local_id) {
            return body;
        }
    }
    panic!("Body not found");
}


fn check_strslice_new<'tcx>(sig: &'tcx FnSig<'tcx>) -> Result<(), VirErr> {

    let (decl, span) = match sig {
        FnSig { header: _, decl, span } => (decl, span),
    };

    let sig_span = span;
    
    let expected_input_num = 1;
    if decl.inputs.len() != expected_input_num {
        crate::err!(*span, format!("Expected {} input for StrSlice::new but got {}", expected_input_num, decl.inputs.len()));
    }


    let (kind, span) = match &decl.inputs[0].kind {
        TyKind::Rptr(_, muty) => (&muty.ty.kind, muty.ty.span),
        _ => crate::err!(decl.inputs[0].span, format!("Expected a Rptr") ),
    };

    
    

    let (res, span) = match kind {
        TyKind::Path( QPath::Resolved(_, path)) => (path.res, path.span),
        _ => crate::err!(span, format!("Expected a resolved path"))
    };

    if res != Res::PrimTy(PrimTy::Str) {
        crate::err!(span, format!("Expected primitive type str"));
    }
    
    
    let (kind, span) = match decl.output {
        FnRetTy::Return( Ty {hir_id: _, kind, span} ) => (kind, span),
        _ => crate::err!(*sig_span, format!(""))
    };



    let (res, span) = match kind {
        TyKind::Path( QPath::Resolved(_, path)) => (path.res, path.span), 
        _ => crate::err!(*span, format!("Expected a resolved path"))
    };

    match res {
        Res::SelfTy(_, _) => {}, 
        _ => crate::err!(span, format!("Expected a Self, while StrSlice<'a> is a valid return type, this isn't suppported at the moment"))
    };
    Ok(())
}

pub(crate) fn check_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    self_typ: Option<Typ>,
    id: rustc_span::def_id::DefId,
    kind: FunctionKind,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    sig: &'tcx FnSig<'tcx>,
    trait_path: Option<vir::ast::Path>,
    self_generics: Option<&'tcx Generics>,
    generics: &'tcx Generics,
    body_id: &BodyId,
) -> Result<Option<Fun>, VirErr> {
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let is_str_new = ctxt.tcx.is_diagnostic_item(Symbol::intern("pervasive::string::StrSlice::new"), id);

    let name = Arc::new(FunX { path: path.clone(), trait_path });
    let mode = get_mode(Mode::Exec, attrs);
    let self_typ_params = if let Some(cg) = self_generics {
        Some(check_generics_bounds_fun(ctxt.tcx, cg)?)
    } else {
        None
    };
    let self_typ = match (self_typ, &kind) {
        (Some(t), _) => Some(t),
        (_, FunctionKind::TraitMethodDecl { .. }) => {
            Some(Arc::new(TypX::TypParam(vir::def::trait_self_type_param())))
        }
        (_, FunctionKind::Static) => None,
        _ => panic!("missing self type for kind {:?}", &kind),
    };
    let ret_typ_mode = match sig {
        FnSig {
            header: FnHeader { unsafety, constness: _, asyncness: _, abi: _ },
            decl,
            span: _,
        } => {
            unsupported_err_unless!(*unsafety == Unsafety::Normal, sig.span, "unsafe");
            check_fn_decl(ctxt.tcx, &sig.span, decl, self_typ.clone(), attrs, mode)?
        }
    };
    let sig_typ_bounds = check_generics_bounds_fun(ctxt.tcx, generics)?;
    let vattrs = get_verifier_attrs(attrs)?;
    let fuel = get_fuel(&vattrs);
    
    if is_str_new {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        unsupported_err_unless!(
            vattrs.external_body,
            sig.span,
            "StrSlice::new must be external_body"
        ); 

        check_strslice_new(sig)?;
        erasure_info.ignored_functions.push(sig.span.data());
        erasure_info.external_functions.push(name);
        return Ok(None);
    }

    if vattrs.external {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        erasure_info.external_functions.push(name);
        return Ok(None);
    }
    let body = find_body(ctxt, body_id);
    let Body { params, value: _, generator_kind } = body;
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    

    for (param, input) in params.iter().zip(sig.decl.inputs.iter()) {
        let Param { hir_id, pat, ty_span: _, span } = param;
        let name = Arc::new(pat_to_var(pat));
        let param_mode = get_var_mode(mode, ctxt.tcx.hir().attrs(*hir_id));
        let is_mut = is_mut_ty(&input);
        if is_mut.is_some() && mode == Mode::Spec {
            return err_span_string(
                *span,
                format!("&mut argument not allowed for #[spec] functions"),
            );
        }
        let (typ, is_mut) = if is_self_or_self_ref(*span, &input)? {
            (self_typ.clone().expect("a param is Self, so this must be an impl"), is_mut.is_some())
        } else {
            (ty_to_vir(ctxt.tcx, is_mut.unwrap_or(&input)), is_mut.is_some())
        };
        let vir_param = spanned_new(*span, ParamX { name, typ, mode: param_mode, is_mut });
        vir_params.push(vir_param);
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
    let params = Arc::new(vir_params);
    let (ret_name, ret_typ, ret_mode) = match (header.ensure_id_typ, ret_typ_mode) {
        (None, None) => {
            (Arc::new(RETURN_VALUE.to_string()), Arc::new(TypX::Tuple(Arc::new(vec![]))), mode)
        }
        (None, Some((typ, mode))) => (Arc::new(RETURN_VALUE.to_string()), typ, mode),
        (Some((x, _)), Some((typ, mode))) => (x, typ, mode),
        _ => panic!("internal error: ret_typ"),
    };
    let ret = spanned_new(
        sig.span,
        ParamX { name: ret_name, typ: ret_typ, mode: ret_mode, is_mut: false },
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
    let fattrs = FunctionAttrsX {
        uses_ghost_blocks: vattrs.verus_macro,
        hidden: Arc::new(header.hidden),
        custom_req_err: vattrs.custom_req_err,
        no_auto_trigger: vattrs.no_auto_trigger,
        broadcast_forall: vattrs.broadcast_forall,
        bit_vector: vattrs.bit_vector,
        autoview: vattrs.autoview,
        atomic: vattrs.atomic,
        integer_ring: vattrs.integer_ring,
        is_decrease_by: vattrs.decreases_by,
        check_recommends: vattrs.check_recommends,
        nonlinear: vattrs.nonlinear,
        spinoff_prover: vattrs.spinoff_prover,
    };

    let mut recommend: Vec<vir::ast::Expr> = (*header.recommend).clone();
    if let Some(decrease_when) = &header.decrease_when {
        // Automatically add decrease_when to recommends
        recommend.push(decrease_when.clone());
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
        is_string_literal: false,
        publish,
        attrs: Arc::new(fattrs),
        body: if vattrs.external_body || header.no_method_body { None } else { Some(vir_body) },
        extra_dependencies: header.extra_dependencies,
    };
    let function = spanned_new(sig.span, func);
    vir.functions.push(function);
    Ok(Some(name))
}

fn is_mut_ty<'tcx>(ty: &'tcx rustc_hir::Ty<'tcx>) -> Option<&'tcx rustc_hir::Ty<'tcx>> {
    let rustc_hir::Ty { kind, .. } = ty;
    match kind {
        rustc_hir::TyKind::Rptr(
            _,
            rustc_hir::MutTy { ty: tys, mutbl: rustc_ast::Mutability::Mut },
        ) => Some(tys),
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

    let is_string_literal = match &vir_body.x {
        vir::ast::ExprX::Const(vir::ast::Constant::StrSlice(val, _)) => {
            let mut global_strings = ctxt.global_strings.borrow_mut();
            global_strings.insert(id, val.clone());
            true
        }, 
        _ => false
    };
    
    let ret_name = Arc::new(RETURN_VALUE.to_string());
    let ret =
        spanned_new(span, ParamX { name: ret_name, typ: typ.clone(), mode: mode, is_mut: false });
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
        is_string_literal,
        publish: get_publish(&vattrs),
        attrs: Default::default(),
        body: if vattrs.external_body { None } else { Some(vir_body) },
        extra_dependencies: vec![],
    };
    let function = spanned_new(span, func);
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
    let ret_typ_mode = check_fn_decl(ctxt.tcx, &span, decl, None, attrs, mode)?;
    let typ_bounds = check_generics_bounds_fun(ctxt.tcx, generics)?;
    let vattrs = get_verifier_attrs(attrs)?;
    let fuel = get_fuel(&vattrs);
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    for (param, input) in idents.iter().zip(decl.inputs.iter()) {
        let name = Arc::new(ident_to_var(param));
        let is_mut = is_mut_ty(input);
        let typ = ty_to_vir(ctxt.tcx, is_mut.unwrap_or(input));
        // REVIEW: the parameters don't have attributes, so we use the overall mode
        let vir_param =
            spanned_new(param.span, ParamX { name, typ, mode, is_mut: is_mut.is_some() });
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
    };
    let ret = spanned_new(span, ret_param);
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
        is_string_literal: false,
        publish: None,
        attrs: Default::default(),
        body: None,
        extra_dependencies: vec![],
    };
    let function = spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}
