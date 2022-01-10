use crate::context::{BodyCtxt, Context};
use crate::rust_to_vir_base::{
    check_generics, check_generics_bounds, def_id_to_vir_path, def_to_path_ident, get_fuel,
    get_mode, get_ret_mode, get_var_mode, get_verifier_attrs, ident_to_var, ty_to_vir,
};
use crate::rust_to_vir_expr::{expr_to_vir, pat_to_var};
use crate::util::{err_span_str, err_span_string, spanned_new, unsupported_err_span, vec_map};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{Body, BodyId, FnDecl, FnHeader, FnSig, Generics, Param, Unsafety};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{FunX, FunctionAttrsX, FunctionX, KrateX, Mode, ParamX, Typ, TypX, VirErr};
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
    expr_to_vir(&bctx, &body.value)
}

fn is_self_or_self_ref(span: Span, ty: &rustc_hir::Ty) -> Result<bool, VirErr> {
    match ty.kind {
        rustc_hir::TyKind::Rptr(
            _,
            rustc_hir::MutTy { ty: rty, mutbl: rustc_hir::Mutability::Not, .. },
        ) => is_self_or_self_ref(span, rty),
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
    self_path: Option<vir::ast::Path>,
    self_typ_params: Option<vir::ast::Idents>,
    attrs: &[Attribute],
    mode: Mode,
) -> Result<Option<(Typ, Mode)>, VirErr> {
    let FnDecl { inputs: _, output, c_variadic, implicit_self } = decl;
    unsupported_unless!(!c_variadic, "c_variadic");
    match implicit_self {
        rustc_hir::ImplicitSelfKind::None => {}
        rustc_hir::ImplicitSelfKind::Imm => {}
        rustc_hir::ImplicitSelfKind::ImmRef => {}
        _ => unsupported!("implicit_self"),
    }
    match output {
        rustc_hir::FnRetTy::DefaultReturn(_) => Ok(None),
        // REVIEW: there's no attribute syntax on return types,
        // so we always return the default mode.
        // The current workaround is to return a struct if the default doesn't work.
        rustc_hir::FnRetTy::Return(ty) => {
            let typ = if is_self_or_self_ref(*sig_span, &ty)? {
                let typ_args = vec_map(
                    self_typ_params.as_ref().expect("expected Self type parameters"),
                    |t| Arc::new(TypX::TypParam(t.clone())),
                );
                Arc::new(TypX::Datatype(
                    self_path.as_ref().expect("a param is Self, so this must be an impl").clone(),
                    Arc::new(typ_args),
                ))
            } else {
                ty_to_vir(tcx, ty)
            };
            Ok(Some((typ, get_ret_mode(mode, attrs))))
        }
    }
}

pub(crate) fn check_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    self_path_mode: Option<(vir::ast::Path, Mode)>,
    id: rustc_span::def_id::DefId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    sig: &'tcx FnSig<'tcx>,
    trait_path: Option<vir::ast::Path>,
    self_generics: Option<&'tcx Generics>,
    generics: &'tcx Generics,
    body_id: &BodyId,
) -> Result<(), VirErr> {
    let path = if let Some((self_path, _)) = &self_path_mode {
        let mut full_path = (**self_path).clone();
        Arc::make_mut(&mut full_path.segments).push(def_to_path_ident(ctxt.tcx, id));
        Arc::new(full_path)
    } else {
        def_id_to_vir_path(ctxt.tcx, id)
    };
    let name = Arc::new(FunX { path, trait_path });
    let mode = get_mode(Mode::Exec, attrs);
    let adt_mode_trait_impl: Option<(_, Mode)> = if let (Some(_), Some((self_path, adt_mode))) =
        (&name.trait_path, &self_path_mode)
    {
        if !vir::modes::mode_le(mode, *adt_mode) {
            return err_span_string(
                sig.span,
                format!(
                    "{} has mode {}, which must not be lower than the function's mode {} for trait impls",
                    vir::ast_util::path_as_rust_name(&self_path),
                    adt_mode,
                    mode
                ),
            );
        }
        Some((self_path, *adt_mode))
    } else {
        None
    };
    let self_typ_params = if let Some(cg) = self_generics {
        Some(check_generics(ctxt.tcx, cg, false)?)
    } else {
        None
    };
    let ret_typ_mode = match sig {
        FnSig {
            header: FnHeader { unsafety, constness: _, asyncness: _, abi: _ },
            decl,
            span: _,
        } => {
            unsupported_err_unless!(*unsafety == Unsafety::Normal, sig.span, "unsafe");
            check_fn_decl(
                ctxt.tcx,
                &sig.span,
                decl,
                self_path_mode.as_ref().map(|(self_path, _)| self_path.clone()),
                self_typ_params.clone(),
                attrs,
                mode,
            )?
        }
    };
    let sig_typ_bounds = check_generics_bounds(ctxt.tcx, generics, true)?;
    let fuel = get_fuel(attrs);
    let vattrs = get_verifier_attrs(attrs)?;
    if vattrs.external {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        erasure_info.external_functions.push(name);
        return Ok(());
    }
    let body = &ctxt.krate.bodies[body_id];
    let Body { params, value: _, generator_kind } = body;
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    for (param, input) in params.iter().zip(sig.decl.inputs.iter()) {
        let Param { hir_id, pat, ty_span: _, span } = param;
        let name = Arc::new(pat_to_var(pat));
        let param_mode = get_var_mode(mode, ctxt.tcx.hir().attrs(*hir_id));
        if let Some((self_path, adt_mode)) = &adt_mode_trait_impl {
            if !vir::modes::mode_le(param_mode, *adt_mode) {
                return err_span_string(
                    sig.span,
                    format!(
                        "{} has mode {}, which must not be lower than the paramater's mode {} for trait impls",
                        vir::ast_util::path_as_rust_name(&self_path),
                        adt_mode,
                        param_mode
                    ),
                );
            }
        }
        let typ = if is_self_or_self_ref(*span, &input)? {
            if mode != param_mode {
                // It's hard for erase.rs to support mode != param_mode (we'd have to erase self),
                // so we currently disallow it:
                return err_span_string(
                    sig.span,
                    format!(
                        "self has mode {}, function has mode {} -- these cannot be different",
                        param_mode, mode
                    ),
                );
            }
            let typ_args =
                vec_map(self_typ_params.as_ref().expect("expected Self type parameters"), |t| {
                    Arc::new(TypX::TypParam(t.clone()))
                });
            Arc::new(TypX::Datatype(
                self_path_mode
                    .as_ref()
                    .map(|(self_path, _)| self_path)
                    .expect("a param is Self, so this must be an impl")
                    .clone(),
                Arc::new(typ_args),
            ))
        } else {
            ty_to_vir(ctxt.tcx, input)
        };
        let vir_param = spanned_new(*span, ParamX { name, typ, mode: param_mode });
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
    if mode == Mode::Spec && (header.require.len() + header.ensure.len()) > 0 {
        return err_span_str(sig.span, "spec functions cannot have requires/ensures");
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
    let ret = spanned_new(sig.span, ParamX { name: ret_name, typ: ret_typ, mode: ret_mode });
    let typ_bounds = {
        let mut typ_bounds: Vec<(vir::ast::Ident, vir::ast::GenericBound)> = Vec::new();
        if let Some(self_typ_params) = self_typ_params {
            for x in self_typ_params.iter() {
                typ_bounds.push((x.clone(), Arc::new(vir::ast::GenericBoundX::None)));
            }
        }
        typ_bounds.extend_from_slice(&sig_typ_bounds[..]);
        Arc::new(typ_bounds)
    };
    let fattrs = FunctionAttrsX {
        hidden: Arc::new(header.hidden),
        custom_req_err: vattrs.custom_req_err,
        no_auto_trigger: false,
        export_as_global_forall: vattrs.export_as_global_forall,
        bit_vector: vattrs.bit_vector,
        autoview: vattrs.autoview,
    };
    let func = FunctionX {
        name,
        visibility,
        mode,
        fuel,
        typ_bounds,
        params,
        ret,
        require: header.require,
        ensure: header.ensure,
        decrease: header.decrease,
        is_abstract: vattrs.is_abstract,
        attrs: Arc::new(fattrs),
        body: if vattrs.external_body { None } else { Some(vir_body) },
    };
    let function = spanned_new(sig.span, func);
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
    let ret_typ_mode = check_fn_decl(ctxt.tcx, &span, decl, None, None, attrs, mode)?;
    let typ_bounds = check_generics_bounds(ctxt.tcx, generics, true)?;
    let fuel = get_fuel(attrs);
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    for (param, input) in idents.iter().zip(decl.inputs.iter()) {
        let name = Arc::new(ident_to_var(param));
        let typ = ty_to_vir(ctxt.tcx, input);
        // REVIEW: the parameters don't have attributes, so we use the overall mode
        let vir_param = spanned_new(param.span, ParamX { name, typ, mode });
        vir_params.push(vir_param);
    }
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = Arc::new(FunX { path, trait_path: None });
    let params = Arc::new(vir_params);
    let (ret_typ, ret_mode) = match ret_typ_mode {
        None => (Arc::new(TypX::Tuple(Arc::new(vec![]))), mode),
        Some((typ, mode)) => (typ, mode),
    };
    let ret_param =
        ParamX { name: Arc::new(RETURN_VALUE.to_string()), typ: ret_typ, mode: ret_mode };
    let ret = spanned_new(span, ret_param);
    let func = FunctionX {
        name,
        visibility,
        fuel,
        mode,
        typ_bounds,
        params,
        ret,
        require: Arc::new(vec![]),
        ensure: Arc::new(vec![]),
        decrease: Arc::new(vec![]),
        is_abstract: false,
        attrs: Default::default(),
        body: None,
    };
    let function = spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}
