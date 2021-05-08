use crate::rust_to_vir_base::{
    check_generics, get_fuel, get_mode, get_var_mode, ident_to_var, ty_to_vir, Ctxt,
};
use crate::rust_to_vir_expr::{expr_to_vir, pat_to_var};
use crate::util::{err_span_str, err_span_string, spanned_new, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{Body, BodyId, Crate, FnDecl, FnHeader, FnSig, Generics, Param, Unsafety};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{FunctionX, KrateX, Mode, ParamX, Typ, VirErr};
use vir::def::RETURN_VALUE;

pub(crate) fn body_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: &BodyId,
    body: &Body<'tcx>,
    mode: Mode,
) -> Result<vir::ast::Expr, VirErr> {
    let def = rustc_middle::ty::WithOptConstParam::unknown(id.hir_id.owner);
    let types = tcx.typeck_opt_const_arg(def);
    let ctxt = Ctxt { tcx, types, mode };
    expr_to_vir(&ctxt, &body.value)
}

fn check_fn_decl<'tcx>(
    tcx: TyCtxt<'tcx>,
    decl: &'tcx FnDecl<'tcx>,
    mode: Mode,
) -> Result<Option<(Typ, Mode)>, VirErr> {
    let FnDecl { inputs: _, output, c_variadic, implicit_self } = decl;
    unsupported_unless!(!c_variadic, "c_variadic");
    match implicit_self {
        rustc_hir::ImplicitSelfKind::None => {}
        _ => unsupported!("implicit_self"),
    }
    match output {
        rustc_hir::FnRetTy::DefaultReturn(_) => Ok(None),
        // REVIEW: there's no attribute syntax on return types,
        // so we always return the default mode.
        // The current workaround is to return a struct if the default doesn't work.
        rustc_hir::FnRetTy::Return(ty) => Ok(Some((ty_to_vir(tcx, ty), mode))),
    }
}

pub(crate) fn check_item_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &'tcx Crate<'tcx>,
    vir: &mut KrateX,
    id: Ident,
    attrs: &[Attribute],
    sig: &'tcx FnSig<'tcx>,
    generics: &Generics,
    body_id: &BodyId,
) -> Result<(), VirErr> {
    let mode = get_mode(Mode::Exec, attrs);
    let ret_typ_mode = match sig {
        FnSig {
            header: FnHeader { unsafety, constness: _, asyncness: _, abi: _ },
            decl,
            span: _,
        } => {
            unsupported_err_unless!(*unsafety == Unsafety::Normal, sig.span, "unsafe");
            check_fn_decl(tcx, decl, mode)?
        }
    };
    let typ_params = check_generics(generics)?;
    let fuel = get_fuel(attrs);
    let body = &krate.bodies[body_id];
    let Body { params, value: _, generator_kind } = body;
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    for (param, input) in params.iter().zip(sig.decl.inputs.iter()) {
        let Param { hir_id, pat, ty_span: _, span } = param;
        let name = Rc::new(pat_to_var(pat));
        let typ = ty_to_vir(tcx, input);
        let mode = get_var_mode(mode, tcx.hir().attrs(*hir_id));
        let vir_param = spanned_new(*span, ParamX { name, typ, mode });
        vir_params.push(vir_param);
    }
    match generator_kind {
        None => {}
        _ => {
            unsupported_err!(sig.span, "generator_kind", generator_kind);
        }
    }
    let mut vir_body = body_to_vir(tcx, body_id, body, mode)?;
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
    let name = Rc::new(ident_to_var(&id));
    let params = Rc::new(vir_params);
    let ret = match (header.ensure_id_typ, ret_typ_mode) {
        (None, None) => None,
        (None, Some((typ, mode))) => Some((Rc::new(RETURN_VALUE.to_string()), typ, mode)),
        (Some((x, _)), Some((typ, mode))) => Some((x, typ, mode)),
        _ => panic!("internal error: ret_typ"),
    };
    let func = FunctionX {
        name,
        mode,
        fuel,
        typ_params,
        params,
        ret,
        require: header.require,
        ensure: header.ensure,
        decrease: header.decrease,
        hidden: Rc::new(header.hidden),
        body: Some(vir_body),
    };
    let function = spanned_new(sig.span, func);
    vir.functions.push(function);
    Ok(())
}

pub(crate) fn check_foreign_item_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    vir: &mut KrateX,
    id: Ident,
    span: Span,
    attrs: &[Attribute],
    decl: &'tcx FnDecl<'tcx>,
    idents: &[Ident],
    generics: &Generics,
) -> Result<(), VirErr> {
    let mode = get_mode(Mode::Exec, attrs);
    let ret_typ_mode = check_fn_decl(tcx, decl, mode)?;
    let typ_params = check_generics(generics)?;
    let fuel = get_fuel(attrs);
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    for (param, input) in idents.iter().zip(decl.inputs.iter()) {
        let name = Rc::new(ident_to_var(param));
        let typ = ty_to_vir(tcx, input);
        // REVIEW: the parameters don't have attributes, so we use the overall mode
        let vir_param = spanned_new(param.span, ParamX { name, typ, mode });
        vir_params.push(vir_param);
    }
    let name = Rc::new(ident_to_var(&id));
    let params = Rc::new(vir_params);
    let func = FunctionX {
        name,
        fuel,
        mode,
        typ_params,
        params,
        ret: ret_typ_mode.map(|(typ, mode)| (Rc::new(RETURN_VALUE.to_string()), typ, mode)),
        require: Rc::new(vec![]),
        ensure: Rc::new(vec![]),
        decrease: None,
        hidden: Rc::new(vec![]),
        body: None,
    };
    let function = spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}
