use crate::rust_to_vir_expr::{
    expr_to_vir, get_fuel, get_mode, ident_to_var, pat_to_var, spanned_new, ty_to_vir,
};
use crate::{unsupported, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{Body, BodyId, Crate, FnDecl, FnHeader, FnSig, Generics, Param, Unsafety};
use rustc_middle::ty::TyCtxt;
use rustc_mir_build::thir;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{Function, FunctionX, Mode, ParamX};

fn body_to_vir<'tcx>(tcx: TyCtxt<'tcx>, id: &BodyId, body: &'tcx Body<'tcx>) -> vir::ast::Expr {
    let did = id.hir_id.owner;
    let arena = thir::Arena::default();
    let expr = thir::build_thir(
        tcx,
        rustc_middle::ty::WithOptConstParam::unknown(did),
        &arena,
        &body.value,
    );
    let vir_expr = expr_to_vir(tcx, expr);
    vir_expr
}

fn check_fn_decl<'tcx>(tcx: TyCtxt<'tcx>, decl: &'tcx FnDecl<'tcx>) -> Option<vir::ast::Typ> {
    let FnDecl { inputs: _, output, c_variadic, implicit_self } = decl;
    unsupported_unless!(!c_variadic, "c_variadic");
    match implicit_self {
        rustc_hir::ImplicitSelfKind::None => {}
        _ => unsupported!("implicit_self"),
    }
    match output {
        rustc_hir::FnRetTy::DefaultReturn(_) => None,
        rustc_hir::FnRetTy::Return(ty) => Some(ty_to_vir(tcx, ty)),
    }
}

fn check_generics<'tcx>(generics: &'tcx Generics<'tcx>) {
    match generics {
        Generics { params, where_clause, span: _ } => {
            unsupported_unless!(params.len() == 0, "generics");
            unsupported_unless!(where_clause.predicates.len() == 0, "where clause");
        }
    }
}

pub(crate) fn check_item_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &'tcx Crate<'tcx>,
    vir: &mut Vec<Function>,
    id: Ident,
    attrs: &[Attribute],
    sig: &'tcx FnSig<'tcx>,
    generics: &Generics,
    body_id: &BodyId,
) {
    let ret = match sig {
        FnSig {
            header: FnHeader { unsafety, constness: _, asyncness: _, abi: _ },
            decl,
            span: _,
        } => {
            unsupported_unless!(*unsafety == Unsafety::Normal, "unsafe");
            check_fn_decl(tcx, decl)
        }
    };
    check_generics(generics);
    let mode = get_mode(attrs);
    let fuel = get_fuel(attrs);
    match (mode, &ret) {
        (Mode::Exec, None) | (Mode::Proof, None) => {}
        (Mode::Exec, Some(_)) | (Mode::Proof, Some(_)) => {
            unsupported!("non-spec function return values");
        }
        (Mode::Spec, _) => {}
    }
    let body = &krate.bodies[body_id];
    let Body { params, value: _, generator_kind } = body;
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    for (param, input) in params.iter().zip(sig.decl.inputs.iter()) {
        let Param { hir_id: _, pat, ty_span: _, span } = param;
        let name = Rc::new(pat_to_var(pat));
        let typ = ty_to_vir(tcx, input);
        let vir_param = spanned_new(*span, ParamX { name, typ });
        vir_params.push(vir_param);
    }
    match generator_kind {
        None => {}
        _ => {
            unsupported!("generator_kind", generator_kind);
        }
    }
    let vir_body = body_to_vir(tcx, body_id, body);
    let name = Rc::new(ident_to_var(&id));
    let params = Rc::new(vir_params);
    let function =
        spanned_new(sig.span, FunctionX { name, mode, fuel, params, ret, body: Some(vir_body) });
    vir.push(function);
}

pub(crate) fn check_foreign_item_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    vir: &mut Vec<Function>,
    id: Ident,
    span: Span,
    attrs: &[Attribute],
    decl: &'tcx FnDecl<'tcx>,
    idents: &[Ident],
    generics: &Generics,
) {
    let ret = check_fn_decl(tcx, decl);
    check_generics(generics);
    let mode = get_mode(attrs);
    let fuel = get_fuel(attrs);
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();
    for (param, input) in idents.iter().zip(decl.inputs.iter()) {
        let name = Rc::new(ident_to_var(param));
        let typ = ty_to_vir(tcx, input);
        let vir_param = spanned_new(param.span, ParamX { name, typ });
        vir_params.push(vir_param);
    }
    let name = Rc::new(ident_to_var(&id));
    let params = Rc::new(vir_params);
    let function = spanned_new(span, FunctionX { name, fuel, mode, params, ret, body: None });
    vir.push(function);
}
