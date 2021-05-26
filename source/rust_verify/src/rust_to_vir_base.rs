use crate::util::{err_span_str, err_span_string, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::TokenTree;
use rustc_ast::{AttrKind, Attribute, IntTy, MacArgs, UintTy};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::definitions::DefPath;
use rustc_hir::{GenericParam, GenericParamKind, Generics, HirId, ParamName, PrimTy, QPath, Ty};
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind, TypeckResults};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{Idents, IntRange, Mode, Path, Typ, TypX, VirErr};
use vir::ast_util::types_equal;

pub(crate) fn def_to_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Path {
    Rc::new(tcx.def_path(def_id).data.iter().map(|d| Rc::new(format!("{}", d))).collect::<Vec<_>>())
}

#[inline(always)]
pub(crate) fn def_id_to_ty_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> TypX {
    TypX::Path(def_id_to_vir_path(tcx, def_id))
}

#[inline(always)]
pub(crate) fn def_id_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Path {
    def_path_to_vir_path(tcx, tcx.def_path(def_id))
}

pub(crate) fn def_path_to_vir_path<'tcx>(_tcx: TyCtxt<'tcx>, def_path: DefPath) -> Path {
    Rc::new(def_path.data.iter().map(|d| Rc::new(format!("{}", d))).collect::<Vec<_>>())
}

// TODO: proper handling of def_ids
// use https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.lang_items ?
pub(crate) fn hack_get_def_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    let debug_name = tcx.def_path_debug_str(def_id);
    let last_colon = debug_name.rfind(':').unwrap();
    debug_name[last_colon + 1..].to_string()
}

// TODO: proper handling of def_ids
// use https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.lang_items ?
pub(crate) fn hack_check_def_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    krate: &str,
    path: &str,
) -> bool {
    let debug_name = tcx.def_path_debug_str(def_id);
    let krate_prefix = format!("{}[", krate);
    let path_suffix = format!("]::{}", path);
    debug_name.starts_with(&krate_prefix) && debug_name.ends_with(&path_suffix)
}

pub(crate) fn ident_to_var<'tcx>(ident: &Ident) -> String {
    ident.to_string()
}

pub(crate) fn get_mode(default_mode: Mode, attrs: &[Attribute]) -> Mode {
    let mut mode = default_mode;
    for attr in attrs {
        match &attr.kind {
            AttrKind::Normal(item, _) => match &item.path.segments[..] {
                [segment] => match ident_to_var(&segment.ident).as_str() {
                    "spec" => mode = Mode::Spec,
                    "proof" => mode = Mode::Proof,
                    "exec" => mode = Mode::Exec,
                    _ => {}
                },
                _ => {}
            },
            _ => {}
        }
    }
    mode
}

pub(crate) fn get_var_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
    let default_mode = if function_mode == Mode::Proof { Mode::Spec } else { function_mode };
    get_mode(default_mode, attrs)
}

fn get_trigger_arg(span: Span, token_tree: TokenTree) -> Result<u64, VirErr> {
    let i = match &token_tree {
        TokenTree::Token(Token { kind: TokenKind::Literal(lit), .. }) => {
            match lit.symbol.as_str().parse::<u64>() {
                Ok(i) => Some(i),
                _ => None,
            }
        }
        _ => None,
    };
    match i {
        Some(i) => Ok(i),
        None => {
            err_span_string(span, format!("expected integer constant, found {:?}", &token_tree))
        }
    }
}

pub(crate) fn get_trigger(span: Span, attrs: &[Attribute]) -> Result<Vec<Option<u64>>, VirErr> {
    let mut groups: Vec<Option<u64>> = Vec::new();
    for attr in attrs {
        match &attr.kind {
            AttrKind::Normal(item, _) => match &item.path.segments[..] {
                [segment] => match ident_to_var(&segment.ident).as_str() {
                    "trigger" => match &item.args {
                        MacArgs::Empty => groups.push(None),
                        MacArgs::Delimited(_, _, token_stream) => {
                            for arg in token_stream.trees().step_by(2) {
                                groups.push(Some(get_trigger_arg(span, arg)?));
                            }
                            if groups.len() == 0 {
                                return err_span_str(
                                    span,
                                    "expected either #[trigger] or non-empty #[trigger(...)]",
                                );
                            }
                        }
                        _ => panic!("internal error: get_trigger"),
                    },
                    _ => {}
                },
                _ => {}
            },
            _ => {}
        }
    }
    Ok(groups)
}

pub(crate) fn get_fuel(attrs: &[Attribute]) -> u32 {
    let mut fuel: u32 = 1;
    for attr in attrs {
        match &attr.kind {
            AttrKind::Normal(item, _) => match &item.path.segments[..] {
                [segment] => match ident_to_var(&segment.ident).as_str() {
                    "opaque" => fuel = 0,
                    _ => {}
                },
                _ => {}
            },
            _ => {}
        }
    }
    fuel
}

pub(crate) fn mk_range<'tcx>(ty: rustc_middle::ty::Ty<'tcx>) -> IntRange {
    match ty.kind() {
        TyKind::Adt(_, _) if ty.to_string() == crate::typecheck::BUILTIN_INT => IntRange::Int,
        TyKind::Adt(_, _) if ty.to_string() == crate::typecheck::BUILTIN_NAT => IntRange::Nat,
        TyKind::Uint(rustc_middle::ty::UintTy::U8) => IntRange::U(8),
        TyKind::Uint(rustc_middle::ty::UintTy::U16) => IntRange::U(16),
        TyKind::Uint(rustc_middle::ty::UintTy::U32) => IntRange::U(32),
        TyKind::Uint(rustc_middle::ty::UintTy::U64) => IntRange::U(64),
        TyKind::Uint(rustc_middle::ty::UintTy::U128) => IntRange::U(128),
        TyKind::Uint(rustc_middle::ty::UintTy::Usize) => IntRange::USize,
        TyKind::Int(rustc_middle::ty::IntTy::I8) => IntRange::I(8),
        TyKind::Int(rustc_middle::ty::IntTy::I16) => IntRange::I(16),
        TyKind::Int(rustc_middle::ty::IntTy::I32) => IntRange::I(32),
        TyKind::Int(rustc_middle::ty::IntTy::I64) => IntRange::I(64),
        TyKind::Int(rustc_middle::ty::IntTy::I128) => IntRange::I(128),
        TyKind::Int(rustc_middle::ty::IntTy::Isize) => IntRange::ISize,
        _ => panic!("mk_range {:?}", ty),
    }
}

pub(crate) fn mid_ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty) -> Typ {
    let typ_x = match ty.kind() {
        TyKind::Bool => TypX::Bool,
        TyKind::Adt(AdtDef { did, .. }, _) => {
            let s = ty.to_string();
            if s == crate::typecheck::BUILTIN_INT {
                TypX::Int(IntRange::Int)
            } else if s == crate::typecheck::BUILTIN_NAT {
                TypX::Int(IntRange::Nat)
            } else {
                def_id_to_ty_path(tcx, *did)
            }
        }
        TyKind::Uint(_) | TyKind::Int(_) => TypX::Int(mk_range(ty)),
        TyKind::Param(param) => TypX::TypParam(Rc::new(param.name.to_string())),
        _ => {
            unsupported!(format!("type {:?}", ty))
        }
    };
    Rc::new(typ_x)
}

pub(crate) fn mid_ty_to_vir_opt<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty) -> Option<Typ> {
    match ty.kind() {
        TyKind::Never => None,
        TyKind::Tuple(_) if ty.tuple_fields().count() == 0 => None,
        _ => Some(mid_ty_to_vir(tcx, ty)),
    }
}

// TODO remove if unused
pub(crate) fn _ty_resolved_path_to_debug_path(_tcx: TyCtxt<'_>, ty: &Ty) -> String {
    let Ty { hir_id: _, kind, span: _ } = ty;
    match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => path
            .segments
            .iter()
            .map(|x| x.ident.name.to_ident_string())
            .collect::<Vec<_>>()
            .join("::"),
        _ => panic!("{:?} does not have a resolved path", ty),
    }
}

pub(crate) fn ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> Typ {
    let Ty { hir_id: _, kind, span } = ty;
    let typ_x = match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::PrimTy(PrimTy::Bool) => TypX::Bool,
            Res::PrimTy(PrimTy::Uint(UintTy::U8)) => TypX::Int(IntRange::U(8)),
            Res::PrimTy(PrimTy::Uint(UintTy::U16)) => TypX::Int(IntRange::U(16)),
            Res::PrimTy(PrimTy::Uint(UintTy::U32)) => TypX::Int(IntRange::U(32)),
            Res::PrimTy(PrimTy::Uint(UintTy::U64)) => TypX::Int(IntRange::U(64)),
            Res::PrimTy(PrimTy::Uint(UintTy::U128)) => TypX::Int(IntRange::U(128)),
            Res::PrimTy(PrimTy::Uint(UintTy::Usize)) => TypX::Int(IntRange::USize),
            Res::PrimTy(PrimTy::Int(IntTy::I8)) => TypX::Int(IntRange::I(8)),
            Res::PrimTy(PrimTy::Int(IntTy::I16)) => TypX::Int(IntRange::I(16)),
            Res::PrimTy(PrimTy::Int(IntTy::I32)) => TypX::Int(IntRange::I(32)),
            Res::PrimTy(PrimTy::Int(IntTy::I64)) => TypX::Int(IntRange::I(64)),
            Res::PrimTy(PrimTy::Int(IntTy::I128)) => TypX::Int(IntRange::I(128)),
            Res::PrimTy(PrimTy::Int(IntTy::Isize)) => TypX::Int(IntRange::ISize),
            Res::Def(DefKind::TyParam, def_id) => {
                let path = def_to_path(tcx, def_id);
                TypX::TypParam(path.last().unwrap().clone())
            }
            Res::Def(DefKind::Struct, def_id) => {
                // TODO: consider using #[rust_diagnostic_item] and https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/query/query_stored/type.diagnostic_items.html for the builtin lib
                if hack_check_def_name(tcx, def_id, "builtin", "int") {
                    TypX::Int(IntRange::Int)
                } else if hack_check_def_name(tcx, def_id, "builtin", "nat") {
                    TypX::Int(IntRange::Nat)
                } else {
                    def_id_to_ty_path(tcx, def_id)
                }
            }
            Res::Def(DefKind::Enum, def_id) => def_id_to_ty_path(tcx, def_id),
            _ => {
                unsupported!(format!("type {:#?} {:?} {:?}", kind, path.res, span))
            }
        },
        _ => {
            unsupported!(format!("type {:#?} {:?}", kind, span))
        }
    };
    Rc::new(typ_x)
}

pub(crate) struct Ctxt<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) mode: Mode,
}

pub(crate) fn typ_of_node<'tcx>(ctxt: &Ctxt<'tcx>, id: &HirId) -> Typ {
    mid_ty_to_vir(ctxt.tcx, ctxt.types.node_type(*id))
}

// Do equality operations on these operands translate into the SMT solver's == operation?
pub(crate) fn is_smt_equality<'tcx>(
    ctxt: &Ctxt<'tcx>,
    _span: Span,
    id1: &HirId,
    id2: &HirId,
) -> bool {
    let (t1, t2) = (typ_of_node(ctxt, id1), typ_of_node(ctxt, id2));
    match (&*t1, &*t2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(_), TypX::Int(_)) => true,
        (TypX::Path(_), TypX::Path(_)) if types_equal(&t1, &t2) => {
            let struct_eq_def_id = ctxt
                .tcx
                .lang_items()
                .structural_teq_trait()
                .expect("structural eq trait is not defined");
            let ty = ctxt.types.node_type(*id1);
            let substs_ref = ctxt.tcx.mk_substs_trait(ty, &[]);
            let type_impls_struct_eq = ctxt.tcx.type_implements_trait((
                struct_eq_def_id,
                ty,
                substs_ref,
                rustc_middle::ty::ParamEnv::empty(),
            ));
            unsupported_unless!(type_impls_struct_eq, "eq_for_non_structural_eq");
            true
        }
        _ => false,
    }
}

// Do arithmetic operations on these operands translate into the SMT solver's <=, +, =>, etc.?
// (possibly with clipping/wrapping for finite-size integers?)
pub(crate) fn is_smt_arith<'tcx>(ctxt: &Ctxt<'tcx>, id1: &HirId, id2: &HirId) -> bool {
    match (&*typ_of_node(ctxt, id1), &*typ_of_node(ctxt, id2)) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(_), TypX::Int(_)) => true,
        _ => false,
    }
}

pub(crate) fn check_generics<'tcx>(generics: &'tcx Generics<'tcx>) -> Result<Idents, VirErr> {
    let Generics { params, where_clause, span: _ } = generics;
    let mut typ_params: Vec<vir::ast::Ident> = Vec::new();
    for param in params.iter() {
        let GenericParam { hir_id: _, name, bounds, span: _, pure_wrt_drop, kind } = param;
        unsupported_err_unless!(bounds.len() == 0, generics.span, "generic bounds");
        unsupported_err_unless!(!pure_wrt_drop, generics.span, "generic pure_wrt_drop");
        match (name, kind) {
            (ParamName::Plain(id), GenericParamKind::Type { default: None, synthetic: None }) => {
                typ_params.push(Rc::new(id.name.as_str().to_string()));
            }
            _ => unsupported_err!(generics.span, "complex generics"),
        }
    }
    unsupported_err_unless!(where_clause.predicates.len() == 0, generics.span, "where clause");
    Ok(Rc::new(typ_params))
}
