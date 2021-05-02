use crate::util::{err_span_str, err_span_string};
use crate::{unsupported, unsupported_unless};
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::TokenTree;
use rustc_ast::{AttrKind, Attribute, IntTy, MacArgs, UintTy};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{HirId, PrimTy, QPath, Ty};
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind, TypeckResults};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{IntRange, Mode, Typ, VirErr};

pub(crate) fn path_to_ty_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Typ {
    let ds =
        tcx.def_path(def_id).data.iter().map(|d| Rc::new(format!("{}", d))).collect::<Vec<_>>();
    Typ::Path(ds)
}

// TODO: proper handling of def_ids
pub(crate) fn hack_get_def_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    let debug_name = tcx.def_path_debug_str(def_id);
    let last_colon = debug_name.rfind(':').unwrap();
    debug_name[last_colon + 1..].to_string()
}

// TODO: proper handling of def_ids
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
    unsupported_unless!(ty.flags().is_empty(), "ty.flags", ty);
    match ty.kind() {
        TyKind::Bool => Typ::Bool,
        TyKind::Adt(AdtDef { did, .. }, _) => {
            let s = ty.to_string();
            if s == crate::typecheck::BUILTIN_INT {
                Typ::Int(IntRange::Int)
            } else if s == crate::typecheck::BUILTIN_NAT {
                Typ::Int(IntRange::Nat)
            } else {
                path_to_ty_path(tcx, *did)
            }
        }
        TyKind::Uint(_) | TyKind::Int(_) => Typ::Int(mk_range(ty)),
        _ => {
            unsupported!(format!("type {:?}", ty))
        }
    }
}

pub(crate) fn ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> Typ {
    let Ty { hir_id: _, kind, span } = ty;
    match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::PrimTy(PrimTy::Bool) => Typ::Bool,
            Res::PrimTy(PrimTy::Uint(UintTy::U8)) => Typ::Int(IntRange::U(8)),
            Res::PrimTy(PrimTy::Uint(UintTy::U16)) => Typ::Int(IntRange::U(16)),
            Res::PrimTy(PrimTy::Uint(UintTy::U32)) => Typ::Int(IntRange::U(32)),
            Res::PrimTy(PrimTy::Uint(UintTy::U64)) => Typ::Int(IntRange::U(64)),
            Res::PrimTy(PrimTy::Uint(UintTy::U128)) => Typ::Int(IntRange::U(128)),
            Res::PrimTy(PrimTy::Uint(UintTy::Usize)) => Typ::Int(IntRange::USize),
            Res::PrimTy(PrimTy::Int(IntTy::I8)) => Typ::Int(IntRange::I(8)),
            Res::PrimTy(PrimTy::Int(IntTy::I16)) => Typ::Int(IntRange::I(16)),
            Res::PrimTy(PrimTy::Int(IntTy::I32)) => Typ::Int(IntRange::I(32)),
            Res::PrimTy(PrimTy::Int(IntTy::I64)) => Typ::Int(IntRange::I(64)),
            Res::PrimTy(PrimTy::Int(IntTy::I128)) => Typ::Int(IntRange::I(128)),
            Res::PrimTy(PrimTy::Int(IntTy::Isize)) => Typ::Int(IntRange::ISize),
            Res::Def(DefKind::Struct, def_id) => {
                if hack_check_def_name(tcx, def_id, "builtin", "int") {
                    Typ::Int(IntRange::Int)
                } else if hack_check_def_name(tcx, def_id, "builtin", "nat") {
                    Typ::Int(IntRange::Nat)
                } else {
                    path_to_ty_path(tcx, def_id)
                }
            }
            Res::Def(DefKind::Enum, def_id) => path_to_ty_path(tcx, def_id),
            _ => {
                unsupported!(format!("type {:?} {:?} {:?}", kind, path.res, span))
            }
        },
        _ => {
            unsupported!(format!("type {:?} {:?}", kind, span))
        }
    }
}

pub(crate) struct Ctxt<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) mode: Mode,
}

pub(crate) fn typ_of_node<'tcx>(ctxt: &Ctxt<'tcx>, id: &HirId) -> Typ {
    mid_ty_to_vir(ctxt.tcx, ctxt.types.node_type(*id))
}
