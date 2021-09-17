use crate::context::Context;
use crate::util::{err_span_str, err_span_string, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless};
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::TokenTree;
use rustc_ast::{AttrKind, Attribute, IntTy, MacArgs, UintTy};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::definitions::DefPath;
use rustc_hir::{
    GenericParam, GenericParamKind, Generics, HirId, ParamName, PrimTy, QPath, Ty, Visibility,
    VisibilityKind,
};
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind, TypeckResults};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{Idents, IntRange, Mode, Path, Typ, TypX, VirErr};
use vir::ast_util::types_equal;

pub(crate) fn def_to_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Path {
    Arc::new(
        tcx.def_path(def_id).data.iter().map(|d| Arc::new(format!("{}", d))).collect::<Vec<_>>(),
    )
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
    Arc::new(def_path.data.iter().map(|d| Arc::new(format!("{}", d))).collect::<Vec<_>>())
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

pub(crate) fn is_visibility_private(vis_kind: &VisibilityKind) -> bool {
    match vis_kind {
        VisibilityKind::Inherited => true,
        VisibilityKind::Public => false,
        VisibilityKind::Crate(_) => false,
        VisibilityKind::Restricted { .. } => unsupported!("restricted visibility"),
    }
}

pub(crate) fn mk_visibility<'tcx>(
    owning_module: &Option<Path>,
    vis: &Visibility<'tcx>,
) -> vir::ast::Visibility {
    vir::ast::Visibility {
        owning_module: owning_module.clone(),
        is_private: is_visibility_private(&vis.node),
    }
}

#[derive(Debug)]
pub(crate) enum AttrTree {
    Fun(Span, String, Option<Box<[AttrTree]>>),
    Eq(Span, String, String),
}

pub(crate) fn token_to_string(token: &Token) -> Result<String, ()> {
    match token.kind {
        TokenKind::Literal(lit) => Ok(lit.symbol.as_str().to_string()),
        TokenKind::Ident(symbol, _) => Ok(symbol.as_str().to_string()),
        _ => Err(()),
    }
}

pub(crate) fn token_tree_to_tree(token_tree: TokenTree) -> Result<AttrTree, ()> {
    match &token_tree {
        TokenTree::Token(token) => Ok(AttrTree::Fun(token.span, token_to_string(token)?, None)),
        _ => Err(()),
    }
}

pub(crate) fn mac_args_to_tree(span: Span, name: String, args: &MacArgs) -> Result<AttrTree, ()> {
    match args {
        MacArgs::Empty => Ok(AttrTree::Fun(span, name, None)),
        MacArgs::Delimited(_, _, token_stream) => {
            let mut fargs: Vec<AttrTree> = Vec::new();
            for arg in token_stream.trees().step_by(2) {
                fargs.push(token_tree_to_tree(arg)?);
            }
            Ok(AttrTree::Fun(span, name, Some(fargs.into_boxed_slice())))
        }
        MacArgs::Eq(_, token) => Ok(AttrTree::Eq(span, name, token_to_string(token)?)),
    }
}

pub(crate) fn attr_to_tree(attr: &Attribute) -> Result<AttrTree, ()> {
    match &attr.kind {
        AttrKind::Normal(item, _) => match &item.path.segments[..] {
            [segment] => {
                let name = ident_to_var(&segment.ident).as_str().to_string();
                mac_args_to_tree(attr.span, name, &item.args)
            }
            _ => Err(()),
        },
        _ => Err(()),
    }
}

pub(crate) fn attrs_to_trees(attrs: &[Attribute]) -> Vec<AttrTree> {
    let mut attr_trees: Vec<AttrTree> = Vec::new();
    for attr in attrs {
        if let Ok(tree) = attr_to_tree(attr) {
            attr_trees.push(tree);
        }
    }
    attr_trees
}

pub(crate) enum Attr {
    // specify mode (spec, proof, exec)
    Mode(Mode),
    // parse function to get header, but don't verify body
    NoVerify,
    // don't parse function; function can't be called directly from verified code
    External,
    // hide body from other modules
    Abstract,
    // hide body (from all modules) until revealed
    Opaque,
    // add manual trigger to expression inside quantifier
    Trigger(Option<Vec<u64>>),
    // custom error string to report for precondition failures
    CustomReqErr(String),
}

fn get_trigger_arg(span: Span, attr_tree: &AttrTree) -> Result<u64, VirErr> {
    let i = match attr_tree {
        AttrTree::Fun(_, name, None) => match name.parse::<u64>() {
            Ok(i) => Some(i),
            _ => None,
        },
        _ => None,
    };
    match i {
        Some(i) => Ok(i),
        None => err_span_string(span, format!("expected integer constant, found {:?}", &attr_tree)),
    }
}

pub(crate) fn parse_attrs(attrs: &[Attribute]) -> Result<Vec<Attr>, VirErr> {
    let mut v: Vec<Attr> = Vec::new();
    for attr in attrs_to_trees(attrs) {
        match attr {
            AttrTree::Fun(_, name, None) if name == "spec" => v.push(Attr::Mode(Mode::Spec)),
            AttrTree::Fun(_, name, None) if name == "proof" => v.push(Attr::Mode(Mode::Proof)),
            AttrTree::Fun(_, name, None) if name == "exec" => v.push(Attr::Mode(Mode::Exec)),
            AttrTree::Fun(_, name, None) if name == "opaque" => v.push(Attr::Opaque),
            AttrTree::Fun(_, name, None) if name == "trigger" => v.push(Attr::Trigger(None)),
            AttrTree::Fun(span, name, Some(args)) if name == "trigger" => {
                let mut groups: Vec<u64> = Vec::new();
                for arg in args.iter() {
                    groups.push(get_trigger_arg(span, arg)?);
                }
                if groups.len() == 0 {
                    return err_span_str(
                        span,
                        "expected either #[trigger] or non-empty #[trigger(...)]",
                    );
                }
                v.push(Attr::Trigger(Some(groups)));
            }
            AttrTree::Fun(span, name, args) if name == "verifier" => match &args {
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "no_verify" => {
                    v.push(Attr::NoVerify)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "external" => {
                    v.push(Attr::External)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "pub_abstract" => {
                    v.push(Attr::Abstract)
                }
                Some(box [AttrTree::Fun(_, arg, None), AttrTree::Fun(_, msg, None)])
                    if arg == "custom_req_err" =>
                {
                    v.push(Attr::CustomReqErr(msg.clone()))
                }
                _ => return err_span_str(span, "unrecognized verifier attribute"),
            },
            _ => {}
        }
    }
    Ok(v)
}

pub(crate) fn parse_attrs_opt(attrs: &[Attribute]) -> Vec<Attr> {
    match parse_attrs(attrs) {
        Ok(attrs) => attrs,
        Err(_) => vec![],
    }
}

pub(crate) fn get_mode(default_mode: Mode, attrs: &[Attribute]) -> Mode {
    let mut mode = default_mode;
    for attr in parse_attrs_opt(attrs) {
        match attr {
            Attr::Mode(m) => mode = m,
            _ => {}
        }
    }
    mode
}

pub(crate) fn get_var_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
    let default_mode = if function_mode == Mode::Proof { Mode::Spec } else { function_mode };
    get_mode(default_mode, attrs)
}

pub(crate) fn get_trigger(attrs: &[Attribute]) -> Result<Vec<Option<u64>>, VirErr> {
    let mut groups: Vec<Option<u64>> = Vec::new();
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::Trigger(None) => groups.push(None),
            Attr::Trigger(Some(group_ids)) => {
                groups.extend(group_ids.into_iter().map(|id| Some(id)));
            }
            _ => {}
        }
    }
    Ok(groups)
}

pub(crate) fn get_fuel(attrs: &[Attribute]) -> u32 {
    let mut fuel: u32 = 1;
    for attr in parse_attrs_opt(attrs) {
        match attr {
            Attr::Opaque => fuel = 0,
            _ => {}
        }
    }
    fuel
}

pub(crate) struct VerifierAttrs {
    pub(crate) do_verify: bool,
    pub(crate) external: bool,
    pub(crate) is_abstract: bool,
    pub(crate) custom_req_err: Option<String>,
}

pub(crate) fn get_verifier_attrs(attrs: &[Attribute]) -> Result<VerifierAttrs, VirErr> {
    let mut vs = VerifierAttrs {
        do_verify: true,
        external: false,
        is_abstract: false,
        custom_req_err: None,
    };
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::NoVerify => vs.do_verify = false,
            Attr::External => vs.external = true,
            Attr::Abstract => vs.is_abstract = true,
            Attr::CustomReqErr(s) => vs.custom_req_err = Some(s.clone()),
            _ => {}
        }
    }
    Ok(vs)
}

pub(crate) fn get_range(typ: &Typ) -> IntRange {
    match &**typ {
        TypX::Int(range) => *range,
        _ => panic!("get_range {:?}", typ),
    }
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

// TODO review and cosolidate type translation, e.g. with `ty_to_vir`, if possible
pub(crate) fn mid_ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty<'tcx>) -> Typ {
    match ty.kind() {
        TyKind::Tuple(_) if ty.tuple_fields().count() == 0 => Arc::new(TypX::Unit),
        TyKind::Bool => Arc::new(TypX::Bool),
        TyKind::Adt(AdtDef { did, .. }, _) => Arc::new({
            let s = ty.to_string();
            // TODO use lang items instead of string comparisons
            if s == crate::typecheck::BUILTIN_INT {
                TypX::Int(IntRange::Int)
            } else if s == crate::typecheck::BUILTIN_NAT {
                TypX::Int(IntRange::Nat)
            } else {
                def_id_to_ty_path(tcx, *did)
            }
        }),
        TyKind::Ref(_, tys, rustc_ast::Mutability::Not) => mid_ty_to_vir(tcx, tys),
        TyKind::Uint(_) | TyKind::Int(_) => Arc::new(TypX::Int(mk_range(ty))),
        TyKind::Param(param) => Arc::new(TypX::TypParam(Arc::new(param.name.to_string()))),
        _ => {
            unsupported!(format!("type {:?}", ty))
        }
    }
}

pub(crate) fn mid_ty_to_vir_opt<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Typ> {
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
    match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => Arc::new(match path.res {
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
        }),
        rustc_hir::TyKind::Rptr(
            _,
            rustc_hir::MutTy { ty: tys, mutbl: rustc_ast::Mutability::Not },
        ) => ty_to_vir(tcx, tys),
        _ => {
            unsupported!(format!("type {:#?} {:?}", kind, span))
        }
    }
}

pub(crate) struct BodyCtxt<'tcx> {
    pub(crate) ctxt: Context<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) mode: Mode,
}

pub(crate) fn typ_of_node<'tcx>(bctx: &BodyCtxt<'tcx>, id: &HirId) -> Typ {
    mid_ty_to_vir(bctx.ctxt.tcx, bctx.types.node_type(*id))
}

pub(crate) fn implements_structural<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &'tcx rustc_middle::ty::TyS<'tcx>,
) -> bool {
    let structural_def_id = tcx
        .get_diagnostic_item(rustc_span::Symbol::intern("builtin::Structural"))
        .expect("structural trait is not defined");
    let substs_ref = tcx.mk_substs([].iter());
    let ty_impls_structural = tcx.type_implements_trait((
        structural_def_id,
        ty,
        substs_ref,
        rustc_middle::ty::ParamEnv::empty(),
    ));
    ty_impls_structural
}

// Do equality operations on these operands translate into the SMT solver's == operation?
pub(crate) fn is_smt_equality<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    _span: Span,
    id1: &HirId,
    id2: &HirId,
) -> bool {
    let (t1, t2) = (typ_of_node(bctx, id1), typ_of_node(bctx, id2));
    match (&*t1, &*t2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(_), TypX::Int(_)) => true,
        (TypX::Path(_), TypX::Path(_)) if types_equal(&t1, &t2) => {
            let ty = bctx.types.node_type(*id1);
            implements_structural(bctx.ctxt.tcx, &ty)
        }
        _ => false,
    }
}

// Do arithmetic operations on these operands translate into the SMT solver's <=, +, =>, etc.?
// (possibly with clipping/wrapping for finite-size integers?)
pub(crate) fn is_smt_arith<'tcx>(bctx: &BodyCtxt<'tcx>, id1: &HirId, id2: &HirId) -> bool {
    match (&*typ_of_node(bctx, id1), &*typ_of_node(bctx, id2)) {
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
                typ_params.push(Arc::new(id.name.as_str().to_string()));
            }
            _ => unsupported_err!(generics.span, "complex generics"),
        }
    }
    unsupported_err_unless!(where_clause.predicates.len() == 0, generics.span, "where clause");
    Ok(Arc::new(typ_params))
}
