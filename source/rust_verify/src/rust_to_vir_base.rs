use crate::context::Context;
use crate::util::{err_span_str, err_span_string, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless};
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_ast::{AttrKind, Attribute, IntTy, MacArgs, UintTy};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::definitions::DefPath;
use rustc_hir::{
    GenericBound, GenericParam, GenericParamKind, Generics, HirId, ParamName, PathSegment,
    PolyTraitRef, PrimTy, QPath, TraitBoundModifier, Ty, Visibility, VisibilityKind,
};
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind, TypeckResults};
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    GenericBoundX, Idents, IntRange, Mode, Path, PathX, Typ, TypBounds, TypX, Typs, VirErr,
};
use vir::ast_util::{path_as_rust_name, types_equal};

pub(crate) fn def_path_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_path: DefPath) -> Path {
    let krate = if def_path.krate == LOCAL_CRATE {
        None
    } else {
        Some(Arc::new(tcx.crate_name(def_path.krate).to_string()))
    };
    let segments =
        Arc::new(def_path.data.iter().map(|d| Arc::new(format!("{}", d))).collect::<Vec<_>>());
    Arc::new(PathX { krate, segments })
}

pub(crate) fn def_id_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Path {
    def_path_to_vir_path(tcx, tcx.def_path(def_id))
}

pub(crate) fn def_to_path_ident<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> vir::ast::Ident {
    let def_path = tcx.def_path(def_id);
    match def_path.data.last().expect("unexpected empty impl path").data {
        rustc_hir::definitions::DefPathData::ValueNs(name) => Arc::new(name.to_string()),
        _ => panic!("unexpected name of impl"),
    }
}

pub(crate) fn def_id_to_datatype<'tcx, 'hir>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    typ_args: Typs,
) -> TypX {
    TypX::Datatype(def_id_to_vir_path(tcx, def_id), typ_args)
}

pub(crate) fn def_id_to_datatype_segments<'tcx, 'hir>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    segments: &'hir [PathSegment<'hir>],
) -> TypX {
    let typ_args: Vec<Typ> = match &segments.last().expect("type must have a segment").args {
        None => vec![],
        Some(args) => args
            .args
            .iter()
            .map(|a| match a {
                rustc_hir::GenericArg::Type(t) => ty_to_vir(tcx, &t),
                _ => panic!("unexpected type arguments"),
            })
            .collect(),
    };
    TypX::Datatype(def_id_to_vir_path(tcx, def_id), Arc::new(typ_args))
}

// TODO: proper handling of def_ids
// use https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.lang_items ?
pub(crate) fn hack_get_def_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    let debug_name = tcx.def_path_debug_str(def_id);
    let last_colon = debug_name.rfind(':').unwrap();
    debug_name[last_colon + 1..].to_string()
}

pub(crate) fn ident_to_var<'tcx>(ident: &Ident) -> String {
    ident.to_string()
}

pub(crate) fn is_visibility_private(vis_kind: &VisibilityKind, inherited_is_private: bool) -> bool {
    match vis_kind {
        VisibilityKind::Inherited => inherited_is_private,
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
        is_private: is_visibility_private(&vis.node, true),
    }
}

#[derive(Debug)]
pub(crate) enum AttrTree {
    Fun(Span, String, Option<Box<[AttrTree]>>),
    Eq(Span, String, String),
}

pub(crate) fn token_to_string(token: &Token) -> Result<Option<String>, ()> {
    match token.kind {
        TokenKind::Literal(lit) => Ok(Some(lit.symbol.as_str().to_string())),
        TokenKind::Ident(symbol, _) => Ok(Some(symbol.as_str().to_string())),
        TokenKind::Comma => Ok(None),
        _ => Err(()),
    }
}

pub(crate) fn token_stream_to_trees(
    span: Span,
    stream: &TokenStream,
) -> Result<Box<[AttrTree]>, ()> {
    let mut token_trees: Vec<TokenTree> = Vec::new();
    for x in stream.trees() {
        token_trees.push(x);
    }
    let mut i = 0;
    let mut trees: Vec<AttrTree> = Vec::new();
    while i < token_trees.len() {
        match &token_trees[i] {
            TokenTree::Token(token) => {
                if let Some(name) = token_to_string(token)? {
                    let fargs = if i + 1 < token_trees.len() {
                        if let TokenTree::Delimited(_, _, token_stream) = &token_trees[i + 1] {
                            i += 1;
                            Some(token_stream_to_trees(span, token_stream)?)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    trees.push(AttrTree::Fun(span, name, fargs));
                }
                i += 1;
            }
            _ => return Err(()),
        }
    }
    Ok(trees.into_boxed_slice())
}

pub(crate) fn mac_args_to_tree(span: Span, name: String, args: &MacArgs) -> Result<AttrTree, ()> {
    match args {
        MacArgs::Empty => Ok(AttrTree::Fun(span, name, None)),
        MacArgs::Delimited(_, _, token_stream) => {
            Ok(AttrTree::Fun(span, name, Some(token_stream_to_trees(span, token_stream)?)))
        }
        MacArgs::Eq(_, token) => match token_to_string(token)? {
            None => Err(()),
            Some(token) => Ok(AttrTree::Eq(span, name, token)),
        },
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
    // function return mode (spec, proof, exec)
    ReturnMode(Mode),
    // parse function to get header, but don't verify body
    NoVerify,
    // don't parse function; function can't be called directly from verified code
    External,
    // hide body from other modules
    Abstract,
    // hide body (from all modules) until revealed
    Opaque,
    // export function's require/ensure as global forall
    ExportAsGlobalForall,
    // when used in a spec context, promote to spec by inserting .view()
    Autoview,
    // add manual trigger to expression inside quantifier
    Trigger(Option<Vec<u64>>),
    // custom error string to report for precondition failures
    CustomReqErr(String),
    // verify using bitvector theory, not converting back and forth with integer
    BitVector,
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
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "export_as_global_forall" => {
                    v.push(Attr::ExportAsGlobalForall)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "autoview" => {
                    v.push(Attr::Autoview)
                }
                Some(box [AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, msg, None)]))])
                    if arg == "custom_req_err" =>
                {
                    v.push(Attr::CustomReqErr(msg.clone()))
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "bit_vector" => {
                    v.push(Attr::BitVector)
                }
                Some(box [AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))])
                    if arg == "returns" && name == "spec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Spec))
                }
                Some(box [AttrTree::Fun(_, arg, None), AttrTree::Fun(_, name, None)])
                    if arg == "returns" && name == "proof" =>
                {
                    v.push(Attr::ReturnMode(Mode::Proof))
                }
                Some(box [AttrTree::Fun(_, arg, None), AttrTree::Fun(_, name, None)])
                    if arg == "returns" && name == "exec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Exec))
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

pub(crate) fn get_ret_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
    let mut mode = get_var_mode(function_mode, &[]);
    for attr in parse_attrs_opt(attrs) {
        match attr {
            Attr::ReturnMode(m) => mode = m,
            _ => {}
        }
    }
    mode
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
    pub(crate) export_as_global_forall: bool,
    pub(crate) autoview: bool,
    pub(crate) custom_req_err: Option<String>,
    pub(crate) bit_vector: bool,
}

pub(crate) fn get_verifier_attrs(attrs: &[Attribute]) -> Result<VerifierAttrs, VirErr> {
    let mut vs = VerifierAttrs {
        do_verify: true,
        external: false,
        is_abstract: false,
        export_as_global_forall: false,
        autoview: false,
        custom_req_err: None,
        bit_vector: false,
    };
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::NoVerify => vs.do_verify = false,
            Attr::External => vs.external = true,
            Attr::Abstract => vs.is_abstract = true,
            Attr::ExportAsGlobalForall => vs.export_as_global_forall = true,
            Attr::Autoview => vs.autoview = true,
            Attr::CustomReqErr(s) => vs.custom_req_err = Some(s.clone()),
            Attr::BitVector => vs.bit_vector = true,
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
        TyKind::Bool => Arc::new(TypX::Bool),
        TyKind::Uint(_) | TyKind::Int(_) => Arc::new(TypX::Int(mk_range(ty))),
        TyKind::Ref(_, tys, rustc_ast::Mutability::Not) => mid_ty_to_vir(tcx, tys),
        TyKind::Param(param) => Arc::new(TypX::TypParam(Arc::new(param.name.to_string()))),
        TyKind::Never => {
            // All types are inhabited in SMT; we pick an arbitrary inhabited type for Never
            Arc::new(TypX::Tuple(Arc::new(vec![])))
        }
        TyKind::Tuple(_) => {
            let typs: Vec<Typ> = ty.tuple_fields().map(|t| mid_ty_to_vir(tcx, t)).collect();
            Arc::new(TypX::Tuple(Arc::new(typs)))
        }
        TyKind::Adt(AdtDef { did, .. }, args) => Arc::new({
            let s = ty.to_string();
            // TODO use lang items instead of string comparisons
            if s == crate::typecheck::BUILTIN_INT {
                TypX::Int(IntRange::Int)
            } else if s == crate::typecheck::BUILTIN_NAT {
                TypX::Int(IntRange::Nat)
            } else {
                let typ_args: Vec<Typ> = args
                    .iter()
                    .map(|arg| match arg.unpack() {
                        rustc_middle::ty::subst::GenericArgKind::Type(t) => mid_ty_to_vir(tcx, t),
                        _ => panic!("unexpected type argument"),
                    })
                    .collect();
                def_id_to_datatype(tcx, *did, Arc::new(typ_args))
            }
        }),
        TyKind::Closure(_def, substs) => {
            let sig = substs.as_closure().sig();
            let args: Vec<Typ> =
                sig.inputs().skip_binder().iter().map(|t| mid_ty_to_vir(tcx, t)).collect();
            let ret = mid_ty_to_vir(tcx, sig.output().skip_binder());
            Arc::new(TypX::Lambda(Arc::new(args), ret))
        }
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
        rustc_hir::TyKind::Tup(tys) => {
            Arc::new(TypX::Tuple(Arc::new(tys.iter().map(|t| ty_to_vir(tcx, t)).collect())))
        }
        rustc_hir::TyKind::Rptr(
            _,
            rustc_hir::MutTy { ty: tys, mutbl: rustc_ast::Mutability::Not },
        ) => ty_to_vir(tcx, tys),
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
                let path = def_id_to_vir_path(tcx, def_id);
                TypX::TypParam(path.segments.last().unwrap().clone())
            }
            Res::Def(DefKind::Struct, def_id) => {
                // TODO: consider using #[rust_diagnostic_item] and https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/query/query_stored/type.diagnostic_items.html for the builtin lib
                let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, def_id));
                if def_name == "builtin::int" {
                    TypX::Int(IntRange::Int)
                } else if def_name == "builtin::nat" {
                    TypX::Int(IntRange::Nat)
                } else if def_name == "alloc::boxed::Box" {
                    match &path.segments[0].args.expect("Box arg").args[0] {
                        rustc_hir::GenericArg::Type(t) => return ty_to_vir(tcx, t),
                        _ => panic!("unexpected arg to Box"),
                    }
                } else {
                    def_id_to_datatype_segments(tcx, def_id, &path.segments)
                }
            }
            Res::Def(DefKind::Enum, def_id) => {
                def_id_to_datatype_segments(tcx, def_id, &path.segments)
            }
            Res::SelfTy(None, Some((impl_def_id, false))) => {
                def_id_to_datatype_segments(tcx, impl_def_id, &path.segments)
            }
            _ => {
                unsupported!(format!("type {:#?} {:?} {:?}", kind, path.res, span))
            }
        }),
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
        (TypX::Datatype(..), TypX::Datatype(..)) if types_equal(&t1, &t2) => {
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

pub(crate) fn check_generic_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    span: Span,
    bound: &'tcx GenericBound<'tcx>,
) -> Result<vir::ast::GenericBound, VirErr> {
    match bound {
        GenericBound::Trait(
            PolyTraitRef { bound_generic_params: [], trait_ref, span: _ },
            TraitBoundModifier::None,
        ) => {
            let path = &trait_ref.path;
            let def_id = match path.res {
                rustc_hir::def::Res::Def(_, def_id) => def_id,
                _ => return unsupported_err!(span, "generic bounds"),
            };
            let f_name = path_as_rust_name(&def_id_to_vir_path(tcx, def_id));
            if f_name == "core::ops::function::Fn" {
                let args = &path.segments.last().expect("last segment").args.expect("GenericArgs");
                unsupported_err_unless!(args.args.len() == 1, span, "generic bounds");
                unsupported_err_unless!(args.bindings.len() == 1, span, "generic bounds");
                unsupported_err_unless!(
                    args.bindings[0].gen_args.args.len() == 0,
                    span,
                    "generic bounds"
                );
                let t_args = match &args.args[0] {
                    rustc_hir::GenericArg::Type(t) => ty_to_vir(tcx, &t),
                    _ => panic!("unexpected arg to Fn"),
                };
                let t_ret = match &args.bindings[0].kind {
                    rustc_hir::TypeBindingKind::Equality { ty } => ty_to_vir(tcx, ty),
                    _ => panic!("unexpected arg to Fn"),
                };
                let args = match &*t_args {
                    TypX::Tuple(args) => args.clone(),
                    _ => panic!("unexpected arg to Fn"),
                };
                Ok(Arc::new(GenericBoundX::FnSpec(args, t_ret)))
            } else {
                unsupported_err!(span, "generic bounds")
            }
        }
        _ => {
            unsupported_err!(span, "generic bounds")
        }
    }
}

pub(crate) fn check_generics_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<TypBounds, VirErr> {
    let Generics { params, where_clause, span: _ } = generics;
    let mut typ_params: Vec<(vir::ast::Ident, vir::ast::GenericBound)> = Vec::new();
    for param in params.iter() {
        let GenericParam { hir_id: _, name, bounds, span: _, pure_wrt_drop, kind } = param;
        unsupported_err_unless!(bounds.len() <= 1, generics.span, "generic bounds");
        unsupported_err_unless!(!pure_wrt_drop, generics.span, "generic pure_wrt_drop");
        match (name, kind) {
            (ParamName::Plain(id), GenericParamKind::Type { default: None, synthetic: None }) => {
                let ident = Arc::new(id.name.as_str().to_string());
                let bound = if bounds.len() == 1 {
                    check_generic_bound(tcx, generics.span, &bounds[0])?
                } else {
                    Arc::new(GenericBoundX::None)
                };
                typ_params.push((ident, bound));
            }
            _ => unsupported_err!(generics.span, "complex generics"),
        }
    }
    unsupported_err_unless!(where_clause.predicates.len() == 0, generics.span, "where clause");
    Ok(Arc::new(typ_params))
}

pub(crate) fn check_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<Idents, VirErr> {
    let typ_bounds = check_generics_bounds(tcx, generics)?;
    let mut typ_params: Vec<vir::ast::Ident> = Vec::new();
    for (x, bound) in typ_bounds.iter() {
        // REVIEW:
        // We currently only allow bounds for functions, not for datatypes,
        // so that datatypes cannot refer to function types.
        // If we allow function types in fields of datatypes, we will need to have VIR perform
        // a positivity check (recursive types only allowed in positive positions) for soundness.
        match &**bound {
            GenericBoundX::None => typ_params.push(x.clone()),
            _ => {
                unsupported_err!(generics.span, "generic bounds");
            }
        }
    }
    Ok(Arc::new(typ_params))
}
