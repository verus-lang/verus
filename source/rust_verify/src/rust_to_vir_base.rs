use crate::attributes::get_verifier_attrs;
use crate::context::BodyCtxt;
use crate::util::{err_span_str, unsupported_err_span};
use crate::{unsupported, unsupported_err_unless};
use rustc_ast::Mutability;
use rustc_hir::definitions::DefPath;
use rustc_hir::{
    GenericParam, GenericParamKind, Generics, HirId, ItemKind, QPath, TraitFn, TraitItemKind, Ty,
    Visibility, VisibilityKind,
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::GenericParamDefKind;
use rustc_middle::ty::ProjectionPredicate;
use rustc_middle::ty::ProjectionTy;
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind};
use rustc_middle::ty::{BoundConstness, ImplPolarity, PredicateKind, TraitPredicate};
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_span::symbol::{kw, Ident};
use rustc_span::{Span, Symbol};
use rustc_trait_selection::infer::InferCtxtExt;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{
    GenericBoundX, IntRange, Path, PathX, Primitive, Typ, TypBounds, TypX, Typs, VirErr,
};
use vir::ast_util::types_equal;
use vir::def::unique_local_name;

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

fn get_function_def_impl_item_node<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: rustc_hir::HirId,
) -> Option<(&'tcx rustc_hir::FnSig<'tcx>, &'tcx rustc_hir::BodyId)> {
    let node = tcx.hir().get(hir_id);
    match node {
        rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
            kind: rustc_hir::ImplItemKind::Fn(fn_sig, body_id),
            ..
        }) => Some((fn_sig, body_id)),
        _ => None,
    }
}

pub(crate) fn get_function_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: rustc_hir::HirId,
) -> (&'tcx rustc_hir::FnSig<'tcx>, &'tcx rustc_hir::BodyId) {
    get_function_def_impl_item_node(tcx, hir_id)
        .or_else(|| match tcx.hir().get(hir_id) {
            rustc_hir::Node::Item(item) => match &item.kind {
                ItemKind::Fn(fn_sig, _, body_id) => Some((fn_sig, body_id)),
                _ => None,
            },
            rustc_hir::Node::TraitItem(item) => match &item.kind {
                TraitItemKind::Fn(fn_sig, TraitFn::Provided(body_id)) => Some((fn_sig, body_id)),
                _ => None,
            },
            node => unsupported!("extern functions, or other function Node", node),
        })
        .expect("function expected")
}

pub(crate) fn typ_path_and_ident_to_vir_path<'tcx>(path: &Path, ident: vir::ast::Ident) -> Path {
    let mut path = (**path).clone();
    Arc::make_mut(&mut path.segments).push(ident);
    Arc::new(path)
}

pub(crate) fn fn_item_hir_id_to_self_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: HirId,
) -> Option<DefId> {
    let parent_id = tcx.hir().get_parent_node(hir_id);
    let parent_node = tcx.hir().get(parent_id);
    match parent_node {
        rustc_hir::Node::Item(rustc_hir::Item {
            kind: rustc_hir::ItemKind::Impl(impll), ..
        }) => match &impll.self_ty.kind {
            rustc_hir::TyKind::Path(QPath::Resolved(
                None,
                rustc_hir::Path { res: rustc_hir::def::Res::Def(_, self_def_id), .. },
            )) => Some(*self_def_id),
            _ => {
                panic!("impl type is not given by a path");
            }
        },
        _ => None,
    }
}

pub(crate) fn fn_item_hir_id_to_self_path<'tcx>(tcx: TyCtxt<'tcx>, hir_id: HirId) -> Option<Path> {
    let parent_id = tcx.hir().get_parent_node(hir_id);
    let parent_node = tcx.hir().get(parent_id);
    match parent_node {
        rustc_hir::Node::Item(rustc_hir::Item {
            kind: rustc_hir::ItemKind::Impl(impll),
            def_id,
            ..
        }) => match &impll.self_ty.kind {
            rustc_hir::TyKind::Path(QPath::Resolved(
                None,
                rustc_hir::Path { res: rustc_hir::def::Res::Def(_, self_def_id), .. },
            )) => Some(def_path_to_vir_path(tcx, tcx.def_path(*self_def_id))),
            _ => {
                // To handle cases like [T] which are not syntactically datatypes
                // but converted into VIR datatypes.

                let self_ty = tcx.type_of(def_id.to_def_id());
                let vir_ty = mid_ty_to_vir_ghost(tcx, self_ty, false).0;
                match &*vir_ty {
                    TypX::Datatype(p, _typ_args) => Some(p.clone()),
                    _ => panic!("impl type is not given by a path"),
                }
            }
        },
        _ => None,
    }
}

pub(crate) fn def_id_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Path {
    // The path that rustc gives a DefId might be given in terms of an 'impl' path
    // However, it makes for a better path name to use the path to the *type*.
    // So first, we check if the given DefId is the definition of a fn inside an impl.
    // If so, we construct a VIR path based on the VIR path for the type.
    if let Some(local_id) = def_id.as_local() {
        let hir = tcx.hir().local_def_id_to_hir_id(local_id);
        if get_function_def_impl_item_node(tcx, hir).is_some() {
            if let Some(ty_path) = fn_item_hir_id_to_self_path(tcx, hir) {
                return typ_path_and_ident_to_vir_path(&ty_path, def_to_path_ident(tcx, def_id));
            }
        }
    }
    // Otherwise build a path based on the segments rustc gives us
    // without doing anything fancy.
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

// TODO: proper handling of def_ids
// use https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.lang_items ?
pub(crate) fn hack_get_def_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    let debug_name = tcx.def_path_debug_str(def_id);
    let last_colon = debug_name.rfind(':').unwrap();
    debug_name[last_colon + 1..].to_string()
}

pub(crate) fn foreign_param_to_var<'tcx>(ident: &Ident) -> String {
    ident.to_string()
}

pub(crate) fn local_to_var<'tcx>(
    ident: &Ident,
    local_id: rustc_hir::hir_id::ItemLocalId,
) -> String {
    unique_local_name(ident.to_string(), local_id.index())
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
    inherited_is_private: bool,
) -> vir::ast::Visibility {
    vir::ast::Visibility {
        owning_module: owning_module.clone(),
        is_private: is_visibility_private(&vis.node, inherited_is_private),
    }
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

pub(crate) fn mid_ty_simplify<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> rustc_middle::ty::Ty<'tcx> {
    match ty.kind() {
        TyKind::Ref(_, t, Mutability::Not) => mid_ty_simplify(tcx, t, allow_mut_ref),
        TyKind::Ref(_, t, Mutability::Mut) if allow_mut_ref => {
            mid_ty_simplify(tcx, t, allow_mut_ref)
        }
        TyKind::Adt(AdtDef { did, .. }, args) => {
            let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, *did));
            let is_box = Some(*did) == tcx.lang_items().owned_box() && args.len() == 2;
            let is_smart_ptr = (def_name == "alloc::rc::Rc"
                || def_name == "alloc::sync::Arc"
                || def_name == "builtin::Ghost"
                || def_name == "builtin::Tracked")
                && args.len() == 1;
            if is_box || is_smart_ptr {
                if let rustc_middle::ty::subst::GenericArgKind::Type(t) = args[0].unpack() {
                    mid_ty_simplify(tcx, t, false)
                } else {
                    panic!("unexpected type argument")
                }
            } else {
                ty
            }
        }
        _ => ty,
    }
}

// TODO review and cosolidate type translation, e.g. with `ty_to_vir`, if possible

// returns VIR Typ and whether Ghost/Tracked was erased from around the outside of the VIR Typ
pub(crate) fn mid_ty_to_vir_ghost<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> (Typ, bool) {
    match ty.kind() {
        TyKind::Bool => (Arc::new(TypX::Bool), false),
        TyKind::Uint(_) | TyKind::Int(_) => (Arc::new(TypX::Int(mk_range(ty))), false),
        TyKind::Ref(_, tys, rustc_ast::Mutability::Not) => {
            mid_ty_to_vir_ghost(tcx, tys, allow_mut_ref)
        }
        TyKind::Ref(_, tys, rustc_ast::Mutability::Mut) if allow_mut_ref => {
            mid_ty_to_vir_ghost(tcx, tys, allow_mut_ref)
        }
        TyKind::Param(param) if param.name == kw::SelfUpper => {
            (Arc::new(TypX::TypParam(vir::def::trait_self_type_param())), false)
        }
        TyKind::Param(param) => {
            (Arc::new(TypX::TypParam(Arc::new(param_ty_to_vir_name(param)))), false)
        }
        TyKind::Never => {
            // All types are inhabited in SMT; we pick an arbitrary inhabited type for Never
            (Arc::new(TypX::Tuple(Arc::new(vec![]))), false)
        }
        TyKind::Tuple(_) => {
            let typs: Vec<Typ> =
                ty.tuple_fields().map(|t| mid_ty_to_vir_ghost(tcx, t, allow_mut_ref).0).collect();
            (Arc::new(TypX::Tuple(Arc::new(typs))), false)
        }
        TyKind::Slice(ty) => {
            let typ = mid_ty_to_vir_ghost(tcx, ty, allow_mut_ref).0;
            let typs = Arc::new(vec![typ]);
            (Arc::new(TypX::Primitive(Primitive::Slice, typs)), false)
        }
        TyKind::Array(ty, const_len) => {
            let typ = mid_ty_to_vir_ghost(tcx, ty, allow_mut_ref).0;
            let len = mid_ty_const_to_vir(tcx, const_len);
            let typs = Arc::new(vec![typ, len]);
            (Arc::new(TypX::Primitive(Primitive::Array, typs)), false)
        }
        TyKind::Adt(AdtDef { did, .. }, args) => {
            let s = ty.to_string();
            let is_strslice =
                tcx.is_diagnostic_item(Symbol::intern("pervasive::string::StrSlice"), *did);
            if is_strslice {
                return (Arc::new(TypX::StrSlice), false);
            }
            // TODO use lang items instead of string comparisons
            if s == crate::typecheck::BUILTIN_INT {
                (Arc::new(TypX::Int(IntRange::Int)), false)
            } else if s == crate::typecheck::BUILTIN_NAT {
                (Arc::new(TypX::Int(IntRange::Nat)), false)
            } else {
                let typ_args: Vec<(Typ, bool)> = args
                    .iter()
                    .filter_map(|arg| match arg.unpack() {
                        rustc_middle::ty::subst::GenericArgKind::Type(t) => {
                            Some(mid_ty_to_vir_ghost(tcx, t, allow_mut_ref))
                        }
                        rustc_middle::ty::subst::GenericArgKind::Lifetime(_) => None,
                        rustc_middle::ty::subst::GenericArgKind::Const(cnst) => {
                            Some((mid_ty_const_to_vir(tcx, cnst), false))
                        }
                    })
                    .collect();
                if Some(*did) == tcx.lang_items().owned_box() && typ_args.len() == 2 {
                    return typ_args[0].clone();
                }
                let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, *did));
                if (def_name == "alloc::rc::Rc" || def_name == "alloc::sync::Arc")
                    && typ_args.len() == 1
                {
                    return typ_args[0].clone();
                }
                if (def_name == "builtin::Ghost" || def_name == "builtin::Tracked")
                    && typ_args.len() == 1
                {
                    return (typ_args[0].0.clone(), true);
                }
                if def_name == "builtin::FnSpec" {
                    assert!(typ_args.len() == 2);
                    let typ_arg_tuple = typ_args[0].0.clone();
                    let ret_typ = typ_args[1].0.clone();
                    let param_typs = match &*typ_arg_tuple {
                        TypX::Tuple(typs) => typs.clone(),
                        _ => {
                            // TODO proper user-facing error msg here
                            panic!("expected first type argument of FnSpec to be a tuple");
                        }
                    };
                    return (Arc::new(TypX::Lambda(param_typs, ret_typ)), false);
                }
                let typ_args = typ_args.into_iter().map(|(t, _)| t).collect();
                (Arc::new(def_id_to_datatype(tcx, *did, Arc::new(typ_args))), false)
            }
        }
        TyKind::Closure(def, substs) => {
            let sig = substs.as_closure().sig();
            let args: Vec<Typ> = sig
                .inputs()
                .skip_binder()
                .iter()
                .map(|t| mid_ty_to_vir_ghost(tcx, t, allow_mut_ref).0)
                .collect();
            assert!(args.len() == 1);
            let args = match &*args[0] {
                TypX::Tuple(typs) => typs.clone(),
                _ => panic!("expected tuple type"),
            };

            let ret = mid_ty_to_vir_ghost(tcx, sig.output().skip_binder(), allow_mut_ref).0;
            let id = def.as_local().unwrap().local_def_index.index();
            (Arc::new(TypX::AnonymousClosure(args, ret, id)), false)
        }
        TyKind::Char => (Arc::new(TypX::Char), false),
        _ => {
            unsupported!(format!("type {:?}", ty))
        }
    }
}

pub(crate) fn mid_ty_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> Typ {
    mid_ty_to_vir_ghost(tcx, ty, allow_mut_ref).0
}

pub(crate) fn mid_ty_const_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    cnst: &rustc_middle::ty::Const<'tcx>,
) -> Typ {
    use rustc_middle::mir::interpret::{ConstValue, Scalar};
    use rustc_middle::ty::ConstKind;

    let cnst = match cnst.val {
        ConstKind::Unevaluated(unevaluated) => cnst.eval(tcx, tcx.param_env(unevaluated.def.did)),
        _ => cnst,
    };
    match cnst.val {
        ConstKind::Param(param) => Arc::new(TypX::TypParam(Arc::new(param.name.to_string()))),
        ConstKind::Value(ConstValue::Scalar(Scalar::Int(i))) => {
            let c = num_bigint::BigInt::from(i.assert_bits(i.size()));
            Arc::new(TypX::ConstInt(c))
        }
        _ => {
            unsupported!(format!("const type argument {:?}", cnst))
        }
    }
}

pub(crate) fn is_type_std_rc_or_arc<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Adt(AdtDef { did, .. }, _args) => {
            let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, *did));
            if def_name == "alloc::rc::Rc" || def_name == "alloc::sync::Arc" {
                return true;
            }
        }
        _ => {}
    }
    false
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

pub(crate) fn typ_of_node<'tcx>(bctx: &BodyCtxt<'tcx>, id: &HirId, allow_mut_ref: bool) -> Typ {
    mid_ty_to_vir(bctx.ctxt.tcx, bctx.types.node_type(*id), allow_mut_ref)
}

pub(crate) fn typ_of_node_expect_mut_ref<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    id: &HirId,
    span: Span,
) -> Result<Typ, VirErr> {
    let ty = bctx.types.node_type(*id);
    if let TyKind::Ref(_, _tys, rustc_ast::Mutability::Mut) = ty.kind() {
        Ok(mid_ty_to_vir(bctx.ctxt.tcx, ty, true))
    } else {
        err_span_str(span, "a mutable reference is expected here")
    }
}

pub(crate) fn implements_structural<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &'tcx rustc_middle::ty::TyS<'tcx>,
) -> bool {
    let structural_def_id = tcx
        .get_diagnostic_item(rustc_span::Symbol::intern("builtin::Structural"))
        .expect("structural trait is not defined");
    let substs_ref = tcx.mk_substs([].iter());
    let ty_impls_structural = tcx.infer_ctxt().enter(|infcx| {
        infcx
            .type_implements_trait(
                structural_def_id,
                ty,
                substs_ref,
                rustc_middle::ty::ParamEnv::empty(),
            )
            .must_apply_modulo_regions()
    });
    ty_impls_structural
}

// Do equality operations on these operands translate into the SMT solver's == operation?
pub(crate) fn is_smt_equality<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    _span: Span,
    id1: &HirId,
    id2: &HirId,
) -> bool {
    let (t1, t2) = (typ_of_node(bctx, id1, false), typ_of_node(bctx, id2, false));
    match (&*t1, &*t2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(_), TypX::Int(_)) => true,
        (TypX::Char, TypX::Char) => true,
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
    match (&*typ_of_node(bctx, id1, false), &*typ_of_node(bctx, id2, false)) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(_), TypX::Int(_)) => true,
        _ => false,
    }
}

pub(crate) fn check_generic_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
    args: &Vec<rustc_middle::ty::Ty<'tcx>>,
) -> Result<vir::ast::GenericBound, VirErr> {
    if Some(trait_def_id) == tcx.lang_items().sized_trait()
        || Some(trait_def_id) == tcx.lang_items().copy_trait()
        || Some(trait_def_id) == tcx.lang_items().unpin_trait()
        || Some(trait_def_id) == tcx.lang_items().sync_trait()
        || Some(trait_def_id) == tcx.get_diagnostic_item(rustc_span::sym::Send)
    {
        // Rust language marker traits are ignored in VIR
        Ok(Arc::new(GenericBoundX::Traits(vec![])))
    } else {
        // TODO we will actually need to handle these arguments at some point.
        // Right now, this is safe only because Verus does not support having
        // a type implement two instances of the same trait with different type args.
        let _args = args;

        let trait_name = def_id_to_vir_path(tcx, trait_def_id);
        Ok(Arc::new(GenericBoundX::Traits(vec![trait_name])))
    }
}

// These 2 functions map a GenericParamDef or ParamTy to the name we use for that type
// parameter in VIR.
//
// In rustc_middle, all the type params have a symbol and an index.
// The indices are all unique. The symbols are unique for all the user-declared type
// params, but they aren't necessarily unique for synthetic params.
// (A synthetic param is a nameless type parameter created when the user writes
// something like `x: impl SomeTrait`.)
//
// In order to keep the AIR readable, though, we want to use the symbol names when
// possible. So:
//  - For synthetic params, use impl%{index} for the name.
//  - For other type params, just use the user-given type param name.

fn generic_param_def_to_vir_name(gen: &rustc_middle::ty::GenericParamDef) -> String {
    let is_synthetic = match gen.kind {
        GenericParamDefKind::Type { synthetic, .. } => synthetic,
        GenericParamDefKind::Const { .. } => false,
        _ => panic!("expected GenericParamDefKind::Type"),
    };

    if is_synthetic {
        vir::def::PREFIX_IMPL_TYPE_PARAM.to_string() + &gen.index.to_string()
    } else {
        gen.name.as_str().to_string()
    }
}

fn param_ty_to_vir_name(param: &rustc_middle::ty::ParamTy) -> String {
    let name = param.name.as_str();
    if name.starts_with("impl ") {
        vir::def::PREFIX_IMPL_TYPE_PARAM.to_string() + &param.index.to_string()
    } else {
        name.to_string()
    }
}

pub(crate) fn check_generics_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_generics: &'tcx Generics<'tcx>,
    check_that_external_body_datatype_declares_positivity: bool,
    def_id: DefId,
) -> Result<Vec<(vir::ast::Ident, vir::ast::GenericBound, bool)>, VirErr> {
    // TODO the 'predicates' object contains the parent def_id; we can use that
    // to handle all the params and bounds from the impl at once,
    // so then we can handle the case where a method adds extra bounds to an impl
    // type parameter

    let Generics { params: hir_params, where_clause: _, span: _ } = hir_generics;
    let generics = tcx.generics_of(def_id);

    let mut mid_params: Vec<&rustc_middle::ty::GenericParamDef> = vec![];
    for param in generics.params.iter() {
        match &param.kind {
            GenericParamDefKind::Lifetime { .. } => {} // ignore
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {
                mid_params.push(param);
            }
        }
    }

    let hir_params: Vec<&GenericParam> = hir_params
        .iter()
        .filter(|p| {
            match &p.kind {
                GenericParamKind::Lifetime { kind: _ } => false, // ignore
                GenericParamKind::Type { default: _, synthetic: _ } => true,
                GenericParamKind::Const { ty: _, default: _ } => true,
            }
        })
        .collect();

    // For each generic param, we're going to collect all the trait bounds here.
    let mut typ_param_bounds: HashMap<String, Vec<vir::ast::GenericBound>> = HashMap::new();
    for param in mid_params.iter() {
        let id = generic_param_def_to_vir_name(param);
        typ_param_bounds.insert(id, vec![]);
    }

    // Process all trait bounds.
    let predicates = tcx.predicates_of(def_id);
    for (predicate, span) in predicates.predicates.iter() {
        // REVIEW: rustc docs say that skip_binder is "dangerous"
        match predicate.kind().skip_binder() {
            PredicateKind::RegionOutlives(_) | PredicateKind::TypeOutlives(_) => {
                // can ignore lifetime bounds
            }
            PredicateKind::Trait(TraitPredicate {
                trait_ref,
                constness: BoundConstness::NotConst,
                polarity: ImplPolarity::Positive,
            }) => {
                let substs = trait_ref.substs;

                // For a bound like `T: SomeTrait<X, Y, Z>`, then:
                // T should be index 0,
                // X, Y, Z, should be the rest
                // The SomeTrait is given by the def_id

                // Note: I _think_ rustc organizes it this way because
                // T, X, Y, Z are actually all handled symmetrically
                // in the formal theory of Rust's traits;
                // i.e., the `Self` of a trait is actually the same as any of the other
                // type parameters, it's just special in the notation for convenience.
                //
                // Right now Verus only allows `Self` (in the example, `T`) to be a type param,
                // and it doesn't have full support for the other type params, so we special
                // case it here.

                let trait_def_id = trait_ref.def_id;

                let mut iter = substs.types();
                let lhs = iter.next().expect("expect lhs of trait bound");
                let trait_params: Vec<rustc_middle::ty::Ty> = iter.collect();

                if Some(trait_def_id) == tcx.lang_items().fn_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_mut_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_once_trait()
                {
                    // Ignore Fn bounds
                    continue;
                }

                let generic_bound = check_generic_bound(tcx, trait_def_id, &trait_params)?;

                match lhs.kind() {
                    TyKind::Param(param) => {
                        if param.name == kw::SelfUpper {
                            // trait definitions might have more trait bounds on Self
                            // for example `trait X : Y` might have the trait bound Y
                            // which looks like a bound `Self: Y` here.
                            // We currently don't support this.
                            //
                            // On the other hand, any functions inside a trait definition
                            // will all have a trait bound `Self: X`. We _do_ need to support
                            // this - that's fundamental to how traits work.
                            if trait_def_id != def_id && Some(trait_def_id) != predicates.parent {
                                match &*generic_bound {
                                    GenericBoundX::Traits(l) if l.len() == 0 => {}
                                    _ => {
                                        return err_span_str(
                                            *span,
                                            "Verus does not yet support trait bounds on Self",
                                        );
                                    }
                                }
                            }
                        } else {
                            let type_param_name = param_ty_to_vir_name(&param);
                            match typ_param_bounds.get_mut(&type_param_name) {
                                None => {
                                    return err_span_str(
                                        *span,
                                        "could not find this type parameter",
                                    );
                                }
                                Some(r) => {
                                    r.push(generic_bound);
                                }
                            }
                        }
                    }
                    _ => {
                        return err_span_str(
                            *span,
                            "Verus does yet not support trait bounds on types that are not type parameters",
                        );
                    }
                };
            }
            PredicateKind::Projection(ProjectionPredicate {
                projection_ty: ProjectionTy { substs: _, item_def_id },
                ty: _,
            }) => {
                // The trait bound `F: Fn(A) -> B`
                // is really more like a trait bound `F: Fn<A, Output=B>`
                // The trait bounds that use = are called projections.
                // When Rust sees a trait bound like this, it actually creates *two*
                // bounds, a Trait bound for `F: Fn<A>` and a Projection for `Output=B`.
                //
                // We don't handle projections in general right now, but we skip
                // over them to support Fns
                // (What Verus actually cares about is the builtin 'FnWithSpecification'
                // trait which Fn/FnMut/FnOnce all get automatically.)

                if Some(item_def_id) == tcx.lang_items().fn_once_output() {
                    // Do nothing
                } else {
                    return err_span_str(*span, "Verus does yet not support this type of bound");
                }
            }
            _ => {
                return err_span_str(*span, "Verus does yet not support this type of bound");
            }
        }
    }

    let mut typ_params: Vec<(vir::ast::Ident, vir::ast::GenericBound, bool)> = Vec::new();

    // In traits, the first type param is Self. This is handled specially,
    // so we skip it here.
    // (Skipping it also allows the HIR type params and middle type params to line up.)
    let first_param_is_self = mid_params.len() > 0 && mid_params[0].name == kw::SelfUpper;
    let skip_n = if first_param_is_self { 1 } else { 0 };

    assert!(hir_params.len() + skip_n == mid_params.len());

    for (idx, mid_param) in mid_params.iter().skip(skip_n).enumerate() {
        match mid_param.kind {
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {}
            _ => {
                continue;
            }
        }

        // We still need to look at the HIR param because we need to check the attributes.
        let hir_param = &hir_params[idx];

        let vattrs = get_verifier_attrs(tcx.hir().attrs(hir_param.hir_id))?;
        let neg = vattrs.maybe_negative;
        let pos = vattrs.strictly_positive;
        if neg && pos {
            return err_span_str(
                hir_param.span,
                "type parameter cannot be both maybe_negative and strictly_positive",
            );
        }
        let strictly_positive = !neg; // strictly_positive is the default
        let GenericParam { hir_id: _, name: _, bounds: _, span, pure_wrt_drop, kind } = hir_param;

        unsupported_err_unless!(!pure_wrt_drop, *span, "generic pure_wrt_drop");

        if let GenericParamKind::Type { .. } = kind {
            if check_that_external_body_datatype_declares_positivity && !neg && !pos {
                return err_span_str(
                    *span,
                    "in external_body datatype, each type parameter must be either #[verifier(maybe_negative)] or #[verifier(strictly_positive)] (maybe_negative is always safe to use)",
                );
            }
        } else if let GenericParamKind::Const { .. } = kind {
        } else {
            panic!("mid_param is a Type, so we expected the HIR param to be a Type");
        }

        match &mid_param.kind {
            GenericParamDefKind::Const { .. }
            | GenericParamDefKind::Type {
                has_default: false,
                synthetic: true | false,
                object_lifetime_default: _,
            } => {
                // trait/function bounds
                let ident = Arc::new(generic_param_def_to_vir_name(mid_param));

                let mut trait_bounds: Vec<Path> = Vec::new();
                for vir_bound in typ_param_bounds.remove(&*ident).unwrap().into_iter() {
                    match &*vir_bound {
                        GenericBoundX::Traits(ts) => {
                            trait_bounds.extend(ts.clone());
                        }
                    }
                }
                let bound = Arc::new(GenericBoundX::Traits(trait_bounds));
                typ_params.push((ident, bound, strictly_positive));
            }
            _ => {
                panic!("shouldn't get here");
            }
        }
    }
    Ok(typ_params)
}

pub(crate) fn check_generics_bounds_fun<'tcx>(
    tcx: TyCtxt<'tcx>,
    generics: &'tcx Generics<'tcx>,
    def_id: DefId,
) -> Result<TypBounds, VirErr> {
    Ok(Arc::new(
        check_generics_bounds(tcx, generics, false, def_id)?
            .into_iter()
            .map(|(a, b, _)| (a, b))
            .collect(),
    ))
}
