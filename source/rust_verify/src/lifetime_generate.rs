use crate::attributes::{get_ghost_block_opt, get_mode, get_verifier_attrs, GhostBlockAttr};
use crate::erase::{ErasureHints, ResolvedCall};
use crate::rust_to_vir_base::{
    def_id_to_vir_path, local_to_var, mid_ty_const_to_vir, mid_ty_to_vir_datatype,
};
use crate::rust_to_vir_expr::get_adt_res;
use crate::verus_items::{PervasiveItem, RustItem, VerusItem, VerusItems};
use crate::{lifetime_ast::*, verus_items};
use air::ast::AstId;
use air::ast_util::str_ident;
use rustc_ast::{BorrowKind, IsAuto, Mutability};
use rustc_hir::def::{CtorKind, DefKind, Res};
use rustc_hir::{
    AssocItemKind, BindingAnnotation, Block, BlockCheckMode, BodyId, Closure, Crate, Expr,
    ExprKind, FnSig, HirId, Impl, ImplItem, ImplItemKind, ItemKind, Let, MaybeOwner, Node,
    OpaqueTy, OpaqueTyOrigin, OwnerNode, Pat, PatKind, Stmt, StmtKind, TraitFn, TraitItem,
    TraitItemKind, TraitItemRef, TraitRef, UnOp, Unsafety,
};
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{
    AdtDef, BoundRegionKind, BoundVariableKind, Clause, Const, GenericParamDefKind, PredicateKind,
    RegionKind, Ty, TyCtxt, TyKind, TypeckResults, VariantDef,
};
use rustc_span::def_id::DefId;
use rustc_span::symbol::kw;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{AutospecUsage, DatatypeTransparency, Fun, FunX, Function, Mode, Path};
use vir::ast_util::get_field;
use vir::def::VERUS_SPEC;

impl TypX {
    fn mk_unit() -> Typ {
        Box::new(TypX::Tuple(vec![]))
    }

    fn mk_bool() -> Typ {
        Box::new(TypX::Primitive("bool".to_string()))
    }
}

struct Context<'tcx> {
    tcx: TyCtxt<'tcx>,
    verus_items: Arc<VerusItems>,
    types_opt: Option<&'tcx TypeckResults<'tcx>>,
    /// Map each function path to its VIR Function, or to None if it is a #[verifier(external)]
    /// function
    functions: HashMap<Fun, Option<Function>>,
    /// Map each datatype path to its VIR Datatype
    datatypes: HashMap<Path, vir::ast::Datatype>,
    ignored_functions: HashSet<DefId>,
    /// For each struct/enum that implements Copy,
    /// for each GenericParam A say whether clone and copy require A: Clone and A: Copy
    copy_types: HashMap<DefId, Vec<bool>>,
    calls: HashMap<HirId, ResolvedCall>,
    /// Mode of each if/else or match condition, used to decide how to erase if/else and match
    /// condition.  For example, in "if x < 10 { x + 1 } else { x + 2 }", this will record the span
    /// and mode of the expression "x < 10"
    condition_modes: HashMap<HirId, Mode>,
    /// Mode of each variable declaration and use.  For example, in
    /// "if x < 10 { x + 1 } else { x + 2 }", we will have three entries, one for each
    /// occurence of "x"
    var_modes: HashMap<HirId, Mode>,
    ret_spec: Option<bool>,
}

impl<'tcx> Context<'tcx> {
    fn types(&self) -> &'tcx TypeckResults<'tcx> {
        self.types_opt.expect("Context.types")
    }
}

pub(crate) struct State {
    rename_count: usize,
    reached: HashSet<(Option<Path>, DefId)>,
    datatype_worklist: Vec<DefId>,
    imported_fun_worklist: Vec<DefId>,
    id_to_name: HashMap<String, Id>,
    typ_param_to_name: HashMap<(String, Option<u32>), Id>,
    lifetime_to_name: HashMap<(String, Option<u32>), Id>,
    fun_to_name: HashMap<Fun, Id>,
    trait_to_name: HashMap<Path, Id>,
    datatype_to_name: HashMap<Path, Id>,
    variant_to_name: HashMap<String, Id>,
    pub(crate) trait_decl_set: HashSet<Path>,
    pub(crate) trait_decls: Vec<TraitDecl>,
    pub(crate) datatype_decls: Vec<DatatypeDecl>,
    pub(crate) assoc_type_impls: Vec<AssocTypeImpl>,
    pub(crate) fun_decls: Vec<FunDecl>,
    enclosing_fun_id: Option<DefId>,
}

impl State {
    fn new() -> State {
        State {
            rename_count: 0,
            reached: HashSet::new(),
            datatype_worklist: Vec::new(),
            imported_fun_worklist: Vec::new(),
            id_to_name: HashMap::new(),
            typ_param_to_name: HashMap::new(),
            lifetime_to_name: HashMap::new(),
            fun_to_name: HashMap::new(),
            trait_to_name: HashMap::new(),
            datatype_to_name: HashMap::new(),
            variant_to_name: HashMap::new(),
            trait_decl_set: HashSet::new(),
            trait_decls: Vec::new(),
            datatype_decls: Vec::new(),
            assoc_type_impls: Vec::new(),
            fun_decls: Vec::new(),
            enclosing_fun_id: None,
        }
    }

    fn id<Key: Clone + Eq + std::hash::Hash>(
        rename_count: &mut usize,
        key_to_name: &mut HashMap<Key, Id>,
        kind: IdKind,
        key: &Key,
        mk_raw_id: impl Fn() -> String,
    ) -> Id {
        let name = key_to_name.get(key);
        if let Some(name) = name {
            return name.clone();
        }
        *rename_count += 1;
        let name = Id::new(kind, *rename_count, mk_raw_id());
        key_to_name.insert(key.clone(), name.clone());
        name
    }

    fn local<S: Into<String>>(&mut self, raw_id: S) -> Id {
        let raw_id = raw_id.into();
        let f = || raw_id.clone();
        Self::id(&mut self.rename_count, &mut self.id_to_name, IdKind::Local, &raw_id, f)
    }

    fn typ_param<S: Into<String>>(&mut self, raw_id: S, maybe_impl_index: Option<u32>) -> Id {
        let raw_id = raw_id.into();
        let (is_impl, impl_index) = match (raw_id.starts_with("impl "), maybe_impl_index) {
            (false, _) => (false, None),
            (true, None) => panic!("unexpected impl type"),
            (true, Some(i)) => (true, Some(i)),
        };
        let f = || if is_impl { "impl".to_string() } else { raw_id.clone() };
        let key = (raw_id.clone(), impl_index);
        Self::id(&mut self.rename_count, &mut self.typ_param_to_name, IdKind::TypParam, &key, f)
    }

    fn lifetime(&mut self, key: (String, Option<u32>)) -> Id {
        let (raw_id, _maybe_disambiguator) = &key;
        let f = || raw_id.replace("'", "");
        Self::id(&mut self.rename_count, &mut self.lifetime_to_name, IdKind::Lifetime, &key, f)
    }

    fn fun_name<'tcx>(&mut self, fun: &Fun) -> Id {
        let f = || fun.path.segments.last().expect("path").to_string();
        Self::id(&mut self.rename_count, &mut self.fun_to_name, IdKind::Fun, fun, f)
    }

    fn trait_name<'tcx>(&mut self, path: &Path) -> Id {
        let f = || path.segments.last().expect("path").to_string();
        Self::id(&mut self.rename_count, &mut self.trait_to_name, IdKind::Trait, path, f)
    }

    fn datatype_name<'tcx>(&mut self, path: &Path) -> Id {
        if let Some(krate) = &path.krate {
            if krate.to_string() == "builtin" && path.segments.len() == 1 {
                return Id::new(IdKind::Builtin, 0, path.segments[0].to_string());
            }
        }
        let f = || path.segments.last().expect("path").to_string();
        Self::id(&mut self.rename_count, &mut self.datatype_to_name, IdKind::Datatype, path, f)
    }

    fn variant<S: Into<String>>(&mut self, raw_id: S) -> Id {
        let raw_id = raw_id.into();
        let f = || raw_id.clone();
        Self::id(&mut self.rename_count, &mut self.variant_to_name, IdKind::Variant, &raw_id, f)
    }

    pub(crate) fn unmangle_names<S: Into<String>>(&self, s: S) -> String {
        let mut s = s.into();
        for (k, v) in self.id_to_name.iter() {
            let sv = v.to_string();
            if s.contains(&sv) {
                s = s.replace(&sv, vir::def::user_local_name(k));
            }
        }
        for (k, v) in self.datatype_to_name.iter() {
            let sv = v.to_string();
            if s.contains(&sv) {
                s = s.replace(&sv, &k.segments.last().expect("segments").to_string());
            }
        }
        s
    }

    fn reach_datatype(&mut self, ctxt: &Context, id: DefId) {
        if !self.reached.contains(&(None, id)) {
            let crate_name = ctxt.tcx.crate_name(ctxt.tcx.def_path(id).krate).to_string();
            if crate_name != "builtin" {
                self.reached.insert((None, id));
                self.datatype_worklist.push(id);
            }
        }
    }

    fn reach_fun(&mut self, self_path: Option<Path>, id: DefId) {
        if id.as_local().is_none() && !self.reached.contains(&(self_path.clone(), id)) {
            self.reached.insert((self_path.clone(), id));
            self.imported_fun_worklist.push(id);
        }
    }
}

fn span_dummy() -> Span {
    let lo = rustc_span::BytePos(0);
    let hi = rustc_span::BytePos(0);
    let ctxt = rustc_span::SyntaxContext::root();
    let data = rustc_span::SpanData { lo, hi, ctxt, parent: None };
    data.span()
}

fn add_copy_type(ctxt: &mut Context, state: &mut State, id: DefId) {
    let tcx = ctxt.tcx;
    let copy = tcx.lang_items().copy_trait();
    let sized = tcx.lang_items().sized_trait();
    // check for implementation of the form:
    //   impl<A1 ... An> Copy for S<A1 ... An>
    if let Some(trait_ref) = tcx.impl_trait_ref(id) {
        if trait_ref.0.substs.len() == 1 {
            if let GenericArgKind::Type(ty) = trait_ref.0.substs[0].unpack() {
                if let TyKind::Adt(AdtDef(adt_def_data), args) = ty.kind() {
                    let did = adt_def_data.did;
                    let generics = tcx.generics_of(id);
                    let mut copy_bounds: Vec<(Id, bool)> = Vec::new();
                    if generics.params.len() == args.len() {
                        for (param, arg) in generics.params.iter().zip(args.iter()) {
                            let name = state.typ_param(param.name.to_string(), Some(param.index));
                            copy_bounds.push((name, false));
                            if let GenericArgKind::Type(arg_ty) = arg.unpack() {
                                if let TyKind::Param(p) = arg_ty.kind() {
                                    if p.name == param.name {
                                        continue;
                                    }
                                }
                            }
                            return;
                        }
                    } else {
                        return;
                    }
                    for (pred, _) in tcx.predicates_of(id).predicates {
                        if let Some(PredicateKind::Clause(Clause::Trait(p))) =
                            pred.kind().no_bound_vars()
                        {
                            let pid = p.trait_ref.def_id;
                            // For now, only allowed predicates are Copy and Sized
                            if Some(pid) == copy {
                                let x = match *erase_ty(
                                    ctxt,
                                    state,
                                    &p.trait_ref.substs[0].expect_ty(),
                                ) {
                                    TypX::TypParam(x) => x,
                                    _ => panic!("PredicateKind::Trait"),
                                };
                                let x_ref = copy_bounds.iter_mut().find(|(name, _)| name == &x);
                                let x_ref = x_ref.expect("generic param bound");
                                x_ref.1 = true;
                                continue;
                            }
                            if Some(pid) == sized {
                                continue;
                            }
                        }
                        return;
                    }
                    if tcx.impl_polarity(id) != rustc_middle::ty::ImplPolarity::Positive {
                        return;
                    }
                    // Found a matching Copy Impl
                    assert!(!ctxt.copy_types.contains_key(&did));
                    let copy_bounds = copy_bounds.into_iter().map(|(_, copy)| copy).collect();
                    ctxt.copy_types.insert(did, copy_bounds);
                }
            }
        }
    }
}

fn erase_hir_region<'tcx>(ctxt: &Context<'tcx>, state: &mut State, r: &RegionKind) -> Option<Id> {
    match r {
        RegionKind::ReEarlyBound(bound) => Some(state.lifetime((bound.name.to_string(), None))),
        RegionKind::ReLateBound(_, bound) => match bound.kind {
            BoundRegionKind::BrNamed(a, _) => Some(state.lifetime(lifetime_key(ctxt, a))),
            _ => None,
        },
        RegionKind::ReStatic => Some(Id::new(IdKind::Builtin, 0, "'static".to_string())),
        RegionKind::ReErased => None,
        _ => {
            dbg!(r);
            panic!("unexpected region")
        }
    }
}

fn erase_generic_const<'tcx>(ctxt: &Context<'tcx>, state: &mut State, cnst: &Const<'tcx>) -> Typ {
    match &*mid_ty_const_to_vir(ctxt.tcx, None, cnst).expect("mit_ty_const_to_vir failed") {
        vir::ast::TypX::TypParam(x) => {
            Box::new(TypX::TypParam(state.typ_param(x.to_string(), None)))
        }
        vir::ast::TypX::ConstInt(i) => Box::new(TypX::Primitive(i.to_string())),
        _ => panic!("GenericArgKind::Const"),
    }
}

fn erase_ty<'tcx>(ctxt: &Context<'tcx>, state: &mut State, ty: &Ty<'tcx>) -> Typ {
    match ty.kind() {
        TyKind::Bool | TyKind::Uint(_) | TyKind::Int(_) | TyKind::Char | TyKind::Str => {
            Box::new(TypX::Primitive(ty.to_string()))
        }
        TyKind::Param(p) if p.name == kw::SelfUpper => {
            Box::new(TypX::TypParam(state.typ_param("Self", None)))
        }
        TyKind::Param(p) => {
            let name = p.name.as_str();
            Box::new(TypX::TypParam(state.typ_param(name.to_string(), Some(p.index))))
        }
        TyKind::Never => Box::new(TypX::Never),
        TyKind::Ref(region, t, mutability) => {
            let lifetime = erase_hir_region(ctxt, state, region);
            Box::new(TypX::Ref(erase_ty(ctxt, state, t), lifetime, *mutability))
        }
        TyKind::Slice(t) => Box::new(TypX::Slice(erase_ty(ctxt, state, t))),
        TyKind::Array(t, len_const) => {
            let t = erase_ty(ctxt, state, t);
            let t_len = erase_generic_const(ctxt, state, len_const);
            Box::new(TypX::Array(t, t_len))
        }
        TyKind::Tuple(_) => Box::new(TypX::Tuple(
            ty.tuple_fields().iter().map(|t| erase_ty(ctxt, state, &t)).collect(),
        )),
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let did = adt_def_data.did;
            state.reach_datatype(ctxt, did);
            let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, did);

            let rust_item = verus_items::get_rust_item(ctxt.tcx, did);
            let mut typ_args: Vec<Typ> = Vec::new();

            let args = if rust_item == Some(RustItem::Box) {
                // For Box, skip the second argument (the Allocator)
                // which is currently restricted to always be `Global`.
                assert!(args.len() == 2);
                &args[0..1]
            } else {
                &args
            };

            for arg in args.iter() {
                match arg.unpack() {
                    rustc_middle::ty::subst::GenericArgKind::Type(t) => {
                        typ_args.push(erase_ty(ctxt, state, &t));
                    }
                    rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                        let lifetime = erase_hir_region(ctxt, state, &region);
                        if let Some(lifetime) = lifetime {
                            typ_args.push(Box::new(TypX::TypParam(lifetime)));
                        } else {
                            typ_args.push(Box::new(TypX::Primitive("'_".to_string())));
                        }
                    }
                    rustc_middle::ty::subst::GenericArgKind::Const(cnst) => {
                        let t = erase_generic_const(ctxt, state, &cnst);
                        typ_args.push(t);
                    }
                }
            }
            let datatype_name = match rust_item {
                Some(RustItem::Box) => {
                    assert!(typ_args.len() == 1);
                    Id::new(IdKind::Builtin, 0, "Box".to_owned())
                }
                Some(RustItem::Rc) => {
                    assert!(typ_args.len() == 1);
                    Id::new(IdKind::Builtin, 0, "Rc".to_owned())
                }
                Some(RustItem::Arc) => {
                    assert!(typ_args.len() == 1);
                    Id::new(IdKind::Builtin, 0, "Arc".to_owned())
                }
                _ => state.datatype_name(&path),
            };
            Box::new(TypX::Datatype(datatype_name, typ_args))
        }
        TyKind::Alias(rustc_middle::ty::AliasKind::Projection, t) => {
            // Note: even if rust_to_vir_base decides to normalize t,
            // we don't have to normalize t here, since we're generating Rust code, not VIR.
            let assoc_item = ctxt.tcx.associated_item(t.def_id);
            let name = state.typ_param(assoc_item.name.to_string(), None);
            let trait_def = ctxt.tcx.generics_of(t.def_id).parent;
            match (trait_def, t.substs.try_as_type_list()) {
                (Some(trait_def), Some(typs)) if typs.len() >= 1 => {
                    let trait_path_vir = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, trait_def);
                    assert!(state.trait_decl_set.contains(&trait_path_vir));
                    let trait_path = state.trait_name(&trait_path_vir);
                    let mut typs_iter = typs.iter();
                    let self_ty = typs_iter.next().unwrap();
                    let self_typ = erase_ty(ctxt, state, &self_ty);
                    let mut trait_typ_args = Vec::new();
                    for ty in typs_iter {
                        let t = erase_ty(ctxt, state, &ty);
                        trait_typ_args.push(t);
                    }
                    let trait_as_datatype = Box::new(TypX::Datatype(trait_path, trait_typ_args));
                    Box::new(TypX::Projection { self_typ, trait_as_datatype, name })
                }
                _ => panic!("unexpected TyKind::Alias"),
            }
        }
        TyKind::Closure(..) => Box::new(TypX::Closure),
        _ => {
            dbg!(ty);
            panic!("unexpected type")
        }
    }
}

fn erase_pat<'tcx>(ctxt: &Context<'tcx>, state: &mut State, pat: &Pat) -> Pattern {
    let mk_pat = |p: PatternX| Box::new((pat.span, p));
    match &pat.kind {
        PatKind::Wild => mk_pat(PatternX::Wildcard),
        PatKind::Binding(ann, hir_id, x, None) => {
            let id = state.local(local_to_var(x, hir_id.local_id));
            let BindingAnnotation(_, mutability) = ann;
            mk_pat(PatternX::Binding(id, mutability.to_owned()))
        }
        PatKind::Path(qpath) => {
            let res = ctxt.types().qpath_res(qpath, pat.hir_id);
            let (adt_def_id, variant_def, is_enum) = get_adt_res(ctxt.tcx, res, pat.span).unwrap();
            let variant_name = str_ident(&variant_def.ident(ctxt.tcx).as_str());
            let vir_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, adt_def_id);

            let name = state.datatype_name(&vir_path);
            let variant =
                if is_enum { Some(state.variant(variant_name.to_string())) } else { None };
            mk_pat(PatternX::DatatypeTuple(name, variant, vec![], None))
        }
        PatKind::Box(p) => mk_pat(PatternX::Box(erase_pat(ctxt, state, p))),
        PatKind::Or(pats) => {
            let mut patterns: Vec<Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(erase_pat(ctxt, state, pat));
            }
            mk_pat(PatternX::Or(patterns))
        }
        PatKind::Tuple(pats, dot_dot_pos) => {
            let mut patterns: Vec<Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(erase_pat(ctxt, state, pat));
            }
            mk_pat(PatternX::Tuple(patterns, dot_dot_pos.as_opt_usize()))
        }
        PatKind::TupleStruct(qpath, pats, dot_dot_pos) => {
            let res = ctxt.types().qpath_res(qpath, pat.hir_id);
            let (adt_def_id, variant_def, is_enum) = get_adt_res(ctxt.tcx, res, pat.span).unwrap();
            let variant_name = str_ident(&variant_def.ident(ctxt.tcx).as_str());
            let vir_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, adt_def_id);

            let name = state.datatype_name(&vir_path);
            let variant_name = state.variant(variant_name.to_string());
            let mut patterns: Vec<Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(erase_pat(ctxt, state, pat));
            }
            let variant = if is_enum { Some(variant_name) } else { None };
            mk_pat(PatternX::DatatypeTuple(name, variant, patterns, dot_dot_pos.as_opt_usize()))
        }
        PatKind::Struct(qpath, pats, has_omitted) => {
            let res = ctxt.types().qpath_res(qpath, pat.hir_id);
            let (adt_def_id, variant_def, is_enum) = get_adt_res(ctxt.tcx, res, pat.span).unwrap();
            let variant_name = str_ident(&variant_def.ident(ctxt.tcx).as_str());
            let vir_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, adt_def_id);

            let variant_opt =
                if is_enum { Some(state.variant(variant_name.to_string())) } else { None };

            let name = state.datatype_name(&vir_path);
            let mut binders: Vec<(Id, Pattern)> = Vec::new();
            for pat in pats.iter() {
                let field = state.local(pat.ident.to_string());
                let pattern = erase_pat(ctxt, state, &pat.pat);
                binders.push((field, pattern));
            }
            mk_pat(PatternX::DatatypeStruct(name, variant_opt, binders, *has_omitted))
        }
        _ => {
            dbg!(pat);
            panic!("unexpected pattern")
        }
    }
}

fn erase_spec_exps_typ<'tcx>(
    _ctxt: &Context,
    state: &mut State,
    span: Span,
    mk_typ: impl FnOnce(&mut State) -> Typ,
    exps: Vec<Option<Exp>>,
    force_some: bool,
) -> Option<Exp> {
    let mk_exp = |e: ExpX| Some(Box::new((span, e)));

    let mut is_some: bool = false;
    let mut args: Vec<Exp> = Vec::new();
    for exp in exps.into_iter() {
        if let Some(exp) = exp {
            args.push(exp);
            is_some = true;
        }
    }
    if is_some || force_some { mk_exp(ExpX::Op(args, mk_typ(state))) } else { None }
}

// Return an Exp instead of an Option<Exp>
// (in particulary, instead of returning None, return a dummy expression with the intended type)
fn erase_spec_exps_force_typ<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    span: Span,
    typ: Typ,
    exps: Vec<Option<Exp>>,
) -> Exp {
    erase_spec_exps_typ(ctxt, state, span, |_| typ, exps, true).expect("erase expr force")
}

fn erase_spec_exps_force<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    expr: &Expr<'tcx>,
    exps: Vec<Option<Exp>>,
) -> Exp {
    let expr_typ = |state: &mut State| erase_ty(ctxt, state, &ctxt.types().node_type(expr.hir_id));
    erase_spec_exps_typ(ctxt, state, expr.span, expr_typ, exps, true).expect("erase expr force")
}

fn erase_spec_exps<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    expr: &Expr<'tcx>,
    exps: Vec<Option<Exp>>,
) -> Option<Exp> {
    let expr_typ = |state: &mut State| erase_ty(ctxt, state, &ctxt.types().node_type(expr.hir_id));
    erase_spec_exps_typ(ctxt, state, expr.span, expr_typ, exps, false)
}

fn phantom_data_expr<'tcx>(ctxt: &Context<'tcx>, state: &mut State, expr: &Expr<'tcx>) -> Exp {
    let e = erase_expr(ctxt, state, true, expr);
    let ty = ctxt.types().node_type(expr.hir_id);
    let typ = Box::new(TypX::Phantom(erase_ty(ctxt, state, &ty)));
    erase_spec_exps_force_typ(ctxt, state, expr.span, typ, vec![e])
}

// Convert an Option<Exp> into an Exp by converting None into an empty block
// (useful for Rust expressions that require blocks, like if or while)
fn force_block(exp: Option<Exp>, span: Span) -> Exp {
    match exp {
        None => Box::new((span, ExpX::Block(vec![], None))),
        Some(exp @ box (_, ExpX::Block(..))) => exp,
        Some(exp @ box (span, _)) => Box::new((span, ExpX::Block(vec![], Some(exp)))),
    }
}

// Convert an Option<Exp> into an Exp by converting None into a unit value
fn force_exp(exp: Option<Exp>, span: Span) -> Exp {
    match exp {
        None => Box::new((span, ExpX::Tuple(vec![]))),
        Some(e) => e,
    }
}

fn mk_typ_args<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    node_substs: &[rustc_middle::ty::subst::GenericArg<'tcx>],
) -> Vec<Typ> {
    let mut typ_args: Vec<Typ> = Vec::new();
    for typ_arg in node_substs {
        match typ_arg.unpack() {
            GenericArgKind::Type(ty) => {
                typ_args.push(erase_ty(ctxt, state, &ty));
            }
            GenericArgKind::Lifetime(_) => {}
            GenericArgKind::Const(c) => {
                typ_args.push(erase_generic_const(ctxt, state, &c));
            }
        }
    }
    typ_args
}

fn erase_call<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr<'tcx>,
    self_path: Option<Path>,
    expr_fun: Option<&Expr<'tcx>>,
    fn_def_id: Option<DefId>,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg<'tcx>>,
    fn_span: Span,
    receiver: Option<&Expr<'tcx>>,
    args_slice: &'tcx [Expr<'tcx>],
    is_method: bool,
    is_variant: bool,
) -> Option<Exp> {
    let mut is_some: bool = false;
    let mk_exp = |e: ExpX| Some(Box::new((expr.span, e)));
    let call = ctxt
        .calls
        .get(&expr.hir_id)
        .unwrap_or_else(|| panic!("internal error: missing function: {:?}", fn_span));
    match call {
        ResolvedCall::Spec => None,
        ResolvedCall::SpecAllowProofArgs => {
            let exps = receiver
                .into_iter()
                .chain(args_slice.iter())
                .map(|a| erase_expr(ctxt, state, expect_spec, a))
                .collect(); // REVIEW(main_new) correct?
            erase_spec_exps_typ(ctxt, state, expr.span, |_| TypX::mk_unit(), exps, false)
        }
        ResolvedCall::CompilableOperator(op) => {
            use crate::erase::CompilableOperator::*;
            let builtin_method = match op {
                SmartPtrClone => Some("clone"),
                TrackedGet => Some("get"),
                TrackedBorrow => Some("borrow"),
                TrackedBorrowMut => Some("borrow_mut"),
                GhostExec | TrackedNew | TrackedExec | TrackedExecBorrow => None,
                IntIntrinsic | Implies | SmartPtrNew | NewStrLit => None,
                GhostSplitTuple | TrackedSplitTuple => None,
            };
            assert!(builtin_method.is_some() == is_method);
            if let Some(method) = builtin_method {
                assert!(receiver.is_some());
                assert!(args_slice.len() == 0);
                let Some(receiver) = receiver else { panic!() };
                let exp = erase_expr(ctxt, state, expect_spec, &receiver).expect("builtin method");
                mk_exp(ExpX::BuiltinMethod(exp, method.to_string()))
            } else if let GhostExec = op {
                Some(erase_spec_exps_force(ctxt, state, expr, vec![]))
            } else {
                assert!(receiver.is_none());
                let exps =
                    args_slice.iter().map(|a| erase_expr(ctxt, state, expect_spec, a)).collect();
                erase_spec_exps(ctxt, state, expr, exps)
            }
        }
        ResolvedCall::Call(f_name, autospec_usage) => {
            if !ctxt.functions.contains_key(f_name) {
                panic!("internal error: function call to {:?} not found {:?}", f_name, expr.span);
            }
            let f = &ctxt.functions[f_name];
            let f = if let Some(f) = f {
                f
            } else {
                panic!("internal error: call to external function {:?} {:?}", f_name, expr.span);
            };

            let (f_name, f) = match (autospec_usage, &f.x.attrs.autospec) {
                (AutospecUsage::IfMarked, Some(new_f_name)) => {
                    let f = &ctxt.functions[new_f_name];
                    let f = if let Some(f) = f {
                        f
                    } else {
                        panic!(
                            "internal error: call to external function {:?} {:?}",
                            f_name, expr.span
                        );
                    };
                    (new_f_name.clone(), f.clone())
                }
                _ => (f_name.clone(), f.clone()),
            };

            if f.x.mode == Mode::Spec {
                return None;
            }

            // Maybe resolve from trait function to a specific implementation

            let mut node_substs = node_substs;
            let mut fn_def_id = fn_def_id.expect("call id");

            let param_env = ctxt.tcx.param_env(state.enclosing_fun_id.expect("enclosing_fun_id"));
            let normalized_substs = ctxt.tcx.normalize_erasing_regions(param_env, node_substs);
            let inst = rustc_middle::ty::Instance::resolve(
                ctxt.tcx,
                param_env,
                fn_def_id,
                normalized_substs,
            );
            if let Ok(Some(inst)) = inst {
                if let rustc_middle::ty::InstanceDef::Item(item) = inst.def {
                    if let rustc_middle::ty::WithOptConstParam { did, const_param_did: None } = item
                    {
                        node_substs = &inst.substs;
                        fn_def_id = did;
                    }
                }
            }

            state.reach_fun(self_path, fn_def_id);

            let typ_args = mk_typ_args(ctxt, state, node_substs);
            let mut exps: Vec<Exp> = Vec::new();
            let mut is_first: bool = true;
            assert!(receiver.map(|_| 1).unwrap_or(0) + args_slice.len() == f.x.params.len());
            for (param, e) in f.x.params.iter().zip(receiver.into_iter().chain(args_slice.iter())) {
                if param.x.mode == Mode::Spec {
                    let exp = erase_expr(ctxt, state, true, e);
                    is_some = is_some || exp.is_some();
                    exps.push(erase_spec_exps_force_typ(
                        ctxt,
                        state,
                        e.span,
                        TypX::mk_unit(),
                        vec![exp],
                    ));
                } else {
                    let mut exp = erase_expr(ctxt, state, false, e).expect("expr");
                    if is_first && is_method {
                        let adjustments = ctxt.types().expr_adjustments(e);
                        if adjustments.len() == 1 {
                            use rustc_middle::ty::adjustment::{
                                Adjust, AutoBorrow, AutoBorrowMutability,
                            };
                            match adjustments[0].kind {
                                Adjust::Borrow(AutoBorrow::Ref(_, m)) => {
                                    let m = match m {
                                        AutoBorrowMutability::Not => Mutability::Not,
                                        AutoBorrowMutability::Mut { .. } => Mutability::Mut,
                                    };
                                    exp = Box::new((exp.0, ExpX::AddrOf(m, exp)));
                                }
                                _ => {}
                            }
                        }
                    }
                    exps.push(exp);
                    is_some = true;
                }
                is_first = false;
            }
            if expect_spec && !is_some {
                None
            } else {
                let name = state.fun_name(&f_name);
                let target = Box::new((fn_span, ExpX::Var(name)));
                mk_exp(ExpX::Call(target, typ_args, exps))
            }
        }
        ResolvedCall::Ctor(path, variant_name) => {
            assert!(receiver.is_none());
            if expect_spec {
                let mut exps: Vec<Option<Exp>> = Vec::new();
                for arg in args_slice.iter() {
                    exps.push(erase_expr(ctxt, state, expect_spec, arg));
                }
                erase_spec_exps(ctxt, state, expr, exps)
            } else {
                let datatype = &ctxt.datatypes[path];
                let variant = datatype.x.get_variant(variant_name);
                let typ_args = mk_typ_args(ctxt, state, node_substs);
                let mut args: Vec<Exp> = Vec::new();
                for (field, arg) in variant.a.iter().zip(args_slice.iter()) {
                    let (_, field_mode, _) = field.a;
                    let e = if field_mode == Mode::Spec {
                        phantom_data_expr(ctxt, state, arg)
                    } else {
                        erase_expr(ctxt, state, expect_spec, arg).expect("expr")
                    };
                    args.push(e);
                }
                // make sure datatype is generated
                let _ = erase_ty(ctxt, state, &ctxt.types().node_type(expr.hir_id));
                let variant_opt =
                    if is_variant { Some(state.variant(variant_name.to_string())) } else { None };
                mk_exp(ExpX::DatatypeTuple(state.datatype_name(path), variant_opt, typ_args, args))
            }
        }
        ResolvedCall::NonStaticExec => {
            assert!(receiver.is_none());
            let expr_fun = expr_fun.expect("exec closure call function target");
            let exp_fun = erase_expr(ctxt, state, false, expr_fun).expect("closure call target");
            let typ_args = mk_typ_args(ctxt, state, node_substs);
            let exps = args_slice
                .iter()
                .map(|a| erase_expr(ctxt, state, false, a).expect("call arg"))
                .collect();
            // syntax quirk: need extra parens when exp_fun is a block
            let exp_fun = Box::new((expr_fun.span, ExpX::ExtraParens(exp_fun)));
            mk_exp(ExpX::Call(exp_fun, typ_args, exps))
        }
    }
}

fn erase_match<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr<'tcx>,
    cond: &Expr<'tcx>,
    arms: Vec<(Option<&Pat<'tcx>>, &Option<rustc_hir::Guard<'tcx>>, Option<&Expr<'tcx>>)>,
) -> Option<Exp> {
    let expr_typ = |state: &mut State| erase_ty(ctxt, state, &ctxt.types().node_type(expr.hir_id));
    let mk_exp1 = |e: ExpX| Box::new((expr.span, e));
    let mk_exp = |e: ExpX| Some(Box::new((expr.span, e)));
    let mut is_some_arms = false;
    let cond_spec = ctxt.condition_modes[&expr.hir_id] == Mode::Spec;
    let ec = erase_expr(ctxt, state, cond_spec, cond);
    let mut e_arms: Vec<(Pattern, Option<Exp>, Exp)> = Vec::new();
    for (pat_opt, guard_opt, body_expr) in arms.iter() {
        let pattern = if let Some(pat) = pat_opt {
            erase_pat(ctxt, state, pat)
        } else {
            Box::new((span_dummy(), PatternX::Wildcard))
        };
        let guard = match guard_opt {
            None => None,
            Some(rustc_hir::Guard::If(guard)) => erase_expr(ctxt, state, cond_spec, guard),
            _ => panic!("unexpected guard"),
        };
        let (body, body_span) = if let Some(b) = body_expr {
            (erase_expr(ctxt, state, expect_spec, b), b.span)
        } else {
            (None, span_dummy())
        };
        is_some_arms = is_some_arms || body.is_some();
        e_arms.push((pattern, guard, force_block(body, body_span)));
    }
    if expect_spec && !is_some_arms {
        erase_spec_exps(ctxt, state, expr, vec![ec])
    } else {
        if expect_spec && e_arms.len() < arms.len() {
            // add default case
            let pattern = Box::new((span_dummy(), PatternX::Wildcard));
            let body = Box::new((span_dummy(), ExpX::Op(vec![], expr_typ(state))));
            e_arms.push((pattern, None, body));
        }
        let c = match ec {
            None => {
                let ctyp = ctxt.types().node_type(cond.hir_id);
                mk_exp1(ExpX::Op(vec![], erase_ty(ctxt, state, &ctyp)))
            }
            Some(e) => e,
        };
        mk_exp(ExpX::Match(c, e_arms))
    }
}

fn erase_inv_block<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    span: Span,
    body: &Block<'tcx>,
) -> Exp {
    assert!(body.stmts.len() == 3);
    let open_stmt = &body.stmts[0];
    let mid_stmt = &body.stmts[1];
    let (_guard_hir, _inner_hir, inner_pat, arg, atomicity) =
        crate::rust_to_vir_expr::invariant_block_open(&ctxt.verus_items, open_stmt)
            .expect("invariant_block_open");
    let pat_typ = erase_ty(ctxt, state, &ctxt.types().node_type(inner_pat.hir_id));
    let inner_pat = erase_pat(ctxt, state, inner_pat);
    let arg = erase_expr(ctxt, state, false, arg).expect("erase_inv_block arg");
    let mid_body = erase_stmt(ctxt, state, mid_stmt);
    Box::new((span, ExpX::OpenInvariant(atomicity, inner_pat, arg, pat_typ, mid_body)))
}

fn erase_expr<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr<'tcx>,
) -> Option<Exp> {
    let expr = expr.peel_drop_temps();
    let expr_typ = |state: &mut State| erase_ty(ctxt, state, &ctxt.types().node_type(expr.hir_id));
    let mk_exp1 = |e: ExpX| Box::new((expr.span, e));
    let mk_exp = |e: ExpX| Some(Box::new((expr.span, e)));

    match &expr.kind {
        ExprKind::Path(qpath) => {
            let res = ctxt.types().qpath_res(qpath, expr.hir_id);

            match res {
                Res::Local(id) => match ctxt.tcx.hir().get(id) {
                    Node::Pat(Pat { kind: PatKind::Binding(_ann, id, ident, _pat), .. }) => {
                        if expect_spec || ctxt.var_modes[&expr.hir_id] == Mode::Spec {
                            None
                        } else {
                            mk_exp(ExpX::Var(state.local(local_to_var(&ident, id.local_id))))
                        }
                    }
                    _ => panic!("unsupported"),
                },
                Res::SelfCtor(_) | Res::Def(DefKind::Ctor(_, _), _) => {
                    let (adt_def_id, variant_def, is_enum) =
                        get_adt_res(ctxt.tcx, res, expr.span).unwrap();
                    let variant_name = str_ident(&variant_def.ident(ctxt.tcx).as_str());
                    let vir_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, adt_def_id);

                    let variant =
                        if is_enum { Some(state.variant(variant_name.to_string())) } else { None };
                    let typ_args = mk_typ_args(ctxt, state, ctxt.types().node_substs(expr.hir_id));
                    return mk_exp(ExpX::DatatypeTuple(
                        state.datatype_name(&vir_path),
                        variant,
                        typ_args,
                        vec![],
                    ));
                }
                Res::Def(DefKind::AssocConst, _id) => {
                    if expect_spec {
                        None
                    } else {
                        let typ = expr_typ(state);
                        assert!(matches!(*typ, TypX::Primitive(_)));
                        mk_exp(ExpX::Op(vec![], typ))
                    }
                }
                Res::Def(DefKind::Const, id) => {
                    if expect_spec || ctxt.var_modes[&expr.hir_id] == Mode::Spec {
                        None
                    } else {
                        let vir_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);
                        let fun_name = Arc::new(FunX { path: vir_path });
                        let fun_exp = mk_exp1(ExpX::Var(state.fun_name(&fun_name)));
                        return mk_exp(ExpX::Call(fun_exp, vec![], vec![]));
                    }
                }
                Res::Def(DefKind::ConstParam, id) => {
                    let local_id = id.as_local().expect("ConstParam local");
                    let hir_id = ctxt.tcx.hir().local_def_id_to_hir_id(local_id);
                    match ctxt.tcx.hir().get(hir_id) {
                        Node::GenericParam(gp) => {
                            let name = state.typ_param(gp.name.ident().to_string(), None);
                            mk_exp(ExpX::Var(name))
                        }
                        _ => panic!("ConstParam"),
                    }
                }
                _ => {
                    panic!("unsupported")
                }
            }
        }
        ExprKind::Lit(_lit) => {
            if expect_spec {
                None
            } else {
                let typ = expr_typ(state);
                mk_exp(ExpX::Op(vec![], typ))
            }
        }
        ExprKind::Call(e0, es) => {
            let is_variant = match &e0.kind {
                ExprKind::Path(qpath) => {
                    let res = ctxt.types().qpath_res(qpath, e0.hir_id);
                    match res {
                        Res::Def(DefKind::Variant, _did) => true,
                        Res::Def(DefKind::Ctor(rustc_hir::def::CtorOf::Variant, ..), _did) => true,
                        _ => false,
                    }
                }
                _ => false,
            };
            let (self_path, fn_def_id) = if let ExprKind::Path(qpath) = &e0.kind {
                let self_path = crate::rust_to_vir_expr::call_self_path(
                    ctxt.tcx,
                    &ctxt.verus_items,
                    ctxt.types(),
                    qpath,
                );
                let def = ctxt.types().qpath_res(&qpath, e0.hir_id);
                if let Res::Def(_, fn_def_id) = def {
                    (self_path, Some(fn_def_id))
                } else {
                    (self_path, None)
                }
            } else {
                (None, None)
            };
            erase_call(
                ctxt,
                state,
                expect_spec,
                expr,
                self_path,
                Some(e0),
                fn_def_id,
                ctxt.types().node_substs(e0.hir_id),
                e0.span,
                None,
                es,
                false,
                is_variant,
            )
        }
        ExprKind::MethodCall(segment, receiver, args, _call_span) => {
            let fn_def_id = ctxt.types().type_dependent_def_id(expr.hir_id).expect("method id");
            let rcvr_typ = mid_ty_to_vir_datatype(
                ctxt.tcx,
                &ctxt.verus_items,
                state.enclosing_fun_id.expect("enclosing_fun_id"),
                receiver.span,
                ctxt.types().node_type(receiver.hir_id),
                true,
            )
            .expect("type");
            let self_path = match &*vir::ast_util::undecorate_typ(&rcvr_typ) {
                vir::ast::TypX::Datatype(path, _, _) => Some(path.clone()),
                _ => None,
            };
            erase_call(
                ctxt,
                state,
                expect_spec,
                expr,
                self_path,
                None,
                Some(fn_def_id),
                ctxt.types().node_substs(expr.hir_id),
                segment.ident.span,
                Some(receiver),
                args,
                true,
                false,
            )
        }
        ExprKind::Struct(qpath, fields, spread) => {
            if expect_spec {
                let mut exps: Vec<Option<Exp>> = Vec::new();
                for f in fields.iter() {
                    exps.push(erase_expr(ctxt, state, expect_spec, f.expr));
                }
                erase_spec_exps(ctxt, state, expr, exps)
            } else {
                let res = ctxt.types().qpath_res(qpath, expr.hir_id);
                let (adt_def_id, variant_def, is_enum) =
                    get_adt_res(ctxt.tcx, res, expr.span).unwrap();
                let variant_name = str_ident(&variant_def.ident(ctxt.tcx).as_str());
                let vir_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, adt_def_id);

                let datatype = &ctxt.datatypes[&vir_path];
                let variant = datatype.x.get_variant(&variant_name);
                let mut fs: Vec<(Id, Exp)> = Vec::new();
                for f in fields.iter() {
                    let field_name = Arc::new(f.ident.as_str().to_string());
                    let (_, field_mode, _) = get_field(&variant.a, &field_name).a;
                    let name = state.local(f.ident.to_string());
                    let e = if field_mode == Mode::Spec {
                        phantom_data_expr(ctxt, state, &f.expr)
                    } else {
                        erase_expr(ctxt, state, expect_spec, f.expr).expect("expr")
                    };
                    fs.push((name, e));
                }
                let variant_opt =
                    if is_enum { Some(state.variant(variant_name.to_string())) } else { None };
                let spread = spread.map(|e| erase_expr(ctxt, state, expect_spec, e).expect("expr"));
                let typ_args = if let box TypX::Datatype(_, typ_args) = expr_typ(state) {
                    typ_args
                } else {
                    panic!("unexpected struct expression type")
                };
                mk_exp(ExpX::DatatypeStruct(
                    state.datatype_name(&vir_path),
                    variant_opt,
                    typ_args,
                    fs,
                    spread,
                ))
            }
        }
        ExprKind::Tup(exprs) => {
            let mut args: Vec<Exp> = Vec::new();
            if expect_spec {
                let exps = exprs.iter().map(|e| erase_expr(ctxt, state, expect_spec, e)).collect();
                erase_spec_exps(ctxt, state, expr, exps)
            } else {
                for e in exprs.iter() {
                    args.push(erase_expr(ctxt, state, expect_spec, e).expect("expr"));
                }
                mk_exp(ExpX::Tuple(args))
            }
        }
        ExprKind::Cast(source, _) => {
            let source = erase_expr(ctxt, state, expect_spec, source);
            erase_spec_exps(ctxt, state, expr, vec![source])
        }
        ExprKind::AddrOf(BorrowKind::Ref, mutability, e) => {
            let exp = erase_expr(ctxt, state, expect_spec, e);
            if expect_spec {
                erase_spec_exps(ctxt, state, expr, vec![exp])
            } else {
                mk_exp(ExpX::AddrOf(*mutability, exp.expect("expr")))
            }
        }
        ExprKind::Box(e) => {
            let exp = erase_expr(ctxt, state, expect_spec, e);
            erase_spec_exps(ctxt, state, expr, vec![exp])
        }
        ExprKind::Unary(op, e1) => {
            let exp1 = erase_expr(ctxt, state, expect_spec, e1);
            match op {
                UnOp::Deref if !expect_spec => mk_exp(ExpX::Deref(exp1.expect("expr"))),
                _ => erase_spec_exps(ctxt, state, expr, vec![exp1]),
            }
        }
        ExprKind::Binary(_op, e1, e2) => {
            let exp1 = erase_expr(ctxt, state, expect_spec, e1);
            let exp2 = erase_expr(ctxt, state, expect_spec, e2);
            erase_spec_exps(ctxt, state, expr, vec![exp1, exp2])
        }
        ExprKind::Index(e1, e2) => {
            let exp1 = erase_expr(ctxt, state, expect_spec, e1);
            let exp2 = erase_expr(ctxt, state, expect_spec, e2);
            if expect_spec {
                erase_spec_exps(ctxt, state, expr, vec![exp1, exp2])
            } else {
                let ty = erase_ty(ctxt, state, &ctxt.types().node_type(expr.hir_id));
                mk_exp(ExpX::Index(ty, exp1.expect("expr"), exp2.expect("expr")))
            }
        }
        ExprKind::Field(e1, field) => {
            let exp1 = erase_expr(ctxt, state, expect_spec, e1);
            if expect_spec {
                erase_spec_exps(ctxt, state, expr, vec![exp1])
            } else {
                let field_name = field.to_string();
                let field_id = if field_name.chars().all(char::is_numeric) {
                    Id::new(IdKind::Builtin, 0, field_name)
                } else {
                    state.local(field.to_string())
                };
                mk_exp(ExpX::Field(exp1.expect("expr"), field_id))
            }
        }
        ExprKind::Assign(e1, e2, _span) => {
            let mode1 = ctxt.var_modes[&e1.hir_id];
            if mode1 == Mode::Spec {
                let exp1 = erase_expr(ctxt, state, true, e1);
                let exp2 = erase_expr(ctxt, state, true, e2);
                erase_spec_exps(ctxt, state, expr, vec![exp1, exp2])
            } else {
                let exp1 = erase_expr(ctxt, state, false, e1);
                let exp2 = erase_expr(ctxt, state, false, e2);
                mk_exp(ExpX::Assign(exp1.expect("expr"), force_exp(exp2, e2.span)))
            }
        }
        ExprKind::AssignOp(_op, e1, e2) => {
            let mode1 = ctxt.var_modes[&e1.hir_id];
            if mode1 == Mode::Spec {
                let exp1 = erase_expr(ctxt, state, true, e1);
                let exp2 = erase_expr(ctxt, state, true, e2);
                erase_spec_exps(ctxt, state, expr, vec![exp1, exp2])
            } else {
                // REVIEW:
                // Right now, we duplicate exp1; this is ok because we only consider one kind of
                // expressions on the lhs: ExprX::VarLoc(_). When we add support
                // for more kinds, this may cause the borrow-checker to report errors in places
                // where it shouldn't (borrow-checking is still sound, but innacurate for these
                // expressions).
                let exp1 = erase_expr(ctxt, state, false, e1);
                let exp2 = erase_expr(ctxt, state, false, e2);
                let expr_typ =
                    |state: &mut State| erase_ty(ctxt, state, &ctxt.types().node_type(e1.hir_id));
                let exp3 = erase_spec_exps_typ(
                    ctxt,
                    state,
                    expr.span,
                    expr_typ,
                    vec![exp1.clone(), exp2],
                    false,
                );
                mk_exp(ExpX::Assign(exp1.expect("expr"), exp3.expect("expr")))
            }
        }
        ExprKind::If(cond, lhs, rhs) => {
            let cond_spec = ctxt.condition_modes[&expr.hir_id] == Mode::Spec;
            let cond = cond.peel_drop_temps();
            match cond.kind {
                ExprKind::Let(Let { pat, init: src_expr, .. }) => {
                    let arm1 = (Some(pat.to_owned()), &None, Some(*lhs));
                    let arm2 = (None, &None, *rhs);
                    erase_match(ctxt, state, expect_spec, expr, src_expr, vec![arm1, arm2])
                }
                _ => {
                    let ec = erase_expr(ctxt, state, cond_spec, cond);
                    let e1 = erase_expr(ctxt, state, expect_spec, lhs);
                    let e2 = match rhs {
                        None => None,
                        Some(rhs) => erase_expr(ctxt, state, expect_spec, rhs),
                    };
                    match (expect_spec, e1, e2) {
                        (true, None, None) => erase_spec_exps(ctxt, state, expr, vec![ec]),
                        (_, e1, e2) => {
                            let c = match ec {
                                None => mk_exp1(ExpX::Op(vec![], TypX::mk_bool())),
                                Some(e) => e,
                            };
                            let e1 = force_block(e1, lhs.span);
                            let e2 = force_block(e2, lhs.span);
                            mk_exp(ExpX::If(c, e1, e2))
                        }
                    }
                }
            }
        }
        ExprKind::Match(cond, arms, _match_source) => {
            let arms_vec = arms.iter().map(|a| (Some(a.pat), &a.guard, Some(a.body))).collect();
            erase_match(ctxt, state, expect_spec, expr, cond, arms_vec)
        }
        ExprKind::Loop(
            Block {
                stmts: [],
                expr: Some(Expr { kind: ExprKind::If(cond, body, _other), .. }),
                ..
            },
            label,
            rustc_hir::LoopSource::While,
            _span,
        ) => {
            let c = erase_expr(ctxt, state, false, cond).expect("expr");
            let b = force_block(erase_expr(ctxt, state, false, body), body.span);
            let label = label.map(|l| state.lifetime((l.ident.to_string(), None)));
            mk_exp(ExpX::While(c, b, label))
        }
        ExprKind::Loop(block, label, _source, _span) => {
            let b = force_block(erase_block(ctxt, state, false, block), block.span);
            let label = label.map(|l| state.lifetime((l.ident.to_string(), None)));
            mk_exp(ExpX::Loop(b, label))
        }
        ExprKind::Break(dest, None) => {
            let label = dest.label.map(|l| state.lifetime((l.ident.to_string(), None)));
            mk_exp(ExpX::Break(label))
        }
        ExprKind::Continue(dest) => {
            let label = dest.label.map(|l| state.lifetime((l.ident.to_string(), None)));
            mk_exp(ExpX::Continue(label))
        }
        ExprKind::Ret(None) => mk_exp(ExpX::Ret(None)),
        ExprKind::Ret(Some(expr)) => {
            let exp = erase_expr(ctxt, state, ctxt.ret_spec.expect("ret_spec"), expr);
            mk_exp(ExpX::Ret(exp))
        }
        ExprKind::Closure(Closure {
            capture_clause: capture_by,
            body: body_id,
            movability,
            ..
        }) => {
            let mut params: Vec<(Span, Id, Typ)> = Vec::new();
            let body = ctxt.tcx.hir().body(*body_id);
            let ps = &body.params;
            for p in ps.iter() {
                let x =
                    state.local(crate::rust_to_vir_expr::pat_to_var(p.pat).expect("pat_to_var"));
                let typ = erase_ty(ctxt, state, &ctxt.types().node_type(p.hir_id));
                params.push((p.pat.span, x, typ));
            }
            let body_exp = erase_expr(ctxt, state, expect_spec, &body.value);
            let body_exp = force_block(body_exp, body.value.span);
            mk_exp(ExpX::Closure(*capture_by, *movability, params, body_exp))
        }
        ExprKind::Block(block, None) => {
            let attrs = ctxt.tcx.hir().attrs(expr.hir_id);
            if crate::rust_to_vir_expr::attrs_is_invariant_block(attrs).expect("attrs") {
                return Some(erase_inv_block(ctxt, state, expr.span, block));
            }
            let g_attr = get_ghost_block_opt(ctxt.tcx.hir().attrs(expr.hir_id));
            let keep = match g_attr {
                Some(GhostBlockAttr::Proof) => true,
                Some(GhostBlockAttr::Tracked) => true,
                Some(GhostBlockAttr::GhostWrapped) => false,
                Some(GhostBlockAttr::TrackedWrapped) => true,
                Some(GhostBlockAttr::Wrapper) => panic!(),
                None => true,
            };
            if keep { erase_block(ctxt, state, expect_spec, block) } else { None }
        }
        _ => {
            dbg!(&expr);
            panic!()
        }
    }
}

fn erase_block<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    expect_spec: bool,
    block: &Block<'tcx>,
) -> Option<Exp> {
    let mk_exp = |e: ExpX| Some(Box::new((block.span, e)));
    assert!(block.rules == BlockCheckMode::DefaultBlock);
    assert!(!block.targeted_by_break);
    let mut stms: Vec<Stm> = Vec::new();
    for stmt in block.stmts {
        stms.extend(erase_stmt(ctxt, state, stmt));
    }
    let e = block.expr.and_then(|e| erase_expr(ctxt, state, expect_spec, e));
    if stms.len() > 0 || e.is_some() { mk_exp(ExpX::Block(stms, e)) } else { None }
}

fn erase_stmt<'tcx>(ctxt: &Context<'tcx>, state: &mut State, stmt: &Stmt<'tcx>) -> Vec<Stm> {
    match &stmt.kind {
        StmtKind::Expr(e) | StmtKind::Semi(e) => {
            if let Some(e) = erase_expr(ctxt, state, true, e) {
                vec![Box::new((stmt.span, StmX::Expr(e)))]
            } else {
                vec![]
            }
        }
        StmtKind::Local(local) => {
            let mode = ctxt.var_modes[&local.pat.hir_id];
            if mode == Mode::Spec {
                if let Some(init) = local.init {
                    if let Some(e) = erase_expr(ctxt, state, true, init) {
                        vec![Box::new((stmt.span, StmX::Expr(e)))]
                    } else {
                        vec![]
                    }
                } else {
                    vec![]
                }
            } else {
                let pat = erase_pat(ctxt, state, &local.pat);
                let typ = erase_ty(ctxt, state, &ctxt.types().node_type(local.pat.hir_id));
                let init_exp = if let Some(init) = local.init {
                    erase_expr(ctxt, state, false, init)
                } else {
                    None
                };
                vec![Box::new((stmt.span, StmX::Let(pat, typ, init_exp)))]
            }
        }
        StmtKind::Item(..) => panic!("unexpected statement"),
    }
}

fn erase_const<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context<'tcx>,
    state: &mut State,
    span: Span,
    id: DefId,
    external_body: bool,
    body_id: &BodyId,
) {
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);
    if let Some(s) = path.segments.last() {
        if s.to_string().starts_with("_DERIVE_builtin_Structural_FOR_") {
            return;
        }
    }
    let fun_name = Arc::new(FunX { path });
    if let Some(f_vir) = &ctxt.functions[&fun_name] {
        if f_vir.x.mode == Mode::Spec && f_vir.x.ret.x.mode == Mode::Spec {
            return;
        }
        let def = rustc_middle::ty::WithOptConstParam::unknown(body_id.hir_id.owner.def_id);
        let types = ctxt.tcx.typeck_opt_const_arg(def);
        ctxt.types_opt = Some(types);
        ctxt.ret_spec = Some(f_vir.x.ret.x.mode == Mode::Spec);

        let name = state.fun_name(&fun_name);
        let ty = ctxt.tcx.type_of(id);
        let typ = erase_ty(ctxt, state, &ty);
        let body = crate::rust_to_vir_func::find_body_krate(krate, body_id);
        let body_exp = if external_body {
            Box::new((body.value.span, ExpX::Panic))
        } else {
            erase_expr(ctxt, state, false, &body.value).expect("const body")
        };
        // Turn const decl into fn decl so we can use the non-const ExpX::Op in the body:
        let decl = FunDecl {
            sig_span: span,
            name_span: span,
            name,
            generic_params: vec![],
            generic_bounds: vec![],
            params: vec![],
            ret: Some((None, typ)),
            body: Box::new((body.value.span, ExpX::Block(vec![], Some(body_exp)))),
        };
        state.fun_decls.push(decl);
        ctxt.types_opt = None;
        ctxt.ret_spec = None;
    }
}

fn lifetime_key<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> (String, Option<u32>) {
    let def_path = ctxt.tcx.def_path(def_id);
    let path_name = &def_path.data.last().unwrap();
    (path_name.data.get_opt_name().unwrap().to_string(), Some(path_name.disambiguator))
}

fn erase_mir_generics<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    id: DefId,
    id_is_fn: bool,
    lifetimes: &mut Vec<GenericParam>,
    typ_params: &mut Vec<GenericParam>,
    generic_bounds: &mut Vec<GenericBound>,
) {
    let mir_generics = ctxt.tcx.generics_of(id);
    let mir_predicates = ctxt.tcx.predicates_of(id);
    if id_is_fn {
        let mir_ty = ctxt.tcx.type_of(id);
        if let TyKind::FnDef(..) = mir_ty.kind() {
            for bv in mir_ty.fn_sig(ctxt.tcx).bound_vars().iter() {
                if let BoundVariableKind::Region(BoundRegionKind::BrNamed(a, _)) = bv {
                    let name = state.lifetime(lifetime_key(ctxt, a));
                    lifetimes.push(GenericParam { name, const_typ: None });
                }
            }
        }
    }
    for gparam in &mir_generics.params {
        match gparam.kind {
            GenericParamDefKind::Lifetime => {
                let name = state.lifetime((gparam.name.to_string(), None));
                lifetimes.push(GenericParam { name, const_typ: None });
            }
            GenericParamDefKind::Type { .. } => {
                let name = state.typ_param(gparam.name.to_string(), Some(gparam.index));
                typ_params.push(GenericParam { name, const_typ: None });
            }
            GenericParamDefKind::Const { .. } => {
                let name = state.typ_param(gparam.name.to_string(), None);
                let t = erase_ty(ctxt, state, &ctxt.tcx.type_of(gparam.def_id));
                typ_params.push(GenericParam { name, const_typ: Some(t) });
            }
        }
    }
    let mut fn_traits: Vec<(Typ, ClosureKind)> = Vec::new();
    let mut fn_projections: HashMap<Typ, (Typ, Typ)> = HashMap::new();
    for (pred, _) in mir_predicates.predicates.iter() {
        match pred.kind().no_bound_vars().expect("no_bound_vars") {
            PredicateKind::Clause(Clause::RegionOutlives(pred)) => {
                let x = erase_hir_region(ctxt, state, &pred.0).expect("bound");
                let typ = Box::new(TypX::TypParam(x));
                let bound = erase_hir_region(ctxt, state, &pred.1).expect("bound");
                let generic_bound = GenericBound { typ, bound: Bound::Id(bound) };
                generic_bounds.push(generic_bound);
            }
            PredicateKind::Clause(Clause::TypeOutlives(pred)) => {
                let typ = erase_ty(ctxt, state, &pred.0);
                let bound = erase_hir_region(ctxt, state, &pred.1).expect("bound");
                let generic_bound = GenericBound { typ, bound: Bound::Id(bound) };
                generic_bounds.push(generic_bound);
            }
            PredicateKind::Clause(Clause::Trait(pred)) => {
                let typ = erase_ty(ctxt, state, &pred.trait_ref.substs[0].expect_ty());
                let id = pred.trait_ref.def_id;
                let trait_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);
                let bound = if Some(id) == ctxt.tcx.lang_items().copy_trait() {
                    Some(Bound::Copy)
                } else if state.trait_decl_set.contains(&trait_path) {
                    let substs = pred.trait_ref.substs;
                    let trait_typ_args =
                        substs.types().skip(1).map(|ty| erase_ty(ctxt, state, &ty)).collect();
                    let trait_path = state.trait_name(&trait_path);
                    let datatype = Box::new(TypX::Datatype(trait_path, trait_typ_args));
                    Some(Bound::Trait(datatype))
                } else {
                    None
                };
                if let Some(bound) = bound {
                    let generic_bound = GenericBound { typ: typ.clone(), bound };
                    generic_bounds.push(generic_bound);
                }
                let kind = if Some(id) == ctxt.tcx.lang_items().fn_trait() {
                    Some(ClosureKind::Fn)
                } else if Some(id) == ctxt.tcx.lang_items().fn_mut_trait() {
                    Some(ClosureKind::FnMut)
                } else if Some(id) == ctxt.tcx.lang_items().fn_once_trait() {
                    Some(ClosureKind::FnOnce)
                } else {
                    None
                };
                if let Some(kind) = kind {
                    fn_traits.push((typ, kind));
                }
            }
            PredicateKind::Clause(Clause::Projection(pred)) => {
                if Some(pred.projection_ty.def_id) == ctxt.tcx.lang_items().fn_once_output() {
                    assert!(pred.projection_ty.substs.len() == 2);
                    let typ = erase_ty(ctxt, state, &pred.projection_ty.substs[0].expect_ty());
                    let mut fn_params = match pred.projection_ty.substs[1].unpack() {
                        GenericArgKind::Type(ty) => erase_ty(ctxt, state, &ty),
                        _ => panic!("unexpected fn projection"),
                    };
                    if !matches!(*fn_params, TypX::Tuple(_)) {
                        fn_params = Box::new(TypX::Tuple(vec![fn_params]));
                    }
                    let fn_ret = erase_ty(ctxt, state, &pred.term.ty().expect("fn_ret"));
                    fn_projections.insert(typ, (fn_params, fn_ret)).map(|_| panic!("{:?}", pred));
                }
            }
            _ => {
                dbg!(pred.kind());
                panic!("unexpected bound")
            }
        }
    }
    for (typ, kind) in fn_traits.into_iter() {
        let (params, ret) = fn_projections.remove(&typ).expect("fn_projections");
        let generic_bound = GenericBound { typ, bound: Bound::Fn(kind, params, ret) };
        generic_bounds.push(generic_bound);
    }
}

fn erase_fn_common<'tcx>(
    krate: Option<&'tcx Crate<'tcx>>,
    ctxt: &mut Context<'tcx>,
    state: &mut State,
    name_span: Span,
    id: DefId,
    sig: Option<&FnSig<'tcx>>,
    sig_span: Span,
    impl_generics: Option<DefId>,
    empty_body: bool,
    external_body: bool,
    body_id: Option<&BodyId>,
) {
    if ctxt.ignored_functions.contains(&id) {
        return;
    }
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);
    let is_verus_spec = path.segments.last().expect("segment.last").starts_with(VERUS_SPEC);
    if is_verus_spec {
        return;
    }
    let fun_name = Arc::new(FunX { path: path.clone() });
    if let Some(f_vir) = &ctxt.functions[&fun_name] {
        if f_vir.x.mode == Mode::Spec {
            return;
        }
        if let Some(body_id) = body_id {
            let def = rustc_middle::ty::WithOptConstParam::unknown(body_id.hir_id.owner.def_id);
            let types = ctxt.tcx.typeck_opt_const_arg(def);
            ctxt.types_opt = Some(types);
            ctxt.ret_spec = Some(f_vir.x.ret.x.mode == Mode::Spec);
        }

        let expect_spec = f_vir.x.ret.x.mode == Mode::Spec;
        let body = if let Some(body_id) = body_id {
            Some(crate::rust_to_vir_func::find_body_krate(krate.expect("krate"), body_id))
        } else {
            None
        };
        let body_exp = if body.is_none() || external_body {
            force_block(Some(Box::new((sig_span, ExpX::Panic))), sig_span)
        } else {
            let body = &body.expect("body");
            state.enclosing_fun_id = Some(id);
            let body_exp = erase_expr(ctxt, state, expect_spec, &body.value);
            state.enclosing_fun_id = None;
            if empty_body {
                if let Some(_) = body_exp {
                    panic!("expected empty method body")
                } else {
                    force_block(Some(Box::new((sig_span, ExpX::Panic))), sig_span)
                }
            } else {
                force_block(body_exp, body.value.span)
            }
        };
        let fn_sig = ctxt.tcx.fn_sig(id);
        let fn_sig = fn_sig.skip_binder();
        state.rename_count += 1;
        let name = state.fun_name(&fun_name);
        let inputs = &fn_sig.inputs();
        assert!(inputs.len() == f_vir.x.params.len());
        let params_info: Vec<(Option<Span>, bool)> = if let Some(body) = body {
            assert!(inputs.len() == body.params.len());
            body.params
                .iter()
                .map(|p| {
                    let is_mut_var = match p.pat.kind {
                        PatKind::Binding(rustc_hir::BindingAnnotation(_, mutability), _, _, _) => {
                            mutability == rustc_hir::Mutability::Mut
                        }
                        _ => panic!("expected binding pattern"),
                    };
                    (Some(p.pat.span), is_mut_var)
                })
                .collect()
        } else {
            inputs.iter().map(|_| (None, false)).collect()
        };
        let mut lifetimes: Vec<GenericParam> = Vec::new();
        let mut typ_params: Vec<GenericParam> = Vec::new();
        let mut generic_bounds: Vec<GenericBound> = Vec::new();
        if let Some(impl_id) = impl_generics {
            erase_mir_generics(
                ctxt,
                state,
                impl_id,
                false,
                &mut lifetimes,
                &mut typ_params,
                &mut generic_bounds,
            );
        }
        erase_mir_generics(
            ctxt,
            state,
            id,
            true,
            &mut lifetimes,
            &mut typ_params,
            &mut generic_bounds,
        );
        let mut params: Vec<(Option<Span>, Id, Typ, bool)> = Vec::new();
        for ((input, param), param_info) in inputs.iter().zip(f_vir.x.params.iter()).zip(params_info.iter()) {
            let name = if let Some((_, name)) = &param.x.unwrapped_info {
                name.to_string()
            } else {
                param.x.name.to_string()
            };
            let is_mut_var = param_info.1;
            let span = param_info.0;
            let x = state.local(name);
            let typ = if param.x.mode == Mode::Spec {
                TypX::mk_unit()
            } else {
                erase_ty(ctxt, state, input)
            };
            params.push((span, x, typ, is_mut_var));
        }
        let ret = if let Some(sig) = sig {
            match sig.decl.output {
                rustc_hir::FnRetTy::DefaultReturn(_) => None,
                rustc_hir::FnRetTy::Return(ty) => {
                    if f_vir.x.ret.x.mode == Mode::Spec {
                        None
                    } else {
                        Some((Some(ty.span), erase_ty(ctxt, state, &fn_sig.output())))
                    }
                }
            }
        } else {
            Some((None, erase_ty(ctxt, state, &fn_sig.output())))
        };
        let decl = FunDecl {
            sig_span: sig_span,
            name_span,
            name,
            // lifetimes must precede typ_params
            generic_params: lifetimes.into_iter().chain(typ_params.into_iter()).collect(),
            generic_bounds,
            params,
            ret,
            body: body_exp,
        };
        state.fun_decls.push(decl);
        ctxt.types_opt = None;
        ctxt.ret_spec = None;
    }
}

fn import_fn<'tcx>(ctxt: &mut Context<'tcx>, state: &mut State, id: DefId) {
    erase_fn_common(
        None,
        ctxt,
        state,
        ctxt.tcx.def_ident_span(id).expect("function name span"),
        id,
        None,
        ctxt.tcx.def_span(id),
        ctxt.tcx.generics_of(id).parent,
        true,
        true,
        None,
    );
}

fn erase_fn<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context<'tcx>,
    state: &mut State,
    name_span: Span,
    id: DefId,
    sig: &FnSig<'tcx>,
    impl_generics: Option<DefId>,
    empty_body: bool,
    external_body: bool,
    body_id: Option<&BodyId>,
) {
    erase_fn_common(
        Some(krate),
        ctxt,
        state,
        name_span,
        id,
        Some(sig),
        sig.span,
        impl_generics,
        empty_body,
        external_body,
        body_id,
    );
}

fn erase_trait<'tcx>(
    _krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context<'tcx>,
    state: &mut State,
    trait_id: DefId,
    trait_items: &[TraitItemRef],
) {
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, trait_id);
    let name = state.trait_name(&path);
    let mut lifetimes: Vec<GenericParam> = Vec::new();
    let mut typ_params: Vec<GenericParam> = Vec::new();
    let mut generic_bounds: Vec<GenericBound> = Vec::new();
    erase_mir_generics(
        ctxt,
        state,
        trait_id,
        false,
        &mut lifetimes,
        &mut typ_params,
        &mut generic_bounds,
    );
    typ_params.remove(0); // remove Self type parameter
    let generic_params = lifetimes.into_iter().chain(typ_params.into_iter()).collect();
    let mut assoc_typs: Vec<Id> = Vec::new();
    for trait_item_ref in trait_items {
        let trait_item = ctxt.tcx.hir().trait_item(trait_item_ref.id);
        let TraitItem { ident, kind, .. } = trait_item;
        match kind {
            TraitItemKind::Type([], None) => {
                assoc_typs.push(state.typ_param(ident.to_string(), None));
            }
            _ => {}
        }
    }
    // We only need traits with associated type declarations.
    if assoc_typs.len() > 0 {
        let decl = TraitDecl { name, generic_params, generic_bounds, assoc_typs };
        state.trait_decl_set.insert(path.clone());
        state.trait_decls.push(decl);
    }
}

fn erase_trait_methods<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context<'tcx>,
    state: &mut State,
    trait_id: DefId,
    items: &[TraitItemRef],
) {
    for trait_item_ref in items {
        let trait_item = ctxt.tcx.hir().trait_item(trait_item_ref.id);
        let TraitItem { ident, owner_id, generics: _, kind, span: _, defaultness: _ } = trait_item;
        match kind {
            TraitItemKind::Fn(sig, fun) => {
                let body_id = match fun {
                    TraitFn::Provided(body_id) => Some(body_id),
                    TraitFn::Required(..) => None,
                };
                let id = owner_id.to_def_id();
                erase_fn(
                    krate,
                    ctxt,
                    state,
                    ident.span,
                    id,
                    sig,
                    Some(trait_id),
                    true,
                    false,
                    body_id,
                );
            }
            TraitItemKind::Type([], None) => {}
            _ => panic!("unexpected trait item"),
        }
    }
}

fn erase_impl<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context<'tcx>,
    state: &mut State,
    impl_id: DefId,
    impll: &Impl<'tcx>,
) {
    for impl_item_ref in impll.items {
        match impl_item_ref.kind {
            AssocItemKind::Fn { .. } => {
                let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                let ImplItem { ident, owner_id, kind, .. } = impl_item;
                let id = owner_id.to_def_id();
                let attrs = ctxt.tcx.hir().attrs(impl_item.hir_id());
                let vattrs = get_verifier_attrs(attrs).expect("get_verifier_attrs");
                if vattrs.external {
                    continue;
                }
                match &kind {
                    ImplItemKind::Fn(sig, body_id) => {
                        erase_fn(
                            krate,
                            ctxt,
                            state,
                            ident.span,
                            id,
                            sig,
                            Some(impl_id),
                            false,
                            vattrs.external_body,
                            Some(body_id),
                        );
                    }
                    _ => panic!(),
                }
            }
            AssocItemKind::Type => {
                let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                if let (ImplItemKind::Type(_ty), Some(TraitRef { path, .. })) =
                    (&impl_item.kind, &impll.of_trait)
                {
                    let trait_ref = ctxt.tcx.impl_trait_ref(impl_id).expect("impl_trait_ref");
                    let name = state.typ_param(&impl_item.ident.to_string(), None);
                    let trait_path_vir =
                        def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, path.res.def_id());
                    if !state.trait_decl_set.contains(&trait_path_vir) {
                        continue;
                    }
                    let trait_path = state.trait_name(&trait_path_vir);
                    // If we have `impl X for Z<A, B, C>` then the list of types is [X, A, B, C].
                    // So to get the type args, we strip off the first element.
                    let mut trait_typ_args: Vec<Typ> = Vec::new();
                    for ty in trait_ref.0.substs.types().skip(1) {
                        trait_typ_args.push(erase_ty(ctxt, state, &ty));
                    }
                    let mut lifetimes: Vec<GenericParam> = Vec::new();
                    let mut typ_params: Vec<GenericParam> = Vec::new();
                    let mut generic_bounds: Vec<GenericBound> = Vec::new();
                    erase_mir_generics(
                        ctxt,
                        state,
                        impl_id,
                        false,
                        &mut lifetimes,
                        &mut typ_params,
                        &mut generic_bounds,
                    );
                    let generic_params =
                        lifetimes.into_iter().chain(typ_params.into_iter()).collect();
                    let self_ty = ctxt.tcx.type_of(impl_id);
                    let self_typ = erase_ty(ctxt, state, &self_ty);
                    let ty = ctxt.tcx.type_of(impl_item.owner_id.to_def_id());
                    let typ = erase_ty(ctxt, state, &ty);
                    let trait_as_datatype = Box::new(TypX::Datatype(trait_path, trait_typ_args));
                    let assoc = AssocTypeImpl {
                        name,
                        generic_params,
                        generic_bounds,
                        self_typ,
                        trait_as_datatype,
                        typ,
                    };
                    state.assoc_type_impls.push(assoc);
                }
            }
            _ => panic!("unexpected impl"),
        }
    }
}

fn erase_datatype<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    span: Span,
    id: DefId,
    datatype: Datatype,
) {
    let datatype = Box::new(datatype);
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);
    let name = state.datatype_name(&path);
    let implements_copy = ctxt.copy_types.get(&id).cloned();
    let mut lifetimes: Vec<GenericParam> = Vec::new();
    let mut typ_params: Vec<GenericParam> = Vec::new();
    let mut generic_bounds: Vec<GenericBound> = Vec::new();
    erase_mir_generics(
        ctxt,
        state,
        id,
        false,
        &mut lifetimes,
        &mut typ_params,
        &mut generic_bounds,
    );
    let generic_params = lifetimes.into_iter().chain(typ_params.into_iter()).collect();
    let decl =
        DatatypeDecl { name, span, implements_copy, generic_params, generic_bounds, datatype };
    state.datatype_decls.push(decl);
}

fn erase_variant_data<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    variant: &VariantDef,
) -> Fields {
    let get_attrs = |f_did: DefId| {
        if let Some(rustc_hir::Node::Field(f_hir)) = ctxt.tcx.hir().get_if_local(f_did) {
            ctxt.tcx.hir().attrs(f_hir.hir_id)
        } else {
            ctxt.tcx.item_attrs(f_did)
        }
    };
    let revise_typ = |f_did: DefId, typ: Typ| {
        let mode = get_mode(Mode::Exec, get_attrs(f_did));
        if mode == Mode::Spec { Box::new(TypX::Phantom(typ)) } else { typ }
    };
    match variant.ctor_kind() {
        Some(CtorKind::Fn) => {
            let mut fields: Vec<Typ> = Vec::new();
            for field in &variant.fields {
                let typ = erase_ty(ctxt, state, &ctxt.tcx.type_of(field.did));
                fields.push(revise_typ(field.did, typ));
            }
            Fields::Pos(fields)
        }
        None => {
            let mut fields: Vec<Field> = Vec::new();
            for field in &variant.fields {
                let name = state.local(field.ident(ctxt.tcx).to_string());
                let typ = erase_ty(ctxt, state, &ctxt.tcx.type_of(field.did));
                fields.push(Field { name, typ: revise_typ(field.did, typ) });
            }
            Fields::Named(fields)
        }
        Some(CtorKind::Const) => {
            assert!(variant.fields.len() == 0);
            Fields::Pos(vec![])
        }
    }
}

// Treat external_body datatypes as abstract (erase the original fields)
fn erase_abstract_datatype<'tcx>(ctxt: &Context<'tcx>, state: &mut State, span: Span, id: DefId) {
    let mut fields: Vec<Typ> = Vec::new();
    let mir_generics = ctxt.tcx.generics_of(id);
    for gparam in mir_generics.params.iter() {
        // Rust requires all lifetime/type variables to be mentioned in the fields,
        // so introduce a dummy field for each lifetime/type variable
        match gparam.kind {
            GenericParamDefKind::Lifetime => {
                let x = state.lifetime((gparam.name.to_string(), None));
                fields.push(Box::new(TypX::Ref(TypX::mk_bool(), Some(x), Mutability::Not)));
            }
            GenericParamDefKind::Type { .. } => {
                let x = state.typ_param(gparam.name.to_string(), Some(gparam.index));
                fields.push(Box::new(TypX::Phantom(Box::new(TypX::TypParam(x)))));
            }
            GenericParamDefKind::Const { .. } => {
                // no dummy needed
            }
        }
    }
    let datatype = Datatype::Struct(Fields::Pos(fields));
    erase_datatype(ctxt, state, span, id, datatype);
}

fn erase_mir_datatype<'tcx>(ctxt: &Context<'tcx>, state: &mut State, id: DefId) {
    let span = ctxt.tcx.def_span(id);

    let attrs = if let Some(rustc_hir::Node::Item(d_hir)) = ctxt.tcx.hir().get_if_local(id) {
        ctxt.tcx.hir().attrs(d_hir.hir_id())
    } else {
        ctxt.tcx.item_attrs(id)
    };
    let vattrs = get_verifier_attrs(attrs).expect("get_verifier_attrs");
    if vattrs.external_type_specification {
        return;
    }

    let rust_item = verus_items::get_rust_item(ctxt.tcx, id);

    if let Some(RustItem::Box) = rust_item {
        return;
    }
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);
    if let Some(RustItem::Rc | RustItem::Arc) = rust_item {
        return;
    }

    let verus_item = ctxt.verus_items.id_to_name.get(&id);

    if let Some(VerusItem::Pervasive(PervasiveItem::StrSlice, _)) = verus_item {
        erase_abstract_datatype(ctxt, state, span, id);
        return;
    }

    // Check if the struct is 'external_body'
    // (Recall that the 'external_body' label may have been applied by a proxy type,
    // so we can't check the vattrs of the datatype definition directly.
    // Need to check the VIR instead.)
    let is_external_body = match ctxt.datatypes.get(&path) {
        Some(dt) => match dt.x.transparency {
            DatatypeTransparency::Never => true,
            DatatypeTransparency::WhenVisible(_) => false,
        },
        None => {
            dbg!(id);
            panic!("erase_mir_datatype: unrecognized datatype");
        }
    };
    if is_external_body {
        erase_abstract_datatype(ctxt, state, span, id);
        return;
    }

    let adt_def = ctxt.tcx.adt_def(id);
    if adt_def.is_struct() {
        let fields = erase_variant_data(ctxt, state, adt_def.non_enum_variant());
        let datatype = Datatype::Struct(fields);
        erase_datatype(ctxt, state, span, id, datatype);
    } else if adt_def.is_enum() {
        let mut variants: Vec<(Id, Fields)> = Vec::new();
        for variant in adt_def.variants().iter() {
            let name = state.variant(variant.ident(ctxt.tcx).to_string());
            let fields = erase_variant_data(ctxt, state, variant);
            variants.push((name, fields));
        }
        let datatype = Datatype::Enum(variants);
        erase_datatype(ctxt, state, span, id, datatype);
    } else {
        panic!("unexpected datatype {:?}", id);
    }
}

pub(crate) fn gen_check_tracked_lifetimes<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: Arc<VerusItems>,
    krate: &'tcx Crate<'tcx>,
    erasure_hints: &ErasureHints,
) -> State {
    let mut ctxt = Context {
        tcx,
        verus_items,
        types_opt: None,
        functions: HashMap::new(),
        datatypes: HashMap::new(),
        ignored_functions: HashSet::new(),
        copy_types: HashMap::new(),
        calls: HashMap::new(),
        condition_modes: HashMap::new(),
        var_modes: HashMap::new(),
        ret_spec: None,
    };
    let mut state = State::new();
    let mut id_to_hir: HashMap<AstId, Vec<HirId>> = HashMap::new();
    for (hir_id, vir_id) in &erasure_hints.hir_vir_ids {
        if !id_to_hir.contains_key(vir_id) {
            id_to_hir.insert(*vir_id, vec![]);
        }
        id_to_hir.get_mut(vir_id).unwrap().push(*hir_id);
    }
    for f in &erasure_hints.vir_crate.functions {
        ctxt.functions.insert(f.x.name.clone(), Some(f.clone())).map(|_| panic!("{:?}", &f.x.name));
    }
    for d in &erasure_hints.vir_crate.datatypes {
        ctxt.datatypes.insert(d.x.path.clone(), d.clone()).map(|_| panic!("{:?}", &d.x.path));
    }
    for (id, _span) in &erasure_hints.ignored_functions {
        ctxt.ignored_functions.insert(*id);
    }
    for (hir_id, span, call) in &erasure_hints.resolved_calls {
        if ctxt.calls.contains_key(hir_id) {
            if &ctxt.calls[hir_id] != call {
                panic!("inconsistent resolved_calls: {:?}", span);
            }
        } else {
            ctxt.calls.insert(*hir_id, call.clone());
        }
    }
    for (span, mode) in &erasure_hints.erasure_modes.condition_modes {
        if crate::spans::from_raw_span(&span.raw_span).is_none() {
            continue;
        }
        if !id_to_hir.contains_key(&span.id) {
            dbg!(span, span.id);
            panic!("missing id_to_hir");
        }
        for hir_id in &id_to_hir[&span.id] {
            if ctxt.condition_modes.contains_key(hir_id) {
                if &ctxt.condition_modes[hir_id] != mode {
                    panic!("inconsistent condition_modes: {:?}", span);
                }
            } else {
                ctxt.condition_modes.insert(*hir_id, *mode);
            }
        }
    }
    for (span, mode) in &erasure_hints.erasure_modes.var_modes {
        if crate::spans::from_raw_span(&span.raw_span).is_none() {
            continue;
        }
        if !id_to_hir.contains_key(&span.id) {
            dbg!(span, span.id);
            panic!("missing id_to_hir");
        }
        for hir_id in &id_to_hir[&span.id] {
            if ctxt.var_modes.contains_key(hir_id) {
                if &ctxt.var_modes[hir_id] != mode {
                    panic!("inconsistent var_modes: {:?}", span);
                }
            } else {
                ctxt.var_modes.insert(*hir_id, *mode);
            }
        }
    }
    for (hir_id, mode) in &erasure_hints.direct_var_modes {
        ctxt.var_modes.insert(*hir_id, *mode).map(|v| panic!("{:?}", v));
    }
    if let Some(copy) = tcx.lang_items().copy_trait() {
        for c in tcx.crates(()) {
            for (copy_impl, _) in tcx.implementations_of_trait((*c, copy)) {
                add_copy_type(&mut ctxt, &mut state, *copy_impl);
            }
        }
    }
    for owner in krate.owners.iter() {
        if let MaybeOwner::Owner(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Impl(Impl { of_trait: Some(trait_ref), .. }) => {
                        if Some(trait_ref.path.res.def_id()) == tcx.lang_items().copy_trait() {
                            add_copy_type(&mut ctxt, &mut state, item.owner_id.to_def_id());
                        }
                    }
                    ItemKind::Trait(
                        IsAuto::No,
                        Unsafety::Normal,
                        _trait_generics,
                        _bounds,
                        trait_items,
                    ) => {
                        // We only need traits with associated type declarations.
                        // Process traits early so we can see which traits we need.
                        let id = item.owner_id.to_def_id();
                        erase_trait(krate, &mut ctxt, &mut state, id, trait_items);
                    }
                    _ => {}
                },
                _ => {}
            }
        }
    }

    for owner in krate.owners.iter() {
        if let MaybeOwner::Owner(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => {
                    let attrs = tcx.hir().attrs(item.hir_id());
                    let vattrs = get_verifier_attrs(attrs).expect("get_verifier_attrs");
                    if vattrs.external {
                        continue;
                    }
                    let id = item.owner_id.to_def_id();
                    match &item.kind {
                        ItemKind::Use { .. } => {}
                        ItemKind::ExternCrate { .. } => {}
                        ItemKind::Mod { .. } => {}
                        ItemKind::ForeignMod { .. } => {}
                        ItemKind::Macro(..) => {}
                        ItemKind::TyAlias(..) => {}
                        ItemKind::Static(..) => {}
                        ItemKind::GlobalAsm(..) => {}
                        ItemKind::Struct(_s, _generics) => {
                            state.reach_datatype(&ctxt, id);
                        }
                        ItemKind::Enum(_e, _generics) => {
                            state.reach_datatype(&ctxt, id);
                        }
                        ItemKind::Const(_ty, body_id) => {
                            erase_const(
                                krate,
                                &mut ctxt,
                                &mut state,
                                item.span,
                                id,
                                vattrs.external_body,
                                body_id,
                            );
                        }
                        ItemKind::Fn(sig, _generics, body_id) => {
                            if !vattrs.external_fn_specification {
                                erase_fn(
                                    krate,
                                    &mut ctxt,
                                    &mut state,
                                    item.ident.span,
                                    id,
                                    sig,
                                    None,
                                    false,
                                    vattrs.external_body,
                                    Some(body_id),
                                );
                            } else {
                                let body = ctxt.tcx.hir().body(*body_id);
                                let (def_id, _) = crate::rust_to_vir_func::get_external_def_id(
                                    ctxt.tcx,
                                    &ctxt.verus_items,
                                    id,
                                    body_id,
                                    body,
                                    sig,
                                )
                                .unwrap();

                                // Case where the external function is local - it doesn't
                                // end up in the 'imported_fun_worklist' in this case
                                if def_id.as_local().is_some() {
                                    import_fn(&mut ctxt, &mut state, def_id);
                                }
                            }
                        }
                        ItemKind::Trait(
                            IsAuto::No,
                            Unsafety::Normal,
                            _trait_generics,
                            _bounds,
                            trait_items,
                        ) => {
                            erase_trait_methods(krate, &mut ctxt, &mut state, id, trait_items);
                        }
                        ItemKind::Impl(impll) => {
                            erase_impl(krate, &mut ctxt, &mut state, id, impll);
                        }
                        ItemKind::OpaqueTy(OpaqueTy {
                            generics: _,
                            bounds: _,
                            origin: OpaqueTyOrigin::AsyncFn(_),
                            in_trait: _,
                        }) => {
                            continue;
                        }
                        _ => {
                            dbg!(item);
                            panic!("unexpected item");
                        }
                    }
                }
                OwnerNode::TraitItem(_trait_item) => {
                    // handled by ItemKind::Trait
                }
                OwnerNode::Crate(_mod_) => {}
                OwnerNode::ImplItem(_) => {}
                OwnerNode::ForeignItem(_foreign_item) => {}
            }
        }
    }
    while let Some(id) = state.imported_fun_worklist.pop() {
        import_fn(&mut ctxt, &mut state, id);
    }
    while let Some(id) = state.datatype_worklist.pop() {
        erase_mir_datatype(&ctxt, &mut state, id);
    }
    state
}
