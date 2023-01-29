use crate::attributes::{get_ghost_block_opt, get_mode, get_verifier_attrs, GhostBlockAttr};
use crate::erase::{ErasureHints, ResolvedCall};
use crate::lifetime_ast::*;
use crate::rust_to_vir_base::{def_id_to_vir_path, local_to_var};
use crate::rust_to_vir_expr::{datatype_constructor_variant_of_res, datatype_variant_of_res};
use air::ast::AstId;
use rustc_ast::{BorrowKind, IsAuto, Mutability};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    AssocItemKind, BindingAnnotation, Block, BlockCheckMode, BodyId, Crate, EnumDef, Expr,
    ExprKind, FnSig, GenericBound, GenericBounds, GenericParamKind, Generics, HirId, Impl,
    ImplItem, ImplItemKind, ItemKind, Node, OwnerNode, Pat, PatKind, QPath, Stmt, StmtKind,
    TraitFn, TraitItem, TraitItemKind, TraitItemRef, TraitRef, UnOp, Unsafety, VariantData,
};
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{
    AdtDef, BoundRegionKind, GenericParamDefKind, PredicateKind, RegionKind, Ty, TyCtxt, TyKind,
    TypeckResults,
};
use rustc_span::def_id::DefId;
use rustc_span::symbol::kw;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{Fun, FunX, Function, Mode, Path};
use vir::ast_util::get_field;

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
    types_opt: Option<&'tcx TypeckResults<'tcx>>,
    /// Map each function path to its VIR Function, or to None if it is a #[verifier(external)]
    /// function
    functions: HashMap<Fun, Option<Function>>,
    /// Map each datatype path to its VIR Datatype
    datatypes: HashMap<Path, vir::ast::Datatype>,
    ignored_functions: HashSet<DefId>,
    /// Set of struct/enum that implement Copy
    copy_types: HashSet<DefId>,
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
    id_to_name: HashMap<String, Id>,
    typ_param_to_name: HashMap<(String, Option<u32>), Id>,
    lifetime_to_name: HashMap<String, Id>,
    fun_to_name: HashMap<Fun, Id>,
    datatype_to_name: HashMap<Path, Id>,
    variant_to_name: HashMap<String, Id>,
    pub(crate) datatype_decls: Vec<DatatypeDecl>,
    pub(crate) const_decls: Vec<ConstDecl>,
    pub(crate) fun_decls: Vec<FunDecl>,
}

impl State {
    fn new() -> State {
        State {
            rename_count: 0,
            id_to_name: HashMap::new(),
            typ_param_to_name: HashMap::new(),
            lifetime_to_name: HashMap::new(),
            fun_to_name: HashMap::new(),
            datatype_to_name: HashMap::new(),
            variant_to_name: HashMap::new(),
            datatype_decls: Vec::new(),
            const_decls: Vec::new(),
            fun_decls: Vec::new(),
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

    fn lifetime<S: Into<String>>(&mut self, raw_id: S) -> Id {
        let raw_id = raw_id.into();
        let f = || raw_id.clone().replace("'", "");
        Self::id(&mut self.rename_count, &mut self.lifetime_to_name, IdKind::Lifetime, &raw_id, f)
    }

    fn fun_name<'tcx>(&mut self, fun: &Fun) -> Id {
        let f = || fun.path.segments.last().expect("path").to_string();
        Self::id(&mut self.rename_count, &mut self.fun_to_name, IdKind::Fun, fun, f)
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
}

fn span_dummy() -> Span {
    let lo = rustc_span::BytePos(0);
    let hi = rustc_span::BytePos(0);
    let ctxt = rustc_span::SyntaxContext::root();
    let data = rustc_span::SpanData { lo, hi, ctxt, parent: None };
    data.span()
}

fn erase_hir_region<'tcx>(_ctxt: &Context<'tcx>, state: &mut State, r: &RegionKind) -> Option<Id> {
    match r {
        RegionKind::ReEarlyBound(bound) => Some(state.lifetime(bound.name.to_string())),
        RegionKind::ReLateBound(_, bound) => match bound.kind {
            BoundRegionKind::BrNamed(_, x) => Some(state.lifetime(x.to_string())),
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

fn erase_ty<'tcx>(ctxt: &Context<'tcx>, state: &mut State, ty: Ty) -> Typ {
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
        TyKind::Tuple(_) => {
            Box::new(TypX::Tuple(ty.tuple_fields().map(|t| erase_ty(ctxt, state, t)).collect()))
        }
        TyKind::Adt(AdtDef { did, .. }, args) => {
            let path = def_id_to_vir_path(ctxt.tcx, *did);
            let is_box = Some(*did) == ctxt.tcx.lang_items().owned_box() && args.len() == 2;
            let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(ctxt.tcx, *did));
            let is_smart_ptr = def_name == "alloc::rc::Rc" || def_name == "alloc::sync::Arc";
            let mut typ_args: Vec<Typ> = Vec::new();
            for arg in args.iter() {
                match arg.unpack() {
                    rustc_middle::ty::subst::GenericArgKind::Type(t) => {
                        typ_args.push(erase_ty(ctxt, state, t));
                    }
                    rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                        let lifetime = erase_hir_region(ctxt, state, region);
                        if let Some(lifetime) = lifetime {
                            typ_args.push(Box::new(TypX::TypParam(lifetime)));
                        } else {
                            typ_args.push(Box::new(TypX::Primitive("'_".to_string())));
                        }
                    }
                    _ => panic!("unexpected type argument"),
                }
            }
            let datatype_name = if is_box || is_smart_ptr {
                if is_box {
                    typ_args.pop();
                }
                assert!(typ_args.len() == 1);
                let name = path.segments.last().expect("builtin").to_string();
                Id::new(IdKind::Builtin, 0, name)
            } else {
                state.datatype_name(&path)
            };
            Box::new(TypX::Datatype(datatype_name, typ_args))
        }
        TyKind::Closure(..) => Box::new(TypX::Closure),
        _ => {
            dbg!(ty);
            panic!("unexpected type")
        }
    }
}

fn erase_pat<'tcx>(ctxt: &Context, state: &mut State, pat: &Pat) -> Pattern {
    let mk_pat = |p: PatternX| Box::new((pat.span, p));
    match &pat.kind {
        PatKind::Wild => mk_pat(PatternX::Wildcard),
        PatKind::Binding(ann, hir_id, x, None) => {
            let id = state.local(local_to_var(x, hir_id.local_id));
            let m = match ann {
                BindingAnnotation::Unannotated => Mutability::Not,
                BindingAnnotation::Mutable => Mutability::Mut,
                _ => panic!(),
            };
            mk_pat(PatternX::Binding(id, m))
        }
        PatKind::Path(QPath::Resolved(None, rustc_hir::Path { res, .. })) => {
            let (vir_path, variant_name) = datatype_variant_of_res(ctxt.tcx, res, true);
            let name = state.datatype_name(&vir_path);
            let variant = state.variant(variant_name.to_string());
            mk_pat(PatternX::DatatypeTuple(name, Some(variant), vec![]))
        }
        PatKind::Box(p) => mk_pat(PatternX::Box(erase_pat(ctxt, state, p))),
        PatKind::Or(pats) => {
            let mut patterns: Vec<Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(erase_pat(ctxt, state, pat));
            }
            mk_pat(PatternX::Or(patterns))
        }
        PatKind::Tuple(pats, None) => {
            let mut patterns: Vec<Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(erase_pat(ctxt, state, pat));
            }
            mk_pat(PatternX::Tuple(patterns))
        }
        PatKind::TupleStruct(
            QPath::Resolved(
                None,
                rustc_hir::Path { res: res @ Res::Def(DefKind::Ctor(ctor_of, _), _), .. },
            ),
            pats,
            None,
        ) => {
            let is_variant = *ctor_of == rustc_hir::def::CtorOf::Variant;
            let (vir_path, variant_name) = datatype_variant_of_res(ctxt.tcx, res, is_variant);
            let name = state.datatype_name(&vir_path);
            let variant_name = state.variant(variant_name.to_string());
            let mut patterns: Vec<Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(erase_pat(ctxt, state, pat));
            }
            let variant = if is_variant { Some(variant_name) } else { None };
            mk_pat(PatternX::DatatypeTuple(name, variant, patterns))
        }
        PatKind::Struct(
            QPath::Resolved(None, rustc_hir::Path { res: res @ Res::Def(DefKind::Variant, _), .. }),
            pats,
            _,
        ) => {
            let (vir_path, variant_name) = datatype_variant_of_res(ctxt.tcx, res, false);
            let name = state.datatype_name(&vir_path);
            let variant = state.variant(variant_name.to_string());
            let mut binders: Vec<(Id, Pattern)> = Vec::new();
            for pat in pats.iter() {
                let field = state.local(pat.ident.to_string());
                let pattern = erase_pat(ctxt, state, &pat.pat);
                binders.push((field, pattern));
            }
            mk_pat(PatternX::DatatypeStruct(name, Some(variant), binders))
        }
        PatKind::Struct(
            QPath::Resolved(None, rustc_hir::Path { res: res @ Res::Def(DefKind::Struct, _), .. }),
            pats,
            _,
        ) => {
            let vir_path = def_id_to_vir_path(ctxt.tcx, res.def_id());
            let name = state.datatype_name(&vir_path);
            let mut binders: Vec<(Id, Pattern)> = Vec::new();
            for pat in pats.iter() {
                let field = state.local(pat.ident.to_string());
                let pattern = erase_pat(ctxt, state, &pat.pat);
                binders.push((field, pattern));
            }
            mk_pat(PatternX::DatatypeStruct(name, None, binders))
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

fn erase_spec_exps_force<'tcx>(
    ctxt: &Context,
    state: &mut State,
    span: Span,
    typ: Typ,
    exps: Vec<Option<Exp>>,
) -> Exp {
    erase_spec_exps_typ(ctxt, state, span, |_| typ, exps, true).expect("erase expr force")
}

fn erase_spec_exps<'tcx>(
    ctxt: &Context,
    state: &mut State,
    expr: &Expr,
    exps: Vec<Option<Exp>>,
) -> Option<Exp> {
    let expr_typ = |state: &mut State| erase_ty(ctxt, state, ctxt.types().node_type(expr.hir_id));
    erase_spec_exps_typ(ctxt, state, expr.span, expr_typ, exps, false)
}

fn phantom_data_expr<'tcx>(ctxt: &Context, state: &mut State, expr: &Expr) -> Exp {
    let e = erase_expr(ctxt, state, true, expr);
    let ty = ctxt.types().node_type(expr.hir_id);
    let typ = Box::new(TypX::Phantom(erase_ty(ctxt, state, ty)));
    erase_spec_exps_force(ctxt, state, expr.span, typ, vec![e])
}

fn force_block(exp: Option<Exp>, span: Span) -> Exp {
    match exp {
        None => Box::new((span, ExpX::Block(vec![], None))),
        Some(exp @ box (_, ExpX::Block(..))) => exp,
        Some(exp @ box (span, _)) => Box::new((span, ExpX::Block(vec![], Some(exp)))),
    }
}

fn mk_typ_args<'tcx>(
    ctxt: &Context,
    state: &mut State,
    node_substs: &[rustc_middle::ty::subst::GenericArg<'tcx>],
) -> Vec<Typ> {
    let mut typ_args: Vec<Typ> = Vec::new();
    for typ_arg in node_substs {
        match typ_arg.unpack() {
            GenericArgKind::Type(ty) => {
                typ_args.push(erase_ty(ctxt, state, ty));
            }
            GenericArgKind::Lifetime(_) => {}
            _ => panic!("typ_arg"),
        }
    }
    typ_args
}

fn erase_call<'tcx>(
    ctxt: &Context,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr,
    expr_fun: Option<&Expr>,
    node_substs: &[rustc_middle::ty::subst::GenericArg<'tcx>],
    fn_span: Span,
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
        ResolvedCall::CompilableOperator => {
            let exps = args_slice.iter().map(|a| erase_expr(ctxt, state, expect_spec, a)).collect();
            erase_spec_exps(ctxt, state, expr, exps)
        }
        ResolvedCall::Call(f_name) => {
            if !ctxt.functions.contains_key(f_name) {
                panic!("internal error: function call to {:?} not found", f_name);
            }
            let f = &ctxt.functions[f_name];
            let f = if let Some(f) = f {
                f
            } else {
                panic!("internal error: call to external function {:?}", f_name);
            };
            if f.x.mode == Mode::Spec {
                return None;
            }
            let typ_args = mk_typ_args(ctxt, state, node_substs);
            let mut exps: Vec<Exp> = Vec::new();
            let mut is_first: bool = true;
            assert!(args_slice.len() == f.x.params.len());
            for (param, e) in f.x.params.iter().zip(args_slice.iter()) {
                if param.x.mode == Mode::Spec {
                    let exp = erase_expr(ctxt, state, true, e);
                    is_some = is_some || exp.is_some();
                    exps.push(erase_spec_exps_force(
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
                let name = state.fun_name(f_name);
                let target = Box::new((fn_span, ExpX::Var(name)));
                mk_exp(ExpX::Call(target, typ_args, exps))
            }
        }
        ResolvedCall::Ctor(path, variant_name) => {
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
                let variant_opt =
                    if is_variant { Some(state.variant(variant_name.to_string())) } else { None };
                mk_exp(ExpX::DatatypeTuple(state.datatype_name(path), variant_opt, typ_args, args))
            }
        }
        ResolvedCall::NonStaticExec => {
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
    ctxt: &Context,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr,
    cond: &Expr,
    arms: Vec<(Option<&Pat>, &Option<rustc_hir::Guard>, Option<&Expr>)>,
) -> Option<Exp> {
    let expr_typ = |state: &mut State| erase_ty(ctxt, state, ctxt.types().node_type(expr.hir_id));
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
                mk_exp1(ExpX::Op(vec![], erase_ty(ctxt, state, ctyp)))
            }
            Some(e) => e,
        };
        mk_exp(ExpX::Match(c, e_arms))
    }
}

fn erase_inv_block<'tcx>(ctxt: &Context, state: &mut State, span: Span, body: &Block) -> Exp {
    assert!(body.stmts.len() == 3);
    let open_stmt = &body.stmts[0];
    let mid_stmt = &body.stmts[1];
    let (_guard_hir, _inner_hir, inner_pat, arg, atomicity) =
        crate::rust_to_vir_expr::invariant_block_open(ctxt.tcx, open_stmt)
            .expect("invariant_block_open");
    let pat_typ = erase_ty(ctxt, state, ctxt.types().node_type(inner_pat.hir_id));
    let inner_pat = erase_pat(ctxt, state, inner_pat);
    let arg = erase_expr(ctxt, state, false, arg).expect("erase_inv_block arg");
    let mid_body = erase_stmt(ctxt, state, mid_stmt);
    Box::new((span, ExpX::OpenInvariant(atomicity, inner_pat, arg, pat_typ, mid_body)))
}

fn erase_expr<'tcx>(
    ctxt: &Context,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr,
) -> Option<Exp> {
    let expr = expr.peel_drop_temps();
    let expr_typ = |state: &mut State| erase_ty(ctxt, state, ctxt.types().node_type(expr.hir_id));
    let mk_exp1 = |e: ExpX| Box::new((expr.span, e));
    let mk_exp = |e: ExpX| Some(Box::new((expr.span, e)));
    match &expr.kind {
        ExprKind::Path(QPath::Resolved(None, path)) => {
            match path.res {
                Res::Local(id) => match ctxt.tcx.hir().get(id) {
                    Node::Binding(Pat {
                        kind: PatKind::Binding(_ann, id, ident, _pat), ..
                    }) => {
                        if expect_spec || ctxt.var_modes[&expr.hir_id] == Mode::Spec {
                            None
                        } else {
                            mk_exp(ExpX::Var(state.local(local_to_var(ident, id.local_id))))
                        }
                    }
                    _ => panic!("unsupported"),
                },
                Res::Def(def_kind, id) => match def_kind {
                    DefKind::Const => {
                        let vir_path = def_id_to_vir_path(ctxt.tcx, id);
                        let fun_name = Arc::new(FunX { path: vir_path, trait_path: None });
                        return mk_exp(ExpX::Var(state.fun_name(&fun_name)));
                    }
                    DefKind::Ctor(ctor_of, _ctor_kind) => {
                        // 0-argument datatype constructor
                        let is_variant = ctor_of == rustc_hir::def::CtorOf::Variant;
                        let (vir_path, variant_name) =
                            datatype_variant_of_res(ctxt.tcx, &path.res, is_variant);
                        let variant = if is_variant {
                            Some(state.variant(variant_name.to_string()))
                        } else {
                            None
                        };
                        let typ_args =
                            mk_typ_args(ctxt, state, ctxt.types().node_substs(expr.hir_id));
                        return mk_exp(ExpX::DatatypeTuple(
                            state.datatype_name(&vir_path),
                            variant,
                            typ_args,
                            vec![],
                        ));
                    }
                    _ => panic!("unsupported"),
                },
                _ => panic!("unsupported"),
            }
        }
        ExprKind::Path(_qpath @ QPath::TypeRelative(_ty, _path_seg)) => {
            if expect_spec {
                None
            } else {
                let typ = expr_typ(state);
                assert!(matches!(*typ, TypX::Primitive(_)));
                mk_exp(ExpX::Op(vec![], typ))
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
            let is_variant = match e0.kind {
                ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path {
                        res: Res::Def(DefKind::Ctor(rustc_hir::def::CtorOf::Variant, _), _),
                        ..
                    },
                )) => true,
                _ => false,
            };
            erase_call(
                ctxt,
                state,
                expect_spec,
                expr,
                Some(e0),
                ctxt.types().node_substs(e0.hir_id),
                e0.span,
                es,
                false,
                is_variant,
            )
        }
        ExprKind::MethodCall(_name_and_generics, fn_span, all_args, _call_span) => erase_call(
            ctxt,
            state,
            expect_spec,
            expr,
            None,
            ctxt.types().node_substs(expr.hir_id),
            *fn_span,
            all_args,
            true,
            false,
        ),
        ExprKind::Struct(QPath::Resolved(_, path), fields, spread) => {
            if expect_spec {
                let mut exps: Vec<Option<Exp>> = Vec::new();
                for f in fields.iter() {
                    exps.push(erase_expr(ctxt, state, expect_spec, f.expr));
                }
                erase_spec_exps(ctxt, state, expr, exps)
            } else {
                let pop_variant = matches!(path.res, Res::Def(DefKind::Variant, _));
                let (vir_path, variant_name) =
                    datatype_constructor_variant_of_res(ctxt.tcx, &path.res, pop_variant);
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
                    if pop_variant { Some(state.variant(variant_name.to_string())) } else { None };
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
            erase_spec_exps(ctxt, state, expr, vec![exp1, exp2])
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
                mk_exp(ExpX::Assign(exp1.expect("expr"), exp2.expect("expr")))
            }
        }
        ExprKind::AssignOp(_op, e1, e2) => {
            let mode1 = ctxt.var_modes[&e1.hir_id];
            if mode1 == Mode::Spec {
                let exp1 = erase_expr(ctxt, state, true, e1);
                let exp2 = erase_expr(ctxt, state, true, e2);
                erase_spec_exps(ctxt, state, expr, vec![exp1, exp2])
            } else {
                let exp1 = erase_expr(ctxt, state, false, e1);
                let exp2 = erase_expr(ctxt, state, false, e2);
                let exp2 = erase_spec_exps(ctxt, state, expr, vec![exp2]);
                mk_exp(ExpX::Assign(exp1.expect("expr"), exp2.expect("expr")))
            }
        }
        ExprKind::If(cond, lhs, rhs) => {
            let cond_spec = ctxt.condition_modes[&expr.hir_id] == Mode::Spec;
            let cond = cond.peel_drop_temps();
            match cond.kind {
                ExprKind::Let(pat, src_expr, _let_span) => {
                    let arm1 = (Some(pat), &None, Some(*lhs));
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
                        (true, Some(e1), None) => {
                            erase_spec_exps(ctxt, state, expr, vec![ec, Some(e1)])
                        }
                        (true, None, Some(e2)) => {
                            erase_spec_exps(ctxt, state, expr, vec![ec, Some(e2)])
                        }
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
            let label = label.map(|l| state.lifetime(l.ident.to_string()));
            mk_exp(ExpX::While(c, b, label))
        }
        ExprKind::Loop(block, label, _source, _span) => {
            let b = force_block(erase_block(ctxt, state, false, block), block.span);
            let label = label.map(|l| state.lifetime(l.ident.to_string()));
            mk_exp(ExpX::Loop(b, label))
        }
        ExprKind::Break(dest, None) => {
            let label = dest.label.map(|l| state.lifetime(l.ident.to_string()));
            mk_exp(ExpX::Break(label))
        }
        ExprKind::Continue(dest) => {
            let label = dest.label.map(|l| state.lifetime(l.ident.to_string()));
            mk_exp(ExpX::Continue(label))
        }
        ExprKind::Ret(None) => mk_exp(ExpX::Ret(None)),
        ExprKind::Ret(Some(expr)) => {
            let exp = erase_expr(ctxt, state, ctxt.ret_spec.expect("ret_spec"), expr);
            mk_exp(ExpX::Ret(exp))
        }
        ExprKind::Closure(capture_by, _fn_decl, body_id, _span, movability) => {
            let mut params: Vec<(Span, Id, Typ)> = Vec::new();
            let body = ctxt.tcx.hir().body(*body_id);
            let ps = &body.params;
            for p in ps.iter() {
                let x = state.local(crate::rust_to_vir_expr::pat_to_var(p.pat));
                let typ = erase_ty(ctxt, state, ctxt.types().node_type(p.hir_id));
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
    ctxt: &Context,
    state: &mut State,
    expect_spec: bool,
    block: &Block,
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

fn erase_stmt<'tcx>(ctxt: &Context, state: &mut State, stmt: &Stmt) -> Vec<Stm> {
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

fn erase_hir_bounds<'tcx>(
    _ctxt: &Context,
    state: &mut State,
    bounds: GenericBounds<'tcx>,
) -> Vec<Bound> {
    let mut bnds: Vec<Bound> = Vec::new();
    for bound in bounds {
        match bound {
            GenericBound::Trait(..) => {}
            GenericBound::LangItemTrait(..) => {}
            GenericBound::Outlives(lifetime) => {
                bnds.push(Bound::Id(state.lifetime(lifetime.name.ident().to_string())));
            }
        }
    }
    bnds
}

fn erase_const<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context,
    state: &mut State,
    span: Span,
    id: DefId,
    external_body: bool,
    body_id: &BodyId,
) {
    let path = def_id_to_vir_path(ctxt.tcx, id);
    if let Some(s) = path.segments.last() {
        if s.to_string().starts_with("_DERIVE_builtin_Structural_FOR_") {
            return;
        }
    }
    let fun_name = Arc::new(FunX { path, trait_path: None });
    if let Some(f_vir) = &ctxt.functions[&fun_name] {
        if f_vir.x.mode == Mode::Spec && f_vir.x.ret.x.mode == Mode::Spec {
            return;
        }
        let def = rustc_middle::ty::WithOptConstParam::unknown(body_id.hir_id.owner);
        let types = ctxt.tcx.typeck_opt_const_arg(def);
        ctxt.types_opt = Some(types);
        ctxt.ret_spec = Some(f_vir.x.ret.x.mode == Mode::Spec);

        let name = state.fun_name(&fun_name);
        let ty = ctxt.tcx.type_of(id);
        let typ = erase_ty(ctxt, state, ty);
        let body = crate::rust_to_vir_func::find_body_krate(krate, body_id);
        let body_exp = if external_body {
            Box::new((body.value.span, ExpX::Panic))
        } else {
            erase_expr(ctxt, state, false, &body.value).expect("const body")
        };
        let decl = ConstDecl { span, name, typ, body: body_exp };
        state.const_decls.push(decl);
        ctxt.types_opt = None;
        ctxt.ret_spec = None;
    }
}

fn erase_fn<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context,
    state: &mut State,
    name_span: Span,
    id: DefId,
    sig: &FnSig<'tcx>,
    trait_path: Option<Path>,
    hir_generics: &Generics<'tcx>,
    impl_generics: Option<(&Generics<'tcx>, DefId)>,
    empty_body: bool,
    external_body: bool,
    body_id: &BodyId,
) {
    if ctxt.ignored_functions.contains(&id) {
        return;
    }
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let fun_name = Arc::new(FunX { path: path.clone(), trait_path });
    if let Some(f_vir) = &ctxt.functions[&fun_name] {
        if f_vir.x.mode == Mode::Spec {
            return;
        }
        let def = rustc_middle::ty::WithOptConstParam::unknown(body_id.hir_id.owner);
        let types = ctxt.tcx.typeck_opt_const_arg(def);
        ctxt.types_opt = Some(types);
        ctxt.ret_spec = Some(f_vir.x.ret.x.mode == Mode::Spec);

        let expect_spec = f_vir.x.ret.x.mode == Mode::Spec;
        let body = crate::rust_to_vir_func::find_body_krate(krate, body_id);
        let body_exp = if external_body {
            force_block(Some(Box::new((sig.span, ExpX::Panic))), sig.span)
        } else {
            let body_exp = erase_expr(ctxt, state, expect_spec, &body.value);
            if empty_body {
                if let Some(_) = body_exp {
                    panic!("expected empty method body")
                } else {
                    force_block(Some(Box::new((sig.span, ExpX::Panic))), sig.span)
                }
            } else {
                force_block(body_exp, body.value.span)
            }
        };
        let fn_sig = ctxt.tcx.fn_sig(id);
        let fn_sig = fn_sig.skip_binder();
        state.rename_count += 1;
        let name = state.fun_name(&fun_name);
        let ps = &body.params;
        let inputs = &fn_sig.inputs();
        assert!(inputs.len() == ps.len());
        assert!(inputs.len() == f_vir.x.params.len());
        let mut lifetimes: Vec<GenericParam> = Vec::new();
        let mut typ_params: Vec<GenericParam> = Vec::new();
        // Example: fn f<'a, 'b: 'a, 'c, A: 'b>(a: &'a A, x: &'c u64, y: &u32) -> &'c u64 { x }
        // In this example:
        //   hir_generics has 'a, 'b, 'c, and A, with bounds as HIR types
        //   mir_generics has 'a, 'b, and A, with bounds as MIR types (missing 'c)
        //   sig.decl.inputs has HIR types &'a A, &'c u64, &u32
        //   fn_sig.inputs has MIR types &'a A, &'c u64, &u32
        //   the patterns in body.params have MIR types &A, &u64, &u32 (missing 'a, 'c)
        // We generally use MIR types because TypeckResults uses them (also, THIR uses them).
        // But hir_generics has a more complete set of lifetime parameters.
        // So we use both hir_generics and mir_generics.
        let f_hir_generics = |state: &mut State,
                              generics: &Generics,
                              lifetimes: &mut Vec<GenericParam>| {
            for gparam in generics.params {
                let bnds = erase_hir_bounds(ctxt, state, gparam.bounds);
                match gparam.kind {
                    GenericParamKind::Lifetime { .. } => {
                        lifetimes.push((state.lifetime(&gparam.name.ident().to_string()), bnds));
                    }
                    GenericParamKind::Type { .. } => {}
                    GenericParamKind::Const { .. } => panic!(),
                }
            }
        };
        let f_mir_generics = |state: &mut State, id: DefId, typ_params: &mut Vec<GenericParam>| {
            let mir_generics = ctxt.tcx.generics_of(id);
            let mir_predicates = ctxt.tcx.predicates_of(id);
            let mut fn_traits: HashMap<Id, ClosureKind> = HashMap::new();
            let mut fn_projections: HashMap<Id, (Typ, Typ)> = HashMap::new();
            for gparam in &mir_generics.params {
                match gparam.kind {
                    GenericParamDefKind::Lifetime => {}
                    GenericParamDefKind::Type { .. } => {
                        let x = state.typ_param(gparam.name.to_string(), Some(gparam.index));
                        typ_params.push((x, vec![]));
                    }
                    GenericParamDefKind::Const { .. } => panic!(),
                }
            }
            for (pred, _) in mir_predicates.predicates.iter() {
                match pred.kind().no_bound_vars().expect("no_bound_vars") {
                    PredicateKind::RegionOutlives(_pred) => {}
                    PredicateKind::TypeOutlives(pred) => {
                        let x = match *erase_ty(ctxt, state, &pred.0) {
                            TypX::TypParam(x) => x,
                            _ => panic!("PredicateKind::TypeOutlives"),
                        };
                        let bound = erase_hir_region(ctxt, state, &pred.1).expect("bound");
                        let x_ref = typ_params.iter_mut().find(|(y, _)| *y == x);
                        let x_ref = x_ref.expect("generic param bound");
                        x_ref.1.push(Bound::Id(bound));
                    }
                    PredicateKind::Trait(pred) => {
                        let x = match *erase_ty(ctxt, state, pred.trait_ref.substs[0].expect_ty()) {
                            TypX::TypParam(x) => x,
                            _ => panic!("PredicateKind::Trait"),
                        };
                        let id = pred.trait_ref.def_id;
                        let bound = if Some(id) == ctxt.tcx.lang_items().copy_trait() {
                            Some(Bound::Copy)
                        } else {
                            None
                        };
                        if let Some(bound) = bound {
                            let x_ref = typ_params.iter_mut().find(|(y, _)| *y == x);
                            let x_ref = x_ref.expect("generic param bound");
                            x_ref.1.push(bound);
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
                            fn_traits.insert(x, kind).map(|_| panic!("{:?}", pred));
                        }
                    }
                    PredicateKind::Projection(pred) => {
                        if Some(pred.projection_ty.item_def_id)
                            == ctxt.tcx.lang_items().fn_once_output()
                        {
                            assert!(pred.projection_ty.substs.len() == 2);
                            let x_ty = pred.projection_ty.substs[0].expect_ty();
                            let x = match *erase_ty(ctxt, state, x_ty) {
                                TypX::TypParam(x) => x,
                                _ => panic!("PredicateKind::Projection"),
                            };
                            let mut fn_params = match pred.projection_ty.substs[1].unpack() {
                                GenericArgKind::Type(ty) => erase_ty(ctxt, state, ty),
                                _ => panic!("unexpected fn projection"),
                            };
                            if !matches!(*fn_params, TypX::Tuple(_)) {
                                fn_params = Box::new(TypX::Tuple(vec![fn_params]));
                            }
                            let fn_ret = erase_ty(ctxt, state, &pred.ty);
                            fn_projections
                                .insert(x, (fn_params, fn_ret))
                                .map(|_| panic!("{:?}", pred));
                        }
                    }
                    _ => {
                        dbg!(pred.kind());
                        panic!("unexpected bound")
                    }
                }
            }
            for (x, bnds) in typ_params.iter_mut() {
                if fn_traits.contains_key(&x) {
                    let (params, ret) = fn_projections.remove(&x).expect("fn_projections");
                    let kind = fn_traits.remove(&x).expect("fn_traits");
                    bnds.push(Bound::Fn(kind, params, ret))
                }
            }
        };
        if let Some((impl_generics, impl_id)) = impl_generics {
            f_hir_generics(state, impl_generics, &mut lifetimes);
            f_mir_generics(state, impl_id, &mut typ_params);
        }
        f_hir_generics(state, hir_generics, &mut lifetimes);
        f_mir_generics(state, id, &mut typ_params);
        let mut params: Vec<(Span, Id, Typ)> = Vec::new();
        for ((input, param), p) in inputs.iter().zip(f_vir.x.params.iter()).zip(ps.iter()) {
            let x = state.local(param.x.name.to_string());
            let typ = if param.x.mode == Mode::Spec {
                TypX::mk_unit()
            } else {
                erase_ty(ctxt, state, input)
            };
            params.push((p.pat.span, x, typ));
        }
        let ret = match sig.decl.output {
            rustc_hir::FnRetTy::DefaultReturn(_) => None,
            rustc_hir::FnRetTy::Return(ty) => {
                if f_vir.x.ret.x.mode == Mode::Spec {
                    None
                } else {
                    Some((ty.span, erase_ty(ctxt, state, fn_sig.output())))
                }
            }
        };
        let decl = FunDecl {
            sig_span: sig.span,
            name_span,
            name,
            // lifetimes must precede typ_params
            generics: lifetimes.into_iter().chain(typ_params.into_iter()).collect(),
            params,
            ret,
            body: body_exp,
        };
        state.fun_decls.push(decl);
        ctxt.types_opt = None;
        ctxt.ret_spec = None;
    }
}

fn erase_trait<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context,
    state: &mut State,
    trait_id: DefId,
    generics: &Generics<'tcx>,
    items: &[TraitItemRef],
) {
    for trait_item_ref in items {
        let trait_item = ctxt.tcx.hir().trait_item(trait_item_ref.id);
        let TraitItem { ident, def_id, generics: item_generics, kind, span: _ } = trait_item;
        match kind {
            TraitItemKind::Fn(sig, fun) => {
                let body_id = match fun {
                    TraitFn::Provided(body_id) => body_id,
                    _ => panic!("unexpected trait function"),
                };
                let id = def_id.to_def_id();
                erase_fn(
                    krate,
                    ctxt,
                    state,
                    ident.span,
                    id,
                    sig,
                    None,
                    item_generics,
                    Some((generics, trait_id)),
                    true,
                    false,
                    body_id,
                );
            }
            _ => panic!("unexpected trait item"),
        }
    }
}

fn erase_impl<'tcx>(
    krate: &'tcx Crate<'tcx>,
    ctxt: &mut Context,
    state: &mut State,
    impl_id: DefId,
    impll: &Impl,
) {
    let trait_path = if let Some(TraitRef { path, hir_ref_id: _ }) = impll.of_trait {
        Some(def_id_to_vir_path(ctxt.tcx, path.res.def_id()))
    } else {
        None
    };
    for impl_item_ref in impll.items {
        match impl_item_ref.kind {
            AssocItemKind::Fn { .. } => {
                let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                let ImplItem { ident, def_id, generics, kind, .. } = impl_item;
                let id = def_id.to_def_id();
                let attrs = ctxt.tcx.hir().attrs(impl_item.hir_id());
                let vattrs = get_verifier_attrs(attrs).expect("get_verifier_attrs");
                if vattrs.external {
                    continue;
                }
                if vattrs.is_variant.is_some() || vattrs.get_variant.is_some() {
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
                            trait_path.clone(),
                            generics,
                            Some((&impll.generics, impl_id)),
                            false,
                            vattrs.external_body,
                            body_id,
                        );
                    }
                    _ => panic!(),
                }
            }
            AssocItemKind::Type => {}
            _ => panic!("unexpected impl"),
        }
    }
}

fn erase_datatype<'tcx>(
    ctxt: &Context,
    state: &mut State,
    span: Span,
    id: DefId,
    hir_generics: &Generics<'tcx>,
    datatype: Datatype,
) {
    let datatype = Box::new(datatype);
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = state.datatype_name(&path);
    let implements_copy = ctxt.copy_types.contains(&id);
    let mut generics: Vec<GenericParam> = Vec::new();
    for gparam in hir_generics.params.iter() {
        let bnds = erase_hir_bounds(ctxt, state, gparam.bounds);
        match gparam.kind {
            GenericParamKind::Lifetime { .. } => {
                generics.push((state.lifetime(&gparam.name.ident().to_string()), bnds));
            }
            GenericParamKind::Type { .. } => {
                generics.push((state.typ_param(gparam.name.ident().to_string(), None), bnds));
            }
            GenericParamKind::Const { .. } => panic!(),
        }
    }
    let decl = DatatypeDecl { name, span, implements_copy, generics, datatype };
    state.datatype_decls.push(decl);
}

fn erase_variant_data<'tcx>(
    ctxt: &Context,
    state: &mut State,
    field_defs: impl Iterator<Item = &'tcx rustc_middle::ty::FieldDef>,
    variant_data: &VariantData<'tcx>,
) -> Fields {
    match variant_data {
        VariantData::Struct(fs, _) => {
            let mut fields: Vec<Field> = Vec::new();
            for (f, fd) in fs.iter().zip(field_defs) {
                let name = state.local(f.ident.to_string());
                let mut typ = erase_ty(ctxt, state, ctxt.tcx.type_of(fd.did));
                let mode = get_mode(Mode::Exec, ctxt.tcx.hir().attrs(f.hir_id));
                if mode == Mode::Spec {
                    typ = Box::new(TypX::Phantom(typ));
                }
                fields.push(Field { name, typ });
            }
            Fields::Named(fields)
        }
        VariantData::Tuple(fs, _) => {
            let mut fields: Vec<Typ> = Vec::new();
            for (f, fd) in fs.iter().zip(field_defs) {
                let mut typ = erase_ty(ctxt, state, ctxt.tcx.type_of(fd.did));
                let mode = get_mode(Mode::Exec, ctxt.tcx.hir().attrs(f.hir_id));
                if mode == Mode::Spec {
                    typ = Box::new(TypX::Phantom(typ));
                }
                fields.push(typ);
            }
            Fields::Pos(fields)
        }
        VariantData::Unit(..) => Fields::Pos(vec![]),
    }
}

fn erase_abstract_datatype<'tcx>(
    ctxt: &Context,
    state: &mut State,
    span: Span,
    id: DefId,
    hir_generics: &Generics<'tcx>,
) {
    let mut fields: Vec<Typ> = Vec::new();
    for gparam in hir_generics.params.iter() {
        match gparam.kind {
            GenericParamKind::Lifetime { .. } => {
                let x = state.lifetime(&gparam.name.ident().to_string());
                fields.push(Box::new(TypX::Ref(TypX::mk_bool(), Some(x), Mutability::Not)));
            }
            GenericParamKind::Type { .. } => {
                let x = state.typ_param(gparam.name.ident().to_string(), None);
                fields.push(Box::new(TypX::Phantom(Box::new(TypX::TypParam(x)))));
            }
            GenericParamKind::Const { .. } => panic!(),
        }
    }
    let datatype = Datatype::Struct(Fields::Pos(fields));
    erase_datatype(ctxt, state, span, id, hir_generics, datatype);
}

fn erase_struct<'tcx>(
    ctxt: &Context,
    state: &mut State,
    span: Span,
    id: DefId,
    hir_generics: &Generics<'tcx>,
    s: &VariantData<'tcx>,
) {
    let type_of = ctxt.tcx.type_of(id);
    let adt_def = type_of.ty_adt_def().expect("adt_def");
    let fields = erase_variant_data(ctxt, state, adt_def.all_fields(), s);
    let datatype = Datatype::Struct(fields);
    erase_datatype(ctxt, state, span, id, hir_generics, datatype);
}

fn erase_enum<'tcx>(
    ctxt: &Context,
    state: &mut State,
    span: Span,
    id: DefId,
    hir_generics: &Generics<'tcx>,
    e: &EnumDef<'tcx>,
) {
    let type_of = ctxt.tcx.type_of(id);
    let adt_def = type_of.ty_adt_def().expect("adt_def");
    let mut variants: Vec<(Id, Fields)> = Vec::new();
    for variant in e.variants.iter() {
        let name = state.variant(variant.ident.to_string());
        let variant_def_name = air::ast_util::str_ident(&variant.ident.as_str());
        let variant_def =
            crate::rust_to_vir_adts::get_mid_variant_def_by_name(&adt_def, &variant_def_name);
        let fields = erase_variant_data(ctxt, state, variant_def.fields.iter(), &variant.data);
        variants.push((name, fields));
    }
    let datatype = Datatype::Enum(variants);
    erase_datatype(ctxt, state, span, id, hir_generics, datatype);
}

pub(crate) fn gen_check_tracked_lifetimes<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &'tcx Crate<'tcx>,
    erasure_hints: &ErasureHints,
) -> State {
    let mut ctxt = Context {
        tcx,
        types_opt: None,
        functions: HashMap::new(),
        datatypes: HashMap::new(),
        ignored_functions: HashSet::new(),
        copy_types: HashSet::new(),
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
        ctxt.calls.insert(*hir_id, call.clone()).map(|_| panic!("{:?}", span));
    }
    for (span, mode) in &erasure_hints.erasure_modes.condition_modes {
        if !id_to_hir.contains_key(&span.id) {
            dbg!(span, span.id);
            panic!("missing id_to_hir");
        }
        for hir_id in &id_to_hir[&span.id] {
            ctxt.condition_modes.insert(*hir_id, *mode).map(|_| panic!("{:?}", span));
        }
    }
    for (span, mode) in &erasure_hints.erasure_modes.var_modes {
        if !id_to_hir.contains_key(&span.id) {
            dbg!(span, span.id);
            panic!("missing id_to_hir");
        }
        for hir_id in &id_to_hir[&span.id] {
            ctxt.var_modes.insert(*hir_id, *mode).map(|v| panic!("{:?} {:?}", span, v));
        }
    }
    for owner in krate.owners.iter() {
        if let Some(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Impl(Impl {
                        generics,
                        of_trait: Some(trait_ref),
                        self_ty:
                            rustc_hir::Ty {
                                kind: rustc_hir::TyKind::Path(QPath::Resolved(_, p)), ..
                            },
                        ..
                    }) => {
                        if Some(trait_ref.path.res.def_id()) == tcx.lang_items().copy_trait() {
                            let mut bounds_ok = true;
                            for param in generics.params {
                                for bound in param.bounds {
                                    if let GenericBound::Trait(pt_ref, _) = bound {
                                        if Some(pt_ref.trait_ref.path.res.def_id())
                                            == tcx.lang_items().copy_trait()
                                        {
                                            continue;
                                        }
                                    }
                                    // REVIEW: we don't yet try to handle bounds other than Copy
                                    // (example: we don't yet handle impl<A: Copy + Eq> Copy for S<A> {})
                                    bounds_ok = false;
                                }
                            }
                            if bounds_ok {
                                ctxt.copy_types.insert(p.res.def_id());
                            }
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }
    }

    for owner in krate.owners.iter() {
        if let Some(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => {
                    let attrs = tcx.hir().attrs(item.hir_id());
                    let vattrs = get_verifier_attrs(attrs).expect("get_verifier_attrs");
                    if vattrs.external {
                        continue;
                    }
                    if vattrs.is_variant.is_some() || vattrs.get_variant.is_some() {
                        continue;
                    }
                    let id = item.def_id.to_def_id();
                    match &item.kind {
                        ItemKind::Use { .. } => {}
                        ItemKind::ExternCrate { .. } => {}
                        ItemKind::Mod { .. } => {}
                        ItemKind::ForeignMod { .. } => {}
                        ItemKind::Macro(..) => {}
                        ItemKind::TyAlias(..) => {}
                        ItemKind::Static(..) => {}
                        ItemKind::GlobalAsm(..) => {}
                        ItemKind::Struct(s, generics) => {
                            if vattrs.external_body {
                                erase_abstract_datatype(&ctxt, &mut state, item.span, id, generics);
                            } else {
                                erase_struct(&ctxt, &mut state, item.span, id, generics, s);
                            }
                        }
                        ItemKind::Enum(e, generics) => {
                            if vattrs.external_body {
                                erase_abstract_datatype(&ctxt, &mut state, item.span, id, generics);
                            } else {
                                erase_enum(&ctxt, &mut state, item.span, id, generics, e);
                            }
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
                        ItemKind::Fn(sig, generics, body_id) => {
                            erase_fn(
                                krate,
                                &mut ctxt,
                                &mut state,
                                item.ident.span,
                                id,
                                sig,
                                None,
                                &generics,
                                None,
                                false,
                                vattrs.external_body,
                                body_id,
                            );
                        }
                        ItemKind::Trait(
                            IsAuto::No,
                            Unsafety::Normal,
                            trait_generics,
                            _bounds,
                            trait_items,
                        ) => {
                            erase_trait(
                                krate,
                                &mut ctxt,
                                &mut state,
                                id,
                                trait_generics,
                                trait_items,
                            );
                        }
                        ItemKind::Impl(impll) => {
                            erase_impl(krate, &mut ctxt, &mut state, id, impll);
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
    state
}
