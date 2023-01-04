use crate::attributes::{get_ghost_block_opt, get_verifier_attrs};
use crate::erase::{ErasureHints, ResolvedCall};
use crate::lifetime_ast::*;
use crate::rust_to_vir_base::{def_id_to_vir_path, local_to_var};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    BindingAnnotation, BlockCheckMode, Crate, Expr, ExprKind, HirId, Impl, ItemKind, Node,
    OwnerNode, Pat, PatKind, QPath, Stmt, StmtKind, VariantData,
};
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind, TypeckResults};
use rustc_span::def_id::DefId;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{Fun, FunX, Function, Mode, Path};

struct Context<'tcx> {
    tcx: TyCtxt<'tcx>,
    types: Option<&'tcx TypeckResults<'tcx>>,
    /// Map each function path to its VIR Function, or to None if it is a #[verifier(external)]
    /// function
    functions: HashMap<Fun, Option<Function>>,
    ignored_functions: HashSet<DefId>,
    /// Set of struct/enum that implement Copy
    copy_types: HashSet<DefId>,
    calls: HashMap<HirId, ResolvedCall>,
    /// Mode of each variable declaration and use.  For example, in
    /// "if x < 10 { x + 1 } else { x + 2 }", we will have three entries, one for each
    /// occurence of "x"
    /// REVIEW: replace Span with HirId (may require bundling Option<HirId> with SpanData in raw_span)
    var_modes: HashMap<Span, Mode>,
}

pub(crate) struct State {
    rename_count: usize,
    // Map path to new name
    id_to_name: HashMap<String, Id>,
    datatype_to_name: HashMap<Path, TypName>,
    pub(crate) datatype_decls: Vec<DatatypeDecl>,
    pub(crate) fun_decls: Vec<FunDecl>,
}

impl State {
    fn new() -> State {
        State {
            rename_count: 0,
            id_to_name: HashMap::new(),
            datatype_to_name: HashMap::new(),
            datatype_decls: Vec::new(),
            fun_decls: Vec::new(),
        }
    }

    fn id<S: Into<String>>(&mut self, raw_id: S) -> Id {
        let raw_id = raw_id.into();
        let name = self.id_to_name.get(&raw_id);
        if let Some(name) = name {
            return name.clone();
        }
        let name = Id::new(self.rename_count, raw_id.clone());
        self.rename_count += 1;
        self.id_to_name.insert(raw_id.clone(), name.clone());
        name
    }

    fn datatype_name<'tcx>(&mut self, path: &Path) -> TypName {
        // TODO: generics
        let name = self.datatype_to_name.get(path);
        if let Some(name) = name {
            return name.clone();
        }
        let name = TypName::new(self.rename_count, path.segments.last().expect("path").to_string());
        self.rename_count += 1;
        self.datatype_to_name.insert(path.clone(), name.clone());
        name
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

fn erase_ty<'tcx>(ctxt: &Context<'tcx>, state: &mut State, ty: Ty) -> Typ {
    match ty.kind() {
        TyKind::Bool | TyKind::Uint(_) | TyKind::Int(_) => {
            Box::new(TypX::Primitive(ty.to_string()))
        }
        TyKind::Adt(AdtDef { did, .. }, args) => {
            if args.len() != 0 {
                todo!();
            }
            let path = def_id_to_vir_path(ctxt.tcx, *did);
            Box::new(TypX::Datatype(state.datatype_name(&path)))
        }
        TyKind::Tuple(ts) => {
            if ts.len() != 0 {
                todo!();
            }
            Box::new(TypX::Primitive(ty.to_string()))
        }
        // TyKind:: ... => Box::new(TypX::Datatype(state.datatype_name(ctxt.tcx, res)))
        _ => {
            panic!("type: {}", ty.to_string());
        }
    }
}

fn erase_struct<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    data: &VariantData,
    adt_def: &'tcx rustc_middle::ty::AdtDef,
) -> Datatype {
    // TODO: erase fields based on modes
    match data {
        VariantData::Struct(fields, _) => {
            let fields = fields
                .iter()
                .zip(adt_def.all_fields())
                .map(|(f, fd)| Field {
                    name: state.id(f.ident.to_string()),
                    typ: erase_ty(ctxt, state, ctxt.tcx.type_of(fd.did)),
                })
                .collect();
            Datatype::Struct(Fields::Named(fields))
        }
        VariantData::Tuple(_fields, _) => {
            let fields = adt_def
                .all_fields()
                .map(|fd| erase_ty(ctxt, state, ctxt.tcx.type_of(fd.did)))
                .collect();
            Datatype::Struct(Fields::Pos(fields))
        }
        VariantData::Unit(..) => Datatype::Struct(Fields::Pos(vec![])),
    }
}

fn erase_pat<'tcx>(_ctxt: &Context, state: &mut State, pat: &Pat) -> Pattern {
    match &pat.kind {
        PatKind::Binding(BindingAnnotation::Unannotated, hir_id, x, None) => {
            let id = state.id(local_to_var(x, hir_id.local_id));
            Box::new((pat.span, PatternX::Binding(id)))
        }
        _ => todo!(),
    }
}

fn erase_expr<'tcx>(
    ctxt: &Context,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr,
) -> Option<Exp> {
    erase_expr_ext(ctxt, state, expect_spec, expr, false)
}

fn erase_expr_ext<'tcx>(
    ctxt: &Context,
    state: &mut State,
    expect_spec: bool,
    expr: &Expr,
    keep_block: bool,
) -> Option<Exp> {
    let mk_exp = |e: ExpX| Some(Box::new((expr.span, e)));
    match &expr.kind {
        ExprKind::Call(e0, es) => {
            let call = ctxt
                .calls
                .get(&expr.hir_id)
                .unwrap_or_else(|| panic!("internal error: missing function: {:?}", e0.span));
            /* TODO?
            let (qself, path, call) = match &e0.kind {
                ExprKind::Path(qself, path)
                    if ctxt.calls.contains_key(expr.hir_id) =>
                {
                    (qself, path, mctxt.find_span(&ctxt.calls, f_expr.span).clone())
                }
                ExprKind::Path(..) => panic!("internal error: missing function: {:?}", f_expr.span),
                _ => {
                    unsupported!("complex function call", f_expr)
                }
            };
            */
            match call {
                ResolvedCall::Spec => None,
                ResolvedCall::CompilableOperator => {
                    todo!()
                }
                // TODO? we shouldn't be dropping calls just because they *return* a spec               ResolvedCall::Call(_) if expect_spec => None,
                ResolvedCall::Call(f_name) => {
                    if !ctxt.functions.contains_key(f_name) {
                        panic!("internal error: function {:?} not found", f_name);
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
                    let mut exps: Vec<Exp> = Vec::new();
                    if let Some(exp) = erase_expr(ctxt, state, false, e0) {
                        exps.push(exp);
                    }
                    assert!(es.len() == f.x.params.len());
                    for (param, e) in f.x.params.iter().zip(es.iter()) {
                        if param.x.mode != Mode::Spec {
                            if let Some(exp) = erase_expr(ctxt, state, false, e) {
                                exps.push(exp);
                            }
                        }
                    }
                    let typ = erase_ty(
                        &ctxt,
                        state,
                        ctxt.types.expect("ctxt.types").node_type(expr.hir_id),
                    );
                    mk_exp(ExpX::Call(exps, typ))
                }
                ResolvedCall::Ctor(_path, _variant) => {
                    todo!()
                }
            }
        }
        ExprKind::Block(block, None) => {
            let attrs = ctxt.tcx.hir().attrs(expr.hir_id);
            if crate::rust_to_vir_expr::attrs_is_invariant_block(attrs).expect("attrs") {
                return None;
            }
            if let Some(_g_attr) = get_ghost_block_opt(ctxt.tcx.hir().attrs(expr.hir_id)) {
                dbg!(_g_attr);
                // TODO todo!()
            }

            assert!(block.rules == BlockCheckMode::DefaultBlock);
            assert!(!block.targeted_by_break);
            let mut stms: Vec<Stm> = Vec::new();

            for stmt in block.stmts {
                stms.extend(erase_stmt(ctxt, state, stmt));
            }
            let e = block.expr.and_then(|e| erase_expr(ctxt, state, expect_spec, e));
            if keep_block || stms.len() > 0 || e.is_some() {
                mk_exp(ExpX::Block(stms, e))
            } else {
                None
            }
        }
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            /* TODO
            if mctxt.find_span_opt(&ctxt.calls, expr.span).is_some() {
                // 0-argument datatype constructor
                expr.kind.clone()
            } else if keep_mode(ctxt, *mctxt.find_span(&ctxt.var_modes, expr.span)) {
                expr.kind.clone()
            } else {
                return None;
            }
            */
            Res::Local(id) => match ctxt.tcx.hir().get(id) {
                Node::Binding(pat) => {
                    if expect_spec || ctxt.var_modes[&expr.span] == Mode::Spec {
                        None
                    } else {
                        mk_exp(ExpX::Var(state.id(crate::rust_to_vir_expr::pat_to_var(pat))))
                    }
                }
                _ => panic!("unsupported"),
            },
            Res::Def(_def_kind, _id) => {
                // TODO?  REVIEW.
                None
            }
            _ => panic!("unsupported"),
        },
        _ => {
            dbg!("TODO");
            None
        }
    }
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
            let mode = ctxt.var_modes[&local.pat.span];
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
                let init_exp = if let Some(init) = local.init {
                    erase_expr(ctxt, state, false, init)
                } else {
                    None
                };
                vec![Box::new((stmt.span, StmX::Let(pat, init_exp)))]
            }
        }
        _ => todo!(),
    }
}

pub(crate) fn gen_check_tracked_lifetimes<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &'tcx Crate<'tcx>,
    erasure_hints: &ErasureHints,
) -> State {
    let mut ctxt = Context {
        tcx,
        types: None,
        functions: HashMap::new(),
        ignored_functions: HashSet::new(),
        copy_types: HashSet::new(),
        calls: HashMap::new(),
        var_modes: HashMap::new(),
    };
    let mut state = State::new();
    for f in &erasure_hints.vir_crate.functions {
        ctxt.functions.insert(f.x.name.clone(), Some(f.clone())).map(|_| panic!("{:?}", &f.x.name));
    }
    for (id, _span) in &erasure_hints.ignored_functions {
        ctxt.ignored_functions.insert(*id);
    }
    for (hir_id, span, call) in &erasure_hints.resolved_calls {
        ctxt.calls.insert(*hir_id, call.clone()).map(|_| panic!("{:?}", span));
    }
    for (span, mode) in &erasure_hints.erasure_modes.var_modes {
        let span = crate::util::from_raw_span(&span.raw_span);
        ctxt.var_modes.insert(span, *mode).map(|v| panic!("{:?} {:?}", span, v));
    }
    for owner in krate.owners.iter() {
        if let Some(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Impl(Impl {
                        of_trait: Some(trait_ref),
                        self_ty:
                            rustc_hir::Ty {
                                kind: rustc_hir::TyKind::Path(QPath::Resolved(_, p)), ..
                            },
                        ..
                    }) => {
                        if Some(trait_ref.path.res.def_id()) == tcx.lang_items().copy_trait() {
                            ctxt.copy_types.insert(p.res.def_id());
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
                    match &item.kind {
                        ItemKind::Struct(s, _generics) => {
                            let res: Res = Res::Def(DefKind::Struct, item.def_id.to_def_id());
                            let path = match res {
                                Res::Def(_, id) => def_id_to_vir_path(tcx, id),
                                _ => todo!(),
                                //Res::PrimTy(p) => TypName::new(None, p.name_str().to_string()),
                                //_ => TypName::new(Some(self.rename_count), "other".to_string()),
                            };
                            let name = state.datatype_name(&path);
                            let type_of = ctxt.tcx.type_of(item.def_id.to_def_id());
                            let adt_def = type_of.ty_adt_def().expect("adt_def");
                            let datatype = Box::new(erase_struct(&ctxt, &mut state, s, adt_def));
                            let implements_copy =
                                ctxt.copy_types.contains(&item.def_id.to_def_id());
                            let decl =
                                DatatypeDecl { name, implements_copy, span: item.span, datatype };
                            state.datatype_decls.push(decl);
                        }
                        ItemKind::Fn(sig, _generics, body_id) => {
                            let id = item.def_id.to_def_id();
                            if ctxt.ignored_functions.contains(&id) {
                                continue;
                            }
                            let path = def_id_to_vir_path(ctxt.tcx, id);
                            let fun_name = Arc::new(FunX { path: path.clone(), trait_path: None });
                            if let Some(f_vir) = &ctxt.functions[&fun_name] {
                                if f_vir.x.mode == Mode::Spec {
                                    continue;
                                }
                                let def = rustc_middle::ty::WithOptConstParam::unknown(
                                    body_id.hir_id.owner,
                                );
                                let types = ctxt.tcx.typeck_opt_const_arg(def);
                                ctxt.types = Some(types);

                                let expect_spec = f_vir.x.ret.x.mode == Mode::Spec;
                                let body = crate::rust_to_vir_func::find_body_krate(krate, body_id);
                                let body_exp =
                                    erase_expr(&ctxt, &mut state, expect_spec, &body.value);
                                if let Some(body_exp) = body_exp {
                                    let id = item.def_id.to_def_id();
                                    let fn_sig = ctxt.tcx.fn_sig(id);
                                    let fn_sig = fn_sig.skip_binder();
                                    state.rename_count += 1;
                                    let name = state
                                        .id(format!("f_{}_{}", item.ident, state.rename_count));
                                    let ps = &body.params;
                                    let inputs = &fn_sig.inputs();
                                    assert!(inputs.len() == ps.len());
                                    assert!(inputs.len() == f_vir.x.params.len());
                                    let mut params: Vec<(Span, Id, Typ)> = Vec::new();
                                    for ((input, param), p) in
                                        inputs.iter().zip(f_vir.x.params.iter()).zip(ps.iter())
                                    {
                                        if param.x.mode != Mode::Spec {
                                            let x = state.id(param.x.name.to_string());
                                            let typ = erase_ty(&ctxt, &mut state, input);
                                            params.push((p.pat.span, x, typ));
                                        }
                                    }
                                    let ret = match sig.decl.output {
                                        rustc_hir::FnRetTy::DefaultReturn(_) => None,
                                        rustc_hir::FnRetTy::Return(_ty) => {
                                            Some(erase_ty(&ctxt, &mut state, fn_sig.output()))
                                        }
                                    };
                                    let decl = FunDecl { name, params, ret, body: body_exp };
                                    state.fun_decls.push(decl);
                                    ctxt.types = None;
                                }
                            }
                        }
                        _ => {}
                    }
                }
                //OwnerNode::Item(Item { kind: ItemKind::Mod(mod_), def_id, .. }) => {
                //}
                _ => {
                    // TODO
                }
            }
        }
    }
    state
}
