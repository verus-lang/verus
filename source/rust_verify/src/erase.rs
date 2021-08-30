use crate::rust_to_vir_base::get_verifier_attrs;
use crate::util::{from_raw_span, vec_map};
use crate::{unsupported, unsupported_unless};
use air::ast::Ident;
use rustc_ast::ast::{
    Block, Crate, Expr, ExprKind, FnDecl, FnKind, FnSig, Item, ItemKind, Local, ModKind, Param,
    Stmt, StmtKind,
};
use rustc_ast::ptr::P;
use rustc_interface::interface::Compiler;
use rustc_span::{Span, SpanData};
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Function, Krate, Mode};
use vir::modes::ErasureModes;

#[derive(Clone, Debug)]
pub enum ResolvedCall {
    Spec,
    CompilableOperator,
    Call(Ident),
}

#[derive(Clone)]
pub struct ErasureHints {
    pub vir_crate: Krate,
    pub resolved_calls: Vec<(SpanData, ResolvedCall)>,
    pub erasure_modes: ErasureModes,
    pub external_functions: Vec<Ident>,
}

#[derive(Clone)]
pub struct Ctxt {
    vir_crate: Krate,
    functions: HashMap<Ident, Option<Function>>,
    calls: HashMap<Span, ResolvedCall>,
    condition_modes: HashMap<Span, Mode>,
    var_modes: HashMap<Span, Mode>,
}

fn expr_to_call(ctxt: &Ctxt, expr: &Expr) -> ResolvedCall {
    match &expr.kind {
        ExprKind::Path(_, path) if path.segments.len() == 1 => ctxt.calls[&expr.span].clone(),
        _ => {
            unsupported!("complex function call", expr)
        }
    }
}

fn erase_expr(ctxt: &Ctxt, is_exec: bool, expr: &Expr) -> Expr {
    erase_expr_opt(ctxt, is_exec, expr).expect("erase_expr")
}

// replace e with e1; e2; ...; en, simplifying if possible
fn replace_with_exprs(expr: &Expr, exprs: Vec<Option<Expr>>) -> Option<Expr> {
    let mut exprs: Vec<Expr> = exprs.into_iter().filter_map(|e| e).collect();
    if exprs.len() == 0 {
        None
    } else if exprs.len() == 1 {
        Some(exprs.swap_remove(0))
    } else {
        let len = exprs.len();
        let stmts: Vec<Stmt> = exprs
            .into_iter()
            .enumerate()
            .map(|(i, expr)| {
                let Expr { id, span, .. } = expr;
                let kind =
                    if i == len - 1 { StmtKind::Expr(P(expr)) } else { StmtKind::Semi(P(expr)) };
                Stmt { id, kind, span }
            })
            .collect();
        let Expr { id, span, .. } = *expr; // for efficiency, don't call expr.clone()
        let rules = rustc_ast::BlockCheckMode::Default;
        let block = Block { stmts, id, rules, span, tokens: None };
        let kind = ExprKind::Block(P(block), None);
        Some(Expr { id, kind, span, attrs: expr.attrs.clone(), tokens: expr.tokens.clone() })
    }
}

fn erase_expr_opt(ctxt: &Ctxt, is_exec: bool, expr: &Expr) -> Option<Expr> {
    let kind = match &expr.kind {
        ExprKind::Lit(_) => {
            if is_exec {
                expr.kind.clone()
            } else {
                return None;
            }
        }
        ExprKind::Path(_, _) => match ctxt.var_modes[&expr.span] {
            Mode::Exec if is_exec => expr.kind.clone(),
            _ => return None,
        },
        ExprKind::Binary(op, e1, e2) => {
            if is_exec {
                let e1 = erase_expr(ctxt, is_exec, e1);
                let e2 = erase_expr(ctxt, is_exec, e2);
                ExprKind::Binary(*op, P(e1), P(e2))
            } else {
                let e1 = erase_expr_opt(ctxt, is_exec, e1);
                let e2 = erase_expr_opt(ctxt, is_exec, e2);
                return replace_with_exprs(expr, vec![e1, e2]);
            }
        }
        ExprKind::Assign(e1, e2, span) => {
            let is_exec1 = ctxt.var_modes[&e1.span] == Mode::Exec;
            if is_exec1 {
                let e1 = erase_expr(ctxt, true, e1);
                let e2 = erase_expr(ctxt, true, e2);
                ExprKind::Assign(P(e1), P(e2), *span)
            } else {
                let e1 = erase_expr_opt(ctxt, false, e1);
                let e2 = erase_expr_opt(ctxt, is_exec, e2);
                return replace_with_exprs(expr, vec![e1, e2]);
            }
        }
        ExprKind::Call(f_expr, args) => {
            let call = expr_to_call(ctxt, &**f_expr);
            match &call {
                ResolvedCall::Spec => return None,
                ResolvedCall::CompilableOperator => ExprKind::Call(
                    f_expr.clone(),
                    vec_map(args, |e| P(erase_expr(ctxt, is_exec, e))),
                ),
                ResolvedCall::Call(f_name) => {
                    let f = &ctxt.functions[f_name];
                    if let Some(f) = f {
                        match f.x.mode {
                            Mode::Spec | Mode::Proof => return None,
                            Mode::Exec => {
                                let mut new_args: Vec<P<Expr>> = Vec::new();
                                for (arg, param) in args.iter().zip(f.x.params.iter()) {
                                    if param.x.mode == Mode::Exec {
                                        new_args.push(P(erase_expr(ctxt, true, arg)));
                                    }
                                }
                                ExprKind::Call(f_expr.clone(), new_args)
                            }
                        }
                    } else {
                        return Some(expr.clone());
                    }
                }
            }
        }
        ExprKind::If(eb, e1, e2_opt) => match ctxt.condition_modes[&expr.span] {
            Mode::Spec | Mode::Proof => {
                let eb = erase_expr(ctxt, false, eb);
                return Some(eb);
            }
            Mode::Exec => {
                let eb = erase_expr(ctxt, true, eb);
                let e1 = erase_block(ctxt, is_exec, e1);
                let e2_opt = e2_opt.as_ref().map(|e2| P(erase_expr(ctxt, is_exec, e2)));
                ExprKind::If(P(eb), P(e1), e2_opt)
            }
        },
        ExprKind::While(eb, block, None) => {
            let eb = erase_expr(ctxt, true, eb);
            let block = erase_block(ctxt, true, block);
            ExprKind::While(P(eb), P(block), None)
        }
        ExprKind::Block(block, None) => ExprKind::Block(P(erase_block(ctxt, is_exec, block)), None),
        _ => {
            unsupported!("unsupported expr", expr)
        }
    };
    let Expr { id, span, .. } = *expr; // for efficiency, don't call expr.clone()
    Some(Expr { id, kind, span, attrs: expr.attrs.clone(), tokens: expr.tokens.clone() })
}

fn erase_stmt(ctxt: &Ctxt, is_exec: bool, stmt: &Stmt) -> Option<Stmt> {
    let kind = match &stmt.kind {
        StmtKind::Local(local) => {
            let is_exec1 = ctxt.var_modes[&local.pat.span] == Mode::Exec;
            if is_exec1 {
                let init = local.init.as_ref().map(|expr| P(erase_expr(ctxt, true, expr)));
                let Local { id, span, .. } = **local; // for efficiency, don't call local.clone()
                let local = Local {
                    id,
                    pat: local.pat.clone(),
                    ty: local.ty.clone(),
                    init,
                    span,
                    attrs: local.attrs.clone(),
                    tokens: local.tokens.clone(),
                };
                Some(StmtKind::Local(P(local)))
            } else {
                local.init.as_ref().and_then(|expr| {
                    erase_expr_opt(ctxt, false, expr).map(|expr| StmtKind::Semi(P(expr)))
                })
            }
        }
        StmtKind::Expr(expr) => erase_expr_opt(ctxt, is_exec, expr).map(|e| StmtKind::Expr(P(e))),
        StmtKind::Semi(expr) => erase_expr_opt(ctxt, false, expr).map(|e| StmtKind::Semi(P(e))),
        StmtKind::Empty => Some(stmt.kind.clone()),
        _ => {
            unsupported!("unsupported stmt", stmt)
        }
    };
    let Stmt { id, span, .. } = *stmt; // for efficiency, don't call stmt.clone()
    kind.map(|kind| Stmt { id, kind, span })
}

fn erase_block(ctxt: &Ctxt, is_exec: bool, block: &Block) -> Block {
    let stmts: Vec<Stmt> =
        block.stmts.iter().filter_map(|stmt| erase_stmt(ctxt, is_exec, stmt)).collect();
    let Block { id, rules, span, .. } = *block; // for efficiency, don't call block.clone()
    Block { stmts, id, rules, span, tokens: block.tokens.clone() }
}

fn erase_fn(ctxt: &Ctxt, f_name: &String, f: &FnKind) -> Option<FnKind> {
    let f_vir = &ctxt.functions[&Arc::new(f_name.clone())].as_ref().expect("erase_fn");
    match f_vir.x.mode {
        Mode::Spec | Mode::Proof => return None,
        Mode::Exec => {}
    }
    let FnKind(defaultness, sig, generics, body_opt) = f;
    let FnSig { header: _, decl, span: _ } = sig;
    let FnDecl { inputs, output } = &**decl;
    let mut new_inputs: Vec<Param> = Vec::new();
    for (input, param) in inputs.iter().zip(f_vir.x.params.iter()) {
        if param.x.mode == Mode::Exec {
            new_inputs.push(input.clone());
        }
    }
    let decl = FnDecl { inputs: new_inputs, output: output.clone() };
    let sig = FnSig { decl: P(decl), ..sig.clone() };
    let body_opt = body_opt.as_ref().map(|body| P(erase_block(ctxt, true, &**body)));
    Some(FnKind(*defaultness, sig, generics.clone(), body_opt))
}

fn erase_mod(ctxt: &Ctxt, module: &ModKind) -> ModKind {
    match module {
        ModKind::Loaded(items, inlined, span) => {
            let items: Vec<P<Item>> =
                items.iter().map(|item| erase_item(ctxt, item)).flatten().collect();
            ModKind::Loaded(items, *inlined, *span)
        }
        _ => {
            unsupported!("unsupported module", module)
        }
    }
}

fn erase_item(ctxt: &Ctxt, item: &Item) -> Vec<P<Item>> {
    let kind = match &item.kind {
        ItemKind::ExternCrate(_) => item.kind.clone(),
        ItemKind::Use(_) => item.kind.clone(),
        ItemKind::Mod(unsafety, kind) => ItemKind::Mod(*unsafety, erase_mod(ctxt, kind)),
        ItemKind::Fn(kind) => {
            let vattrs = get_verifier_attrs(&item.attrs).expect("get_verifier_attrs");
            if vattrs.external {
                return vec![P(item.clone())];
            }
            match erase_fn(ctxt, &item.ident.name.to_string(), kind) {
                None => return vec![],
                Some(kind) => ItemKind::Fn(Box::new(kind)),
            }
        }
        _ => {
            unsupported!("unsupported item", item)
        }
    };
    let Item { id, span, ident, .. } = *item; // for efficiency, don't call item.clone()
    vec![P(Item {
        id,
        span,
        ident,
        kind,
        vis: item.vis.clone(),
        attrs: item.attrs.clone(),
        tokens: item.tokens.clone(),
    })]
}

pub(crate) fn erase_crate(ctxt: &Ctxt, krate: &Crate) -> Crate {
    let Crate { attrs, items, span, proc_macros } = krate;
    unsupported_unless!(proc_macros.len() == 0, "procedural macros", proc_macros);
    let mut new_items: Vec<P<Item>> = Vec::new();
    for item in items {
        new_items.extend(erase_item(ctxt, item));
    }
    Crate { items: new_items, attrs: attrs.clone(), span: *span, proc_macros: proc_macros.clone() }
}

struct EraseRewrite {
    ctxt: Ctxt,
}

impl rustc_lint::FormalVerifierRewrite for EraseRewrite {
    fn rewrite_crate(&mut self, c: &rustc_ast::ast::Crate) -> rustc_ast::ast::Crate {
        crate::erase::erase_crate(&self.ctxt, c)
    }
}

pub struct CompilerCallbacks {
    pub erasure_hints: ErasureHints,
}

fn mk_ctxt(erasure_hints: &ErasureHints) -> Ctxt {
    let mut functions = HashMap::new();
    let mut calls: HashMap<Span, ResolvedCall> = HashMap::new();
    for f in &erasure_hints.vir_crate.functions {
        functions.insert(f.x.name.clone(), Some(f.clone()));
    }
    for name in &erasure_hints.external_functions {
        functions.insert(name.clone(), None);
    }
    for (span, call) in &erasure_hints.resolved_calls {
        calls.insert(span.span(), call.clone());
    }
    let mut condition_modes: HashMap<Span, Mode> = HashMap::new();
    let mut var_modes: HashMap<Span, Mode> = HashMap::new();
    for (span, mode) in &erasure_hints.erasure_modes.condition_modes {
        condition_modes.insert(from_raw_span(&span.raw_span), *mode);
    }
    for (span, mode) in &erasure_hints.erasure_modes.var_modes {
        var_modes.insert(from_raw_span(&span.raw_span), *mode);
    }
    Ctxt {
        vir_crate: erasure_hints.vir_crate.clone(),
        functions,
        calls,
        condition_modes,
        var_modes,
    }
}

impl rustc_driver::Callbacks for CompilerCallbacks {
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let _ = {
            let expansion_result = queries.expansion().expect("expansion");
            let peeked = expansion_result.peek();
            let lint_store = &peeked.2;
            let ctxt = mk_ctxt(&self.erasure_hints);
            lint_store.formal_verifier_callback.replace(Some(Box::new(EraseRewrite { ctxt })));
        };
        rustc_driver::Compilation::Continue
    }
}
