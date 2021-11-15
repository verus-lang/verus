//! This module erases the non-compiled code ("ghost code") so that Rust can compile the
//! remaining code.  Ghost code includes #[spec] and #[proof] code.
//! This "erasure" step happens after verification, since the ghost code is needed
//! for verification.
//!
//! There are many possible ways we could potentially implement erasure:
//! - Erase ghost code from the VIR (vir::ast).  This would have the advantage that VIR contains
//!   the information that determines which code is ghost and which code is compiled.
//!   However, VIR is designed for verification and not compilation.
//!   It doesn't contain all of the original Rust code that the Rust compiler needs for
//!   compilation -- the translation from Rust to VIR is lossy and we can't recover the
//!   original Rust code from the VIR.
//! - Erase ghost code from Rust MIR or HIR.  These would be the most principled approaches:
//!   we would first verify the HIR/VIR code, and then remove the ghost code at a later
//!   stage in the overall Rust pipeline (AST -> HIR -> MIR -> LLVM -> machine code).
//!   However, this is easier said than done.  Erasure is a global operation that changes
//!   not just statements and expressions, but also datatypes and function types
//!   (for example, by removing fields from structs or parameters from functions).
//!   Doing this on HIR or MIR would likely require intrusive changes to the Rust compiler,
//!   which we're trying to avoid.
//! - After verifying HIR/VIR, throw away the HIR/VIR code, back up to an earlier stage
//!   (like Rust AST), erase the ghost code from that, and then run the whole pipeline
//!   (AST -> HIR -> MIR -> ...) on the erased code.  This isn't elegant, but it's relatively
//!   simple to implement, and it's therefore what we do.
//!
//! Specifically, after verifying HIR/VIR, we rerun the Rust compiler, but in this second
//! run, we intercept and rewrite the Rust AST to remove ghost code.
//! Deciding which code is ghost depends on the HIR/VIR analysis from the first run,
//! so we have to save information from the first run and pass it into the second run
//! (this information is passed in the ErasureHints struct defined below.)
//! In this saved information, we rely on Spans to match expressions and statements in the
//! HIR/VIR with the corresponding expressions and statements in the AST.
//!
//! In fact, we actually make three runs, because we want to run Rust's lifetime checking
//! on #[proof] variables.  In this run, we erase #[spec] but not #[proof] and #[code],
//! then we run mir_borrowck, then we stop and throw away the results.
//!
//! Summary of three runs:
//! 1) AST -> HIR -> VIR for verification on #[code], #[proof], #[spec]
//! 2) AST -> HIR -> VIR -> MIR for mir_borrowck on #[code], #[proof]
//! 3) AST -> HIR -> VIR -> MIR -> ... for compilation of #[code]
//!
//! Notes:
//!
//! #[verifier(external)] functions are kept verbatim.
//! #[verifier(no_verify)] functions, on the other hand, need erasure to remove requires/ensures.

use crate::rust_to_vir_base::get_verifier_attrs;
use crate::util::{from_raw_span, vec_map};
use crate::{unsupported, unsupported_unless};

use rustc_ast::ast::{
    Block, Crate, Expr, ExprKind, FnDecl, FnKind, FnSig, Item, ItemKind, Lit, LitIntType, LitKind,
    Local, ModKind, NodeId, Param, PathSegment, Stmt, StmtKind,
};
use rustc_ast::ptr::P;
use rustc_data_structures::thin_vec::ThinVec;
use rustc_interface::interface::Compiler;
use rustc_span::symbol::{Ident, Symbol};
use rustc_span::{Span, SpanData};

use std::cell::Cell;
use std::collections::HashMap;

use vir::ast::Path;
use vir::ast::{Function, Krate, Mode};
use vir::modes::ErasureModes;

/// Information about each call in the AST (each ExprKind::Call).
#[derive(Clone, Debug)]
pub enum ResolvedCall {
    /// The call is to a spec or proof function, and should be erased
    Spec,
    /// The call is to an operator like == or + that should be compiled.
    CompilableOperator,
    /// The call is to a function, and we record the resolved name of the function here.
    Call(Path),
}

#[derive(Clone)]
pub struct ErasureHints {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    pub vir_crate: Krate,
    /// Details of each call in the first run's HIR
    pub resolved_calls: Vec<(SpanData, ResolvedCall)>,
    /// Results of mode (spec/proof/exec) inference from first run's VIR
    pub erasure_modes: ErasureModes,
    /// List of #[verifier(external)] functions.  (These don't appear in vir_crate,
    /// so we need to record them separately here.)
    pub external_functions: Vec<Path>,
}

#[derive(Clone)]
pub struct Ctxt {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    vir_crate: Krate,
    /// Map each function path to its VIR Function, or to None if it is a #[verifier(external)]
    /// function
    functions: HashMap<Path, Option<Function>>,
    /// Map each function span to its VIR Function, excluding #[verifier(external)] functions
    functions_by_span: HashMap<Span, Function>,
    /// Details of each call in the first run's HIR
    calls: HashMap<Span, ResolvedCall>,
    /// Mode of each if/else or match condition, used to decide how to erase if/else and match
    /// condition.  For example, in "if x < 10 { x + 1 } else { x + 2 }", this will record the span
    /// and mode of the expression "x < 10"
    condition_modes: HashMap<Span, Mode>,
    /// Mode of each variable declaration and use.  For example, in
    /// "if x < 10 { x + 1 } else { x + 2 }", we will have three entries, one for each
    /// occurence of "x"
    var_modes: HashMap<Span, Mode>,
    /// Keep #[proof] variables, code if true, erase #[proof] if false
    keep_proofs: bool,
    /// counter to generate arbitrary unique integers
    arbitrary_counter: Cell<u64>,
}

struct MCtxt<'a> {
    f_next_node_id: &'a mut dyn FnMut() -> NodeId,
}

impl<'a> MCtxt<'a> {
    fn next_node_id(&mut self) -> NodeId {
        (self.f_next_node_id)()
    }
}

fn call_arbitrary(ctxt: &Ctxt, mctxt: &mut MCtxt, span: Span) -> Expr {
    // builtin::internal_arbitrary
    let strs = vec!["builtin", "internal_arbitrary"];
    let segments = vec_map(&strs, |s| PathSegment {
        ident: Ident::from_str(s),
        id: mctxt.next_node_id(),
        args: None,
    });
    let path = rustc_ast::ast::Path { span, segments, tokens: None };
    let kind = ExprKind::Path(None, path);
    let attrs = ThinVec::new();
    let id = mctxt.next_node_id();
    let expr_path = Expr { id, kind, span, attrs, tokens: None };

    // n
    let n = ctxt.arbitrary_counter.get();
    ctxt.arbitrary_counter.set(n + 1);
    let kind = rustc_ast::token::LitKind::Integer;
    let symbol = Symbol::intern(&n.to_string());
    let token = rustc_ast::token::Lit::new(kind, symbol, None);
    let kind = LitKind::Int(n as u128, LitIntType::Unsuffixed);
    let lit = Lit { token, kind, span };
    let kind = ExprKind::Lit(lit);
    let id = mctxt.next_node_id();
    let attrs = ThinVec::new();
    let expr_n = Expr { id, kind, span, attrs, tokens: None };

    // builtin::internal_arbitrary(n)
    let kind = ExprKind::Call(P(expr_path), vec![P(expr_n)]);
    let id = mctxt.next_node_id();
    let attrs = ThinVec::new();
    Expr { id, kind, span, attrs, tokens: None }
}

fn keep_mode(ctxt: &Ctxt, mode: Mode) -> bool {
    match mode {
        Mode::Spec => false,
        Mode::Proof => ctxt.keep_proofs,
        Mode::Exec => true,
    }
}

fn expr_to_call(ctxt: &Ctxt, expr: &Expr) -> ResolvedCall {
    match &expr.kind {
        ExprKind::Path(_, path) if path.segments.len() == 1 => ctxt.calls[&expr.span].clone(),
        _ => {
            unsupported!("complex function call", expr)
        }
    }
}

fn erase_expr(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, expr: &Expr) -> Expr {
    erase_expr_opt(ctxt, mctxt, expect, expr).expect("erase_expr")
}

/// Replace expr with e1; e2; ...; en, simplifying if possible
fn replace_with_exprs(mctxt: &mut MCtxt, expr: &Expr, exprs: Vec<Option<Expr>>) -> Option<Expr> {
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
                let id = mctxt.next_node_id();
                let span = expr.span;
                let kind =
                    if i == len - 1 { StmtKind::Expr(P(expr)) } else { StmtKind::Semi(P(expr)) };
                Stmt { id, kind, span }
            })
            .collect();
        let Expr { id, span, .. } = *expr; // for efficiency, don't call expr.clone()
        let rules = rustc_ast::BlockCheckMode::Default;
        let block = Block { stmts, id, rules, span, tokens: None };
        let kind = ExprKind::Block(P(block), None);
        let id = mctxt.next_node_id();
        Some(Expr { id, kind, span, attrs: expr.attrs.clone(), tokens: expr.tokens.clone() })
    }
}

/// Erase ghost code from expr, and return Some resulting expression.
/// If the entire expression is ghost, return None.
fn erase_expr_opt(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, expr: &Expr) -> Option<Expr> {
    let kind = match &expr.kind {
        ExprKind::Lit(_) => {
            if keep_mode(ctxt, expect) {
                expr.kind.clone()
            } else {
                return None;
            }
        }
        ExprKind::Path(_, _) => {
            if keep_mode(ctxt, ctxt.var_modes[&expr.span]) && keep_mode(ctxt, expect) {
                expr.kind.clone()
            } else {
                return None;
            }
        }
        ExprKind::Paren(e) => match erase_expr_opt(ctxt, mctxt, expect, e) {
            None => return None,
            Some(e) => ExprKind::Paren(P(e)),
        },
        ExprKind::AddrOf(borrow, mutability, e1) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                ExprKind::AddrOf(*borrow, *mutability, P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        ExprKind::Unary(op, e1) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                ExprKind::Unary(*op, P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        ExprKind::Binary(op, e1, e2) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                let e2 = erase_expr(ctxt, mctxt, expect, e2);
                ExprKind::Binary(*op, P(e1), P(e2))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1);
                let e2 = erase_expr_opt(ctxt, mctxt, expect, e2);
                return replace_with_exprs(mctxt, expr, vec![e1, e2]);
            }
        }
        ExprKind::Assign(e1, e2, span) => {
            let mode1 = ctxt.var_modes[&e1.span];
            if keep_mode(ctxt, mode1) {
                let e1 = erase_expr(ctxt, mctxt, mode1, e1);
                let e2 = erase_expr(ctxt, mctxt, mode1, e2);
                ExprKind::Assign(P(e1), P(e2), *span)
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, mode1, e1);
                let e2 = erase_expr_opt(ctxt, mctxt, expect, e2);
                return replace_with_exprs(mctxt, expr, vec![e1, e2]);
            }
        }
        ExprKind::Call(f_expr, args) => {
            let call = expr_to_call(ctxt, &**f_expr);
            match &call {
                ResolvedCall::Spec => return None,
                ResolvedCall::CompilableOperator => ExprKind::Call(
                    f_expr.clone(),
                    vec_map(args, |e| P(erase_expr(ctxt, mctxt, expect, e))),
                ),
                ResolvedCall::Call(f_path) => {
                    let f = &ctxt.functions[f_path];
                    if let Some(f) = f {
                        if keep_mode(ctxt, f.x.mode) {
                            let mut new_args: Vec<P<Expr>> = Vec::new();
                            for (arg, param) in args.iter().zip(f.x.params.iter()) {
                                if keep_mode(ctxt, param.x.mode) {
                                    new_args.push(P(erase_expr(ctxt, mctxt, param.x.mode, arg)));
                                }
                            }
                            ExprKind::Call(f_expr.clone(), new_args)
                        } else {
                            return None;
                        }
                    } else {
                        return Some(expr.clone());
                    }
                }
            }
        }
        ExprKind::If(eb, e1, e2_opt) => {
            let modeb = ctxt.condition_modes[&expr.span];
            let keep = |mctxt: &mut MCtxt, eb| {
                let e1 = erase_block(ctxt, mctxt, expect, e1);
                let e2_opt = e2_opt.as_ref().map(|e2| P(erase_expr(ctxt, mctxt, expect, e2)));
                ExprKind::If(P(eb), P(e1), e2_opt)
            };
            if modeb == Mode::Exec {
                let eb = erase_expr(ctxt, mctxt, modeb, eb);
                keep(mctxt, eb)
            } else {
                assert!(expect != Mode::Exec);
                if !ctxt.keep_proofs {
                    let eb = erase_expr(ctxt, mctxt, modeb, eb);
                    return Some(eb);
                } else if modeb == Mode::Spec && expect == Mode::Proof {
                    let eb_erase = erase_expr_opt(ctxt, mctxt, modeb, eb);
                    // We erase eb, so we have no bool for the If.
                    // Create a nondeterministic boolean to take eb's place.
                    let e_nondet = call_arbitrary(ctxt, mctxt, expr.span);
                    let eb = replace_with_exprs(mctxt, eb, vec![eb_erase, Some(e_nondet)]);
                    keep(mctxt, eb.expect("e_nondet"))
                } else {
                    let eb = erase_expr(ctxt, mctxt, modeb, eb);
                    keep(mctxt, eb)
                }
            }
        }
        ExprKind::While(eb, block, None) => {
            // The mode checker only allows While for Mode::Exec
            let eb = erase_expr(ctxt, mctxt, Mode::Exec, eb);
            let block = erase_block(ctxt, mctxt, Mode::Exec, block);
            ExprKind::While(P(eb), P(block), None)
        }
        ExprKind::Block(block, None) => {
            ExprKind::Block(P(erase_block(ctxt, mctxt, expect, block)), None)
        }
        _ => {
            unsupported!("unsupported expr", expr)
        }
    };
    let Expr { id, span, .. } = *expr; // for efficiency, don't call expr.clone()
    Some(Expr { id, kind, span, attrs: expr.attrs.clone(), tokens: expr.tokens.clone() })
}

/// Erase ghost code from stmt, and return Some resulting statement.
/// If the entire statment is ghost, return None.
fn erase_stmt(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, stmt: &Stmt) -> Option<Stmt> {
    let kind = match &stmt.kind {
        StmtKind::Local(local) => {
            let mode1 = ctxt.var_modes[&local.pat.span];
            if keep_mode(ctxt, mode1) {
                let init = local.init.as_ref().map(|expr| P(erase_expr(ctxt, mctxt, mode1, expr)));
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
                    erase_expr_opt(ctxt, mctxt, mode1, expr).map(|expr| StmtKind::Semi(P(expr)))
                })
            }
        }
        StmtKind::Expr(expr) => {
            erase_expr_opt(ctxt, mctxt, expect, expr).map(|e| StmtKind::Expr(P(e)))
        }
        StmtKind::Semi(expr) => {
            erase_expr_opt(ctxt, mctxt, Mode::Spec, expr).map(|e| StmtKind::Semi(P(e)))
        }
        StmtKind::Empty => Some(stmt.kind.clone()),
        _ => {
            unsupported!("unsupported stmt", stmt)
        }
    };
    let Stmt { id, span, .. } = *stmt; // for efficiency, don't call stmt.clone()
    kind.map(|kind| Stmt { id, kind, span })
}

fn erase_block(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, block: &Block) -> Block {
    let stmts: Vec<Stmt> =
        block.stmts.iter().filter_map(|stmt| erase_stmt(ctxt, mctxt, expect, stmt)).collect();
    let Block { id, rules, span, .. } = *block; // for efficiency, don't call block.clone()
    Block { stmts, id, rules, span, tokens: block.tokens.clone() }
}

fn erase_fn(ctxt: &Ctxt, mctxt: &mut MCtxt, f: &FnKind) -> Option<FnKind> {
    let FnKind(defaultness, sig, generics, body_opt) = f;
    let f_vir = &ctxt.functions_by_span[&sig.span];
    if !keep_mode(ctxt, f_vir.x.mode) {
        return None;
    }
    let FnSig { header: _, decl, span: _ } = sig;
    let FnDecl { inputs, output } = &**decl;
    let mut new_inputs: Vec<Param> = Vec::new();
    for (input, param) in inputs.iter().zip(f_vir.x.params.iter()) {
        if keep_mode(ctxt, param.x.mode) {
            new_inputs.push(input.clone());
        }
    }
    let decl = FnDecl { inputs: new_inputs, output: output.clone() };
    let sig = FnSig { decl: P(decl), ..sig.clone() };
    let body_opt = body_opt.as_ref().map(|body| P(erase_block(ctxt, mctxt, f_vir.x.mode, &**body)));
    Some(FnKind(*defaultness, sig, generics.clone(), body_opt))
}

fn erase_mod(ctxt: &Ctxt, mctxt: &mut MCtxt, module: &ModKind) -> ModKind {
    match module {
        ModKind::Loaded(items, inlined, span) => {
            let items: Vec<P<Item>> =
                items.iter().map(|item| erase_item(ctxt, mctxt, item)).flatten().collect();
            ModKind::Loaded(items, *inlined, *span)
        }
        _ => {
            unsupported!("unsupported module", module)
        }
    }
}

fn erase_item(ctxt: &Ctxt, mctxt: &mut MCtxt, item: &Item) -> Vec<P<Item>> {
    let kind = match &item.kind {
        ItemKind::ExternCrate(_) => item.kind.clone(),
        ItemKind::Use(_) => item.kind.clone(),
        ItemKind::Mod(unsafety, kind) => ItemKind::Mod(*unsafety, erase_mod(ctxt, mctxt, kind)),
        ItemKind::ForeignMod { .. } => item.kind.clone(),
        ItemKind::Struct(_, _) => {
            // TODO:
            // We don't yet have ghost structs or ghost fields.
            // When we do, we will need to erase them here.
            item.kind.clone()
        }
        ItemKind::Fn(kind) => {
            let vattrs = get_verifier_attrs(&item.attrs).expect("get_verifier_attrs");
            if vattrs.external {
                return vec![P(item.clone())];
            }
            match erase_fn(ctxt, mctxt, kind) {
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

fn erase_crate(ctxt: &Ctxt, mctxt: &mut MCtxt, krate: &Crate) -> Crate {
    let Crate { attrs, items, span, proc_macros } = krate;
    unsupported_unless!(proc_macros.len() == 0, "procedural macros", proc_macros);
    let mut new_items: Vec<P<Item>> = Vec::new();
    for item in items {
        new_items.extend(erase_item(ctxt, mctxt, item));
    }
    Crate { items: new_items, attrs: attrs.clone(), span: *span, proc_macros: proc_macros.clone() }
}

fn mk_ctxt(erasure_hints: &ErasureHints, keep_proofs: bool) -> Ctxt {
    let mut functions = HashMap::new();
    let mut functions_by_span = HashMap::new();
    let mut calls: HashMap<Span, ResolvedCall> = HashMap::new();
    for f in &erasure_hints.vir_crate.functions {
        functions.insert(f.x.path.clone(), Some(f.clone()));
        functions_by_span.insert(from_raw_span(&f.span.raw_span), f.clone());
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
        functions_by_span,
        calls,
        condition_modes,
        var_modes,
        keep_proofs,
        arbitrary_counter: Cell::new(0),
    }
}

#[derive(Clone)]
pub struct CompilerCallbacks {
    pub erasure_hints: ErasureHints,
    pub lifetimes_only: bool,
}

/// Implement the callback from Rust that rewrites the AST
/// (Rust will call rewrite_crate just before transforming AST into HIR).
impl rustc_lint::FormalVerifierRewrite for CompilerCallbacks {
    fn rewrite_crate(
        &mut self,
        krate: &rustc_ast::ast::Crate,
        next_node_id: &mut dyn FnMut() -> NodeId,
    ) -> rustc_ast::ast::Crate {
        let ctxt = mk_ctxt(&self.erasure_hints, self.lifetimes_only);
        let mut mctxt = MCtxt { f_next_node_id: next_node_id };
        crate::erase::erase_crate(&ctxt, &mut mctxt, krate)
    }
}

impl rustc_driver::Callbacks for CompilerCallbacks {
    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let _ = {
            // Install the rewrite_crate callback so that Rust will later call us back on the AST
            let registration = queries.register_plugins().expect("register_plugins");
            let peeked = registration.peek();
            let lint_store = &peeked.1;
            lint_store.formal_verifier_callback.replace(Some(Box::new(self.clone())));
        };
        if self.lifetimes_only {
            crate::lifetime::check(queries);
            rustc_driver::Compilation::Stop
        } else {
            rustc_driver::Compilation::Continue
        }
    }
}
