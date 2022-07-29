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
//! on #[proof] variables.  In this run, we erase #[spec] but not #[proof] and #[exec],
//! then we run mir_borrowck, then we stop and throw away the results.
//!
//! Summary of three runs:
//! 1) AST -> HIR -> VIR for verification on #[exec], #[proof], #[spec]
//! 2) AST -> HIR -> VIR -> MIR for mir_borrowck on #[exec], #[proof]
//! 3) AST -> HIR -> VIR -> MIR -> ... for compilation of #[exec]
//!
//! Notes:
//!
//! #[verifier(external)] functions are kept verbatim.
//! #[verifier(external_body)] functions, on the other hand, need erasure to remove requires/ensures.

use crate::attributes::{get_mode, get_verifier_attrs};
use crate::rust_to_vir_expr::attrs_is_invariant_block;
use crate::unsupported;
use crate::util::{from_raw_span, vec_map};

use rustc_ast::ast::{
    AngleBracketedArg, AngleBracketedArgs, Arm, AssocItem, AssocItemKind, BinOpKind, Block, Crate,
    EnumDef, Expr, ExprField, ExprKind, FieldDef, FnDecl, FnRetTy, FnSig, GenericArg, GenericArgs,
    GenericParam, GenericParamKind, Generics, Impl, Item, ItemKind, Lit, LitIntType, LitKind,
    Local, LocalKind, ModKind, NodeId, Param, Pat, PatField, PatKind, PathSegment, Stmt, StmtKind,
    StructExpr, StructRest, Trait, Ty, TyKind, Variant, VariantData,
};
use rustc_ast::ptr::P;
use rustc_data_structures::thin_vec::ThinVec;
use rustc_interface::interface::Compiler;
use rustc_span::symbol::{Ident, Symbol};
use rustc_span::{Span, SpanData};

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use vir::ast::{
    Datatype, ExprX, FieldOpr, Fun, Function, GenericBoundX, Krate, Mode, Path, Pattern, PatternX,
    UnaryOpr,
};
use vir::ast_util::get_field;
use vir::modes::{mode_join, ErasureModes};

/// Information about each call in the AST (each ExprKind::Call).
#[derive(Clone, Debug)]
pub enum ResolvedCall {
    /// The call is to a spec or proof function, and should be erased
    Spec,
    /// The call is to an operator like == or + that should be compiled.
    CompilableOperator,
    /// The call is to a function, and we record the resolved name of the function here.
    Call(Fun),
    /// Path and variant of datatype constructor
    Ctor(Path, vir::ast::Ident),
}

#[derive(Clone)]
pub struct ErasureHints {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    pub vir_crate: Krate,
    /// Details of each call in the first run's HIR
    pub resolved_calls: Vec<(SpanData, ResolvedCall)>,
    /// Details of some expressions in first run's HIR
    pub resolved_exprs: Vec<(SpanData, vir::ast::Expr)>,
    /// Details of some patterns in first run's HIR
    pub resolved_pats: Vec<(SpanData, Pattern)>,
    /// Results of mode (spec/proof/exec) inference from first run's VIR
    pub erasure_modes: ErasureModes,
    /// List of #[verifier(external)] functions.  (These don't appear in vir_crate,
    /// so we need to record them separately here.)
    pub external_functions: Vec<Fun>,
    /// List of function spans ignored by the verifier. These should not be erased
    pub ignored_functions: Vec<SpanData>,
}

#[derive(Clone)]
pub struct Ctxt {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    _vir_crate: Krate,
    /// Map each function path to its VIR Function, or to None if it is a #[verifier(external)]
    /// function
    functions: HashMap<Fun, Option<Function>>,
    /// Map each datatype path to its VIR Datatype
    datatypes: HashMap<Path, Datatype>,
    /// Map each function span to its VIR Function, excluding #[verifier(external)] functions.
    /// Spans of functions ignored by the verifier map to None.
    functions_by_span: HashMap<Span, Option<Function>>,
    /// Details of each call in the first run's HIR
    calls: HashMap<Span, ResolvedCall>,
    /// Details of some expressions in first run's HIR
    resolved_exprs: HashMap<Span, vir::ast::Expr>,
    /// Details of some patterns in first run's HIR
    resolved_pats: HashMap<Span, Pattern>,
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
    // Allocate a fresh NodeId
    f_next_node_id: &'a mut dyn FnMut() -> NodeId,
    // Unfortunately for us, Rust likes to include surrounding parentheses in an
    // expression's span in HIR, but not in Rust AST.
    // For an expression "((5))", the span is like "((5))" in HIR and like "5" in AST.
    // Keep a mapping from "5" to "(5)" to "((5))" so we can correct for this.
    remap_parens: HashMap<Span, Span>,
    // Mode of current function's return value
    ret_mode: Option<Mode>,
    external_body: bool,
}

impl<'a> MCtxt<'a> {
    fn next_node_id(&mut self) -> NodeId {
        (self.f_next_node_id)()
    }

    fn find_span_opt<'m, A>(&self, map: &'m HashMap<Span, A>, mut span: Span) -> Option<&'m A> {
        loop {
            if let Some(a) = map.get(&span) {
                return Some(a);
            }
            if let Some(s) = self.remap_parens.get(&span) {
                span = *s;
            } else {
                return None;
            }
        }
    }

    fn find_span<'m, A>(&self, map: &'m HashMap<Span, A>, span: Span) -> &'m A {
        if let Some(a) = self.find_span_opt(map, span) {
            a
        } else {
            panic!("internal error: could not find span {:#?}", span);
        }
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

fn phantom_data_segments(mctxt: &mut MCtxt, span: Span) -> Vec<PathSegment> {
    let phantom_data = Symbol::intern("PhantomData");
    let syms = vec![rustc_span::sym::std, rustc_span::sym::marker, phantom_data];
    syms.into_iter()
        .map(|s| PathSegment { ident: Ident::new(s, span), id: mctxt.next_node_id(), args: None })
        .collect()
}

fn phantom_data_expr(mctxt: &mut MCtxt, span: Span) -> Expr {
    let segments = phantom_data_segments(mctxt, span);
    let path = rustc_ast::Path { span, segments, tokens: None };
    let kind = ExprKind::Path(None, path);
    let id = mctxt.next_node_id();
    Expr { id, kind, span, attrs: ThinVec::new(), tokens: None }
}

fn keep_mode(ctxt: &Ctxt, mode: Mode) -> bool {
    match mode {
        Mode::Spec => false,
        Mode::Proof => ctxt.keep_proofs,
        Mode::Exec => true,
    }
}

fn update_item<K>(item: &Item<K>, kind: K) -> Item<K> {
    let Item { id, span, ident, .. } = *item; // for asymptotic efficiency, don't call item.clone()
    let Item { vis, attrs, tokens, .. } = item;
    Item { id, span, ident, kind, vis: vis.clone(), attrs: attrs.clone(), tokens: tokens.clone() }
}

/// Replace expr with e1; e2; ...; en, simplifying if possible
fn replace_with_exprs_span(
    mctxt: &mut MCtxt,
    span: Span,
    expr: Option<&Expr>,
    exprs: Vec<Option<Expr>>,
) -> Option<Expr> {
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
        let rules = rustc_ast::BlockCheckMode::Default;
        let id = mctxt.next_node_id();
        let block = Block { stmts, id, rules, span, tokens: None, could_be_bare_literal: false };
        let kind = ExprKind::Block(P(block), None);
        match expr {
            None => {
                let id = mctxt.next_node_id();
                Some(Expr { id, kind, span, attrs: ThinVec::new(), tokens: None })
            }
            Some(expr) => Some(Expr {
                id: expr.id,
                kind,
                span,
                attrs: expr.attrs.clone(),
                tokens: expr.tokens.clone(),
            }),
        }
    }
}

fn replace_with_exprs(mctxt: &mut MCtxt, expr: &Expr, exprs: Vec<Option<Expr>>) -> Option<Expr> {
    replace_with_exprs_span(mctxt, expr.span, Some(expr), exprs)
}

fn erase_field_pat(ctxt: &Ctxt, mctxt: &mut MCtxt, fpat: &PatField) -> PatField {
    let PatField { ident, is_shorthand, id, span, is_placeholder, .. } = *fpat;
    let pat = P(erase_pat(ctxt, mctxt, &fpat.pat));
    PatField { ident, pat, is_shorthand, attrs: fpat.attrs.clone(), id, span, is_placeholder }
}

fn erase_pat(ctxt: &Ctxt, mctxt: &mut MCtxt, pat: &Pat) -> Pat {
    let kind = match &pat.kind {
        PatKind::Wild => return pat.clone(),
        PatKind::Ident(_, _, None) => return pat.clone(),
        PatKind::Struct(qself, path, fields, recovered) => match &ctxt.resolved_pats[&pat.span].x {
            PatternX::Constructor(vir_path, variant, _) => {
                let datatype = &ctxt.datatypes[vir_path];
                let variant = &datatype.x.get_variant(variant).a;
                let mut fpats: Vec<PatField> = Vec::new();
                for fpat in fields {
                    let name = Arc::new(fpat.ident.as_str().to_string());
                    let (_, mode, _) = get_field(variant, &name).a;
                    let p = if keep_mode(ctxt, mode) {
                        erase_field_pat(ctxt, mctxt, fpat)
                    } else {
                        let mut p = fpat.clone();
                        p.pat.kind = PatKind::Wild;
                        p
                    };
                    fpats.push(p);
                }
                PatKind::Struct(qself.clone(), path.clone(), fpats, *recovered)
            }
            _ => panic!("internal error: expected PatternX::Constructor"),
        },
        PatKind::TupleStruct(qself, path, pats0) => match &ctxt.resolved_pats[&pat.span].x {
            PatternX::Constructor(vir_path, variant, _) => {
                let datatype = &ctxt.datatypes[vir_path];
                let variant = &datatype.x.get_variant(variant).a;
                let mut pats: Vec<P<Pat>> = Vec::new();
                for (field, pat) in variant.iter().zip(pats0.iter()) {
                    let (_, mode, _) = field.a;
                    let p = if keep_mode(ctxt, mode) {
                        erase_pat(ctxt, mctxt, pat)
                    } else {
                        Pat { kind: PatKind::Wild, ..(**pat).clone() }
                    };
                    pats.push(P(p));
                }
                PatKind::TupleStruct(qself.clone(), path.clone(), pats)
            }
            _ => panic!("internal error: expected PatternX::Constructor"),
        },
        PatKind::Path(..) => return pat.clone(),
        PatKind::Tuple(pats) => {
            let pats = vec_map(pats, |p| P(erase_pat(ctxt, mctxt, p)));
            PatKind::Tuple(pats)
        }
        PatKind::Paren(pat) => PatKind::Paren(P(erase_pat(ctxt, mctxt, pat))),
        _ => panic!("internal error: unsupported pattern"),
    };
    let Pat { id, span, .. } = *pat; // for asymptotic efficiency, don't call pat.clone()
    Pat { id, kind, span, tokens: pat.tokens.clone() }
}

fn erase_arm(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, arm: &Arm) -> Arm {
    let pat = P(erase_pat(ctxt, mctxt, &*arm.pat));
    let guard = arm.guard.as_ref().map(|e| P(erase_expr(ctxt, mctxt, expect, e)));
    let body = P(erase_expr(ctxt, mctxt, expect, &*arm.body));
    // for asymptotic efficiency, don't call arm.clone()
    let Arm { span, id, is_placeholder, .. } = *arm;
    let Arm { attrs, .. } = arm;
    Arm { attrs: attrs.clone(), pat, guard, body, span, id, is_placeholder }
}

fn erase_call(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    segment: &PathSegment,
    f_name: &Fun,
    args: &Vec<P<Expr>>,
) -> Option<Option<(PathSegment, Vec<P<Expr>>)>> {
    // TODO this is a temporary diagnostic until the erasure code is refactored
    if !ctxt.functions.contains_key(f_name) {
        let f_name = vir::ast_util::path_as_rust_name(&f_name.path);
        panic!(
            "function {} is unknown to erasure; possibly an uncaught mode-checking error",
            f_name
        );
    }
    let f = &ctxt.functions[f_name];
    if let Some(f) = f {
        let mut segment = segment.clone();
        if let Some(args) = &segment.args {
            match &**args {
                GenericArgs::AngleBracketed(args) => {
                    let mut new_args: Vec<AngleBracketedArg> = Vec::new();
                    let mut typ_bounds_iter = f.x.typ_bounds.iter();
                    for arg in args.args.iter() {
                        match arg {
                            AngleBracketedArg::Arg(GenericArg::Type(_)) => {
                                let (_, bounds) =
                                    typ_bounds_iter.next().expect("missing typ_bound");
                                match &**bounds {
                                    GenericBoundX::Traits(_) => new_args.push(arg.clone()),
                                    GenericBoundX::FnSpec(..) => {}
                                }
                            }
                            AngleBracketedArg::Arg(GenericArg::Lifetime(_)) => {
                                new_args.push(arg.clone());
                            }
                            _ => {}
                        }
                    }
                    let args = AngleBracketedArgs { span: args.span, args: new_args };
                    segment.args = Some(P(GenericArgs::AngleBracketed(args)));
                }
                GenericArgs::Parenthesized(_) => {
                    unsupported!("parenthesized generic arguments");
                }
            }
        }
        if keep_mode(ctxt, f.x.mode) {
            let mut new_args: Vec<P<Expr>> = Vec::new();
            for (arg, param) in args.iter().zip(f.x.params.iter()) {
                if keep_mode(ctxt, param.x.mode) {
                    new_args.push(P(erase_expr(ctxt, mctxt, param.x.mode, arg)));
                }
            }
            Some(Some((segment, new_args)))
        } else {
            Some(None)
        }
    } else {
        None
    }
}

fn erase_expr(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, expr: &Expr) -> Expr {
    erase_expr_opt(ctxt, mctxt, expect, expr)
        .unwrap_or_else(|| panic!("internal error: expected Some(Expr) {:?}", &expr.span))
}

/// Erase ghost code from expr, and return Some resulting expression.
/// If the entire expression is ghost, return None.
fn erase_expr_opt(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, expr: &Expr) -> Option<Expr> {
    if mctxt.external_body {
        match &expr.kind {
            ExprKind::Block(..) => {}
            ExprKind::Call(f_expr, _) => match mctxt.find_span_opt(&ctxt.calls, f_expr.span) {
                Some(ResolvedCall::Spec) => return None,
                _ => return Some(expr.clone()),
            },
            _ => return Some(expr.clone()),
        }
    }

    let kind = match &expr.kind {
        ExprKind::Lit(_) => {
            if keep_mode(ctxt, expect) {
                expr.kind.clone()
            } else {
                return None;
            }
        }
        ExprKind::Path(_, _) => {
            if keep_mode(ctxt, expect) {
                if mctxt.find_span_opt(&ctxt.calls, expr.span).is_some() {
                    // 0-argument datatype constructor
                    expr.kind.clone()
                } else if keep_mode(ctxt, *mctxt.find_span(&ctxt.var_modes, expr.span)) {
                    expr.kind.clone()
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
        ExprKind::Paren(e) => {
            mctxt.remap_parens.insert(e.span, expr.span).map(|_| panic!("{:?}", e.span));
            match erase_expr_opt(ctxt, mctxt, expect, e) {
                None => return None,
                Some(e) => ExprKind::Paren(P(e)),
            }
        }
        ExprKind::Cast(e1, ty) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                ExprKind::Cast(P(e1), ty.clone())
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        ExprKind::AddrOf(borrow, mutability, e1) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                ExprKind::AddrOf(*borrow, *mutability, P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        ExprKind::Box(e1) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                ExprKind::Box(P(e1))
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
        ExprKind::AssignOp(
            op @ rustc_span::source_map::Spanned { node: BinOpKind::Shr, .. },
            e1,
            e2,
        ) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                let e2 = erase_expr(ctxt, mctxt, expect, e2);
                ExprKind::AssignOp(*op, P(e1), P(e2))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1);
                let e2 = erase_expr_opt(ctxt, mctxt, expect, e2);
                return replace_with_exprs(mctxt, expr, vec![e1, e2]);
            }
        }
        ExprKind::Assign(e1, e2, span) => {
            let e1_var_span = match &e1.kind {
                rustc_ast::ExprKind::Unary(rustc_ast::UnOp::Deref, e) => e.span,
                _ => e1.span,
            };
            let mode1 = *mctxt.find_span(&ctxt.var_modes, e1_var_span);
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
            let (qself, path, call) = match &f_expr.kind {
                ExprKind::Path(qself, path)
                    if mctxt.find_span_opt(&ctxt.calls, f_expr.span).is_some() =>
                {
                    (qself, path, mctxt.find_span(&ctxt.calls, f_expr.span).clone())
                }
                ExprKind::Path(..) => panic!("internal error: missing function: {:?}", f_expr.span),
                _ => {
                    unsupported!("complex function call", f_expr)
                }
            };
            match &call {
                ResolvedCall::Spec => return None,
                ResolvedCall::CompilableOperator => {
                    if keep_mode(ctxt, expect) {
                        ExprKind::Call(
                            f_expr.clone(),
                            vec_map(args, |e| P(erase_expr(ctxt, mctxt, expect, e))),
                        )
                    } else {
                        return None;
                    }
                }
                ResolvedCall::Call(f_name) => {
                    let segment = path.segments.last().expect("path with segments");
                    match erase_call(ctxt, mctxt, segment, f_name, args) {
                        None => return Some(expr.clone()),
                        Some(None) => return None,
                        Some(Some((segment, args))) => {
                            let mut path = path.clone();
                            *path.segments.last_mut().unwrap() = segment;
                            let kind = ExprKind::Path(qself.clone(), path);
                            let f_expr = P(Expr { kind, ..(**f_expr).clone() });
                            ExprKind::Call(f_expr, args)
                        }
                    }
                }
                ResolvedCall::Ctor(path, variant) => {
                    if keep_mode(ctxt, expect) {
                        let datatype = &ctxt.datatypes[path];
                        let mut new_args: Vec<P<Expr>> = Vec::new();
                        let variant = datatype.x.get_variant(variant);
                        for (field, arg) in variant.a.iter().zip(args.iter()) {
                            let (_, field_mode, _) = field.a;
                            let e = if keep_mode(ctxt, field_mode) {
                                erase_expr(ctxt, mctxt, mode_join(expect, field_mode), &arg)
                            } else {
                                phantom_data_expr(mctxt, arg.span)
                            };
                            new_args.push(P(e));
                        }
                        ExprKind::Call(f_expr.clone(), new_args)
                    } else {
                        return None;
                    }
                }
            }
        }
        ExprKind::MethodCall(m_path, args, span) => {
            let call = mctxt.find_span(&ctxt.calls, *span).clone();
            match &call {
                ResolvedCall::Call(f_path) => match erase_call(ctxt, mctxt, m_path, f_path, args) {
                    None => return Some(expr.clone()),
                    Some(None) => return None,
                    Some(Some((segment, args))) => {
                        if args.len() == 0 {
                            return None;
                        } else {
                            ExprKind::MethodCall(segment, args, *span)
                        }
                    }
                },
                ResolvedCall::Spec => return None,
                ResolvedCall::CompilableOperator => {
                    if keep_mode(ctxt, expect) {
                        ExprKind::MethodCall(
                            m_path.clone(),
                            vec_map(args, |e| P(erase_expr(ctxt, mctxt, expect, e))),
                            span.clone(),
                        )
                    } else {
                        return None;
                    }
                }
                _ => panic!("internal error: MethodCall ResolvedCall {:?}", call),
            }
        }
        ExprKind::Tup(exprs) => {
            if keep_mode(ctxt, expect) {
                ExprKind::Tup(vec_map(exprs, |e| P(erase_expr(ctxt, mctxt, expect, e))))
            } else {
                let exprs = vec_map(exprs, |e| erase_expr_opt(ctxt, mctxt, expect, e));
                return replace_with_exprs(mctxt, expr, exprs);
            }
        }
        ExprKind::Struct(strct) => {
            let StructExpr { qself, path, fields, rest } = &**strct;
            if keep_mode(ctxt, expect) {
                let rest = match rest {
                    StructRest::None | StructRest::Rest(_) => rest.clone(),
                    StructRest::Base(e) => StructRest::Base(P(erase_expr(ctxt, mctxt, expect, e))),
                };
                let (vir_path, variant) = match mctxt.find_span(&ctxt.calls, expr.span) {
                    ResolvedCall::Ctor(path, variant) => (path, variant),
                    _ => panic!("internal error: expected Ctor"),
                };
                let datatype = &ctxt.datatypes[vir_path];
                let mut new_fields: Vec<ExprField> = Vec::new();
                let variant = datatype.x.get_variant(variant);
                for field in fields {
                    let name = Arc::new(field.ident.as_str().to_string());
                    let (_, field_mode, _) = get_field(&variant.a, &name).a;
                    let e = if keep_mode(ctxt, field_mode) {
                        erase_expr(ctxt, mctxt, mode_join(expect, field_mode), &field.expr)
                    } else {
                        phantom_data_expr(mctxt, field.span)
                    };
                    // for asymptotic efficiency, don't call field.clone():
                    let ExprField {
                        id, span, ident, is_shorthand, is_placeholder, ref attrs, ..
                    } = *field;
                    let field = ExprField {
                        attrs: attrs.clone(),
                        id,
                        span,
                        ident,
                        expr: P(e),
                        is_shorthand,
                        is_placeholder,
                    };
                    new_fields.push(field);
                }
                // TODO: instantiate any type parameters left unused after erasure
                ExprKind::Struct(P(StructExpr {
                    qself: qself.clone(),
                    path: path.clone(),
                    fields: new_fields,
                    rest,
                }))
            } else {
                let mut exprs = vec_map(fields, |f| erase_expr_opt(ctxt, mctxt, expect, &f.expr));
                match rest {
                    StructRest::None | StructRest::Rest(_) => {}
                    StructRest::Base(e) => exprs.push(erase_expr_opt(ctxt, mctxt, expect, e)),
                }
                return replace_with_exprs(mctxt, expr, exprs);
            }
        }
        ExprKind::Field(e1, field) => {
            let field_mode = match &mctxt.find_span(&ctxt.resolved_exprs, expr.span).x {
                ExprX::UnaryOpr(UnaryOpr::Field(FieldOpr { datatype, variant, field }), _) => {
                    let datatype = &ctxt.datatypes[datatype];
                    let variant = datatype.x.get_variant(variant);
                    get_field(&variant.a, field).a.1
                }
                ExprX::UnaryOpr(UnaryOpr::TupleField { .. }, _) => Mode::Exec,
                _ => panic!("internal error: expected Field"),
            };
            if keep_mode(ctxt, field_mode) && keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1);
                ExprKind::Field(P(e1), field.clone())
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        ExprKind::Closure(..) => return None,
        ExprKind::If(eb, e1, e2_opt) => {
            let modeb = *mctxt.find_span(&ctxt.condition_modes, expr.span);
            let eb_erase = match &eb.kind {
                ExprKind::Let(pat, eb1, _span) => {
                    let eb1 = erase_expr_opt(ctxt, mctxt, modeb, eb1);
                    if let Some(eb1) = eb1 {
                        let pat = erase_pat(ctxt, mctxt, pat);
                        let Expr { id, span, .. } = **eb; // for asymptotic efficiency, don't call eb.clone()
                        let kind = ExprKind::Let(P(pat), P(eb1), span);
                        let attrs = eb.attrs.clone();
                        Some(Expr { id, kind, span, attrs, tokens: eb.tokens.clone() })
                    } else {
                        None
                    }
                }
                _ => erase_expr_opt(ctxt, mctxt, modeb, eb),
            };
            let keep = |mctxt: &mut MCtxt, eb| {
                let e1 = erase_block(ctxt, mctxt, expect, e1);
                let e2_opt = e2_opt.as_ref().map(|e2| P(erase_expr(ctxt, mctxt, expect, e2)));
                ExprKind::If(P(eb), P(e1), e2_opt)
            };
            if modeb == Mode::Exec {
                let eb = eb_erase.expect("erase_expr");
                keep(mctxt, eb)
            } else {
                assert!(expect != Mode::Exec);
                if !ctxt.keep_proofs {
                    return eb_erase;
                } else if ctxt.keep_proofs && modeb == Mode::Spec || eb_erase.is_none() {
                    // We erase eb, so we have no bool for the If.
                    // Create a nondeterministic boolean to take eb's place.
                    let e_nondet = call_arbitrary(ctxt, mctxt, expr.span);
                    let eb = replace_with_exprs_span(
                        mctxt,
                        expr.span,
                        None,
                        vec![eb_erase, Some(e_nondet)],
                    );
                    keep(mctxt, eb.expect("e_nondet"))
                } else {
                    let eb = eb_erase.expect("erase_expr");
                    keep(mctxt, eb)
                }
            }
        }
        ExprKind::Match(e0, arms0) => {
            let mode0 = *mctxt.find_span(&ctxt.condition_modes, expr.span);
            let keep = |mctxt: &mut MCtxt, e0| {
                let arms = vec_map(&arms0, |arm| erase_arm(ctxt, mctxt, expect, arm));
                ExprKind::Match(P(e0), arms)
            };
            if mode0 == Mode::Exec {
                let e0 = erase_expr(ctxt, mctxt, mode0, e0);
                keep(mctxt, e0)
            } else {
                assert!(expect != Mode::Exec);
                if !ctxt.keep_proofs {
                    return erase_expr_opt(ctxt, mctxt, mode0, e0);
                } else if ctxt.keep_proofs && mode0 == Mode::Spec {
                    let e0_erase = erase_expr_opt(ctxt, mctxt, mode0, e0);
                    // We erase e0, so we have no value to match on.
                    // Create nondeterministic booleans to take e0's place
                    // and a series of if/else to replace the match.
                    // if non_det1 e1 else if non_det2 e2 else ... else en
                    let mut if_else: Option<Expr> = None;
                    assert!(arms0.len() > 0); // already enforced by mode checker
                    for i in (0..arms0.len()).rev() {
                        // Turn arms0[i].body into block
                        let arm = &arms0[i];
                        let span = expr.span;
                        let stmts = erase_expr_opt(ctxt, mctxt, expect, &arm.body)
                            .map(|body| {
                                let kind = StmtKind::Expr(P(body));
                                let id = mctxt.next_node_id();
                                Stmt { id, kind, span }
                            })
                            .into_iter()
                            .collect();
                        let id = mctxt.next_node_id();
                        let rules = rustc_ast::BlockCheckMode::Default;
                        let block = Block {
                            stmts,
                            id,
                            rules,
                            span,
                            tokens: None,
                            could_be_bare_literal: false,
                        };
                        // Create if/else
                        let kind = if i == arms0.len() - 1 {
                            ExprKind::Block(P(block), None)
                        } else {
                            let e_nondet = call_arbitrary(ctxt, mctxt, expr.span);
                            ExprKind::If(P(e_nondet), P(block), Some(P(if_else.unwrap())))
                        };
                        let id = mctxt.next_node_id();
                        let e = Expr { id, kind, span, attrs: ThinVec::new(), tokens: None };
                        if_else = Some(e);
                    }
                    return replace_with_exprs(mctxt, expr, vec![e0_erase, if_else]);
                } else {
                    let e0 = erase_expr(ctxt, mctxt, mode0, e0);
                    keep(mctxt, e0)
                }
            }
        }
        ExprKind::Loop(block, None) => {
            // The mode checker only allows loops for Mode::Exec
            let block = erase_block(ctxt, mctxt, Mode::Exec, block);
            ExprKind::Loop(P(block), None)
        }
        ExprKind::While(eb, block, None) => {
            // The mode checker only allows loops for Mode::Exec
            let eb = erase_expr(ctxt, mctxt, Mode::Exec, eb);
            let block = erase_block(ctxt, mctxt, Mode::Exec, block);
            ExprKind::While(P(eb), P(block), None)
        }
        ExprKind::Ret(None) => ExprKind::Ret(None),
        ExprKind::Ret(Some(e1)) => {
            let e1 = erase_expr_opt(ctxt, mctxt, mctxt.ret_mode.expect("erase: ret_mode"), e1);
            ExprKind::Ret(e1.map(|e1| P(e1)))
        }
        ExprKind::Block(block, None) => {
            let is_inv_block = attrs_is_invariant_block(&expr.attrs).expect("attrs fail");
            if is_inv_block {
                ExprKind::Block(P(erase_inv_block(ctxt, mctxt, expect, block)), None)
            } else {
                ExprKind::Block(P(erase_block(ctxt, mctxt, expect, block)), None)
            }
        }
        _ => {
            unsupported!("unsupported expr", expr)
        }
    };
    let Expr { id, span, .. } = *expr; // for asymptotic efficiency, don't call expr.clone()
    Some(Expr { id, kind, span, attrs: expr.attrs.clone(), tokens: expr.tokens.clone() })
}

/// Erase ghost code from stmt, and return Some resulting statement.
/// If the entire statment is ghost, return None.
fn erase_stmt(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    expect: Mode,
    stmt: &Stmt,
    is_last: bool,
) -> Option<Stmt> {
    if mctxt.external_body {
        match &stmt.kind {
            StmtKind::Expr(..) | StmtKind::Semi(..) => {}
            _ => return Some(stmt.clone()),
        }
    }

    let kind = match &stmt.kind {
        StmtKind::Local(local) => {
            let mode1 = *mctxt.find_span(&ctxt.var_modes, local.pat.span);
            let Local { id, span, ref ty, ref kind, ref attrs, ref tokens, .. } = **local;
            if keep_mode(ctxt, mode1) {
                let kind = match kind {
                    LocalKind::Decl => LocalKind::Decl,
                    LocalKind::Init(expr) => {
                        LocalKind::Init(P(erase_expr(ctxt, mctxt, mode1, expr)))
                    }
                    LocalKind::InitElse(_, _) => unsupported!("unsupported stmt", stmt),
                };
                let pat = P(erase_pat(ctxt, mctxt, &local.pat));
                let ty = ty.clone();
                let attrs = attrs.clone();
                let tokens = tokens.clone();
                let local = Local { id, pat, ty, kind, span, attrs, tokens };

                Some(StmtKind::Local(P(local)))
            } else {
                match kind {
                    LocalKind::Decl => None,
                    LocalKind::Init(expr) => {
                        erase_expr_opt(ctxt, mctxt, mode1, expr).map(|expr| StmtKind::Semi(P(expr)))
                    }
                    LocalKind::InitElse(_, _) => unsupported!("unsupported stmt", stmt),
                }
            }
        }
        StmtKind::Expr(expr) if is_last => {
            erase_expr_opt(ctxt, mctxt, expect, expr).map(|e| StmtKind::Expr(P(e)))
        }
        StmtKind::Expr(expr) => {
            erase_expr_opt(ctxt, mctxt, Mode::Spec, expr).map(|e| StmtKind::Expr(P(e)))
        }
        StmtKind::Semi(expr) => {
            erase_expr_opt(ctxt, mctxt, Mode::Spec, expr).map(|e| StmtKind::Semi(P(e)))
        }
        StmtKind::Empty => Some(stmt.kind.clone()),
        _ => {
            unsupported!("unsupported stmt", stmt)
        }
    };
    let Stmt { id, span, .. } = *stmt; // for asymptotic efficiency, don't call stmt.clone()
    kind.map(|kind| Stmt { id, kind, span })
}

fn erase_inv_block(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, block: &Block) -> Block {
    if block.stmts.len() != 3 {
        panic!(
            "erase_inv_block: the checks in invariant_block_to_vir should ensure the block has exactly 3 statements"
        );
    }

    let mut result_stmts = Vec::new();

    // First statement:
    //   let (guard, mut ident) = open_atomic_invariant_begin(arg);
    // or
    //   let (guard, mut ident) = open_local_invariant_begin(arg);

    // first, pattern match to get at the arg

    let open_stmt = &block.stmts[0];
    match &open_stmt.kind {
        StmtKind::Local(local) => {
            let init = match &local.kind {
                LocalKind::Decl => panic!(
                    "erase_inv_block: the checks in invariant_block_to_vir should ensure the first statement is an initializer"
                ),
                LocalKind::Init(init) => init,
                LocalKind::InitElse(_, _) => unsupported!("unsupported stmt", open_stmt),
            };
            match &**init {
                Expr { kind: ExprKind::Call(callfn, args), span, id, attrs, tokens } => {
                    let arg = &args[0];
                    let expr_opt = erase_expr_opt(ctxt, mctxt, Mode::Proof, arg);
                    if ctxt.keep_proofs {
                        let expr = expr_opt.expect("erase_inv_block: arg shouldn't be erased");
                        // Reconstruct the call statement with the new expression
                        let kind = StmtKind::Local(P(Local {
                            pat: local.pat.clone(),
                            attrs: local.attrs.clone(),
                            id: local.id,
                            span: local.span.clone(),
                            tokens: local.tokens.clone(),
                            ty: local.ty.clone(),
                            kind: LocalKind::Init(P(Expr {
                                kind: ExprKind::Call(callfn.clone(), vec![P(expr)]),
                                span: span.clone(),
                                id: *id,
                                attrs: attrs.clone(),
                                tokens: tokens.clone(),
                            })),
                        }));
                        let id = open_stmt.id;
                        let span = open_stmt.span.clone();
                        result_stmts.push(Stmt { id, kind, span });
                    } else {
                        match expr_opt {
                            None => {
                                // expr was erased; just erase the whole statement
                            }
                            Some(expr) => {
                                // Erase the open_invariant_begin call, but keep whatever is left of arg
                                let id = open_stmt.id;
                                let span = open_stmt.span.clone();
                                let kind = StmtKind::Semi(P(expr));
                                result_stmts.push(Stmt { id, kind, span });
                            }
                        }
                    }
                }
                _ => {
                    panic!(
                        "erase_inv_block: the checks in invariant_block_to_vir should ensure this match statement succeeds"
                    );
                }
            }
        }
        _ => {
            panic!(
                "erase_inv_block: the checks in invariant_block_to_vir should ensure this match statement succeeds"
            );
        }
    }

    // Middle statement: the user-supplied block
    if let Some(stmt) = erase_stmt(ctxt, mctxt, expect, &block.stmts[1], false) {
        result_stmts.push(stmt);
    }

    // Final statement:
    // open_invariant_end(guard, ident);
    // This is purely proof code. Keep it iff we keep proof-code.
    if ctxt.keep_proofs {
        result_stmts.push(block.stmts[2].clone());
    }

    let Block { id, rules, span, .. } = *block;
    Block {
        stmts: result_stmts,
        id,
        rules,
        span,
        tokens: block.tokens.clone(),
        could_be_bare_literal: false,
    }
}

fn erase_block(ctxt: &Ctxt, mctxt: &mut MCtxt, expect: Mode, block: &Block) -> Block {
    let stmts: Vec<Stmt> = block
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(i, stmt)| erase_stmt(ctxt, mctxt, expect, stmt, i == block.stmts.len() - 1))
        .collect();
    let Block { id, rules, span, .. } = *block; // for asymptotic efficiency, don't call block.clone()
    Block { stmts, id, rules, span, tokens: block.tokens.clone(), could_be_bare_literal: false }
}

fn erase_fn(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    f: &rustc_ast::ast::Fn,
    external_body: bool,
    is_trait: bool,
) -> Option<rustc_ast::ast::Fn> {
    let rustc_ast::ast::Fn { defaultness, sig, generics, body: body_opt } = f;
    let f_vir = if let Some(f_vir) = &ctxt.functions_by_span[&sig.span] {
        f_vir
    } else {
        return Some(f.clone());
    };
    if !keep_mode(ctxt, f_vir.x.mode) {
        return None;
    }
    let Generics { params, where_clause, span: generics_span } = generics;
    let mut new_params: Vec<GenericParam> = Vec::new();

    // Skip over type params in impl<...>
    let mut num_typ_params = 0;
    for param in params.iter() {
        match &param.kind {
            GenericParamKind::Type { .. } => {
                num_typ_params += 1;
            }
            _ => {}
        }
    }
    let n_skip = f_vir.x.typ_bounds.len() - num_typ_params;
    let mut typ_bounds_iter = f_vir.x.typ_bounds.iter().skip(n_skip);

    for param in params.iter() {
        match param.kind {
            GenericParamKind::Lifetime => {
                new_params.push(param.clone());
            }
            GenericParamKind::Type { .. } => {
                let (_, bound) = typ_bounds_iter.next().expect("missing typ_bound");
                // erase Fn trait bounds, since the type checker won't be able to infer them
                // TODO: also erase other type parameters left unused after erasure
                match &**bound {
                    GenericBoundX::Traits(_) => new_params.push(param.clone()),
                    GenericBoundX::FnSpec(..) => {}
                }
            }
            _ => {}
        }
    }
    let generics =
        Generics { params: new_params, where_clause: where_clause.clone(), span: *generics_span };
    let FnSig { header: _, decl, span: _ } = sig;
    let FnDecl { inputs, output } = &**decl;
    let mut new_inputs: Vec<Param> = Vec::new();
    for (input, param) in inputs.iter().zip(f_vir.x.params.iter()) {
        if keep_mode(ctxt, param.x.mode) {
            new_inputs.push(input.clone());
        }
    }
    let ret_mode = f_vir.x.ret.x.mode;
    let output =
        if keep_mode(ctxt, ret_mode) { output.clone() } else { FnRetTy::Default(sig.span) };
    let decl = FnDecl { inputs: new_inputs, output };
    let sig = FnSig { decl: P(decl), ..sig.clone() };
    mctxt.ret_mode = Some(ret_mode);
    mctxt.external_body = external_body;
    let body_opt = if is_trait { &None } else { body_opt };
    let body_opt = body_opt.as_ref().map(|body| P(erase_block(ctxt, mctxt, ret_mode, &**body)));
    mctxt.ret_mode = None;
    mctxt.external_body = false;
    Some(rustc_ast::ast::Fn { defaultness: *defaultness, sig, generics, body: body_opt })
}

fn erase_assoc_item(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    item: &AssocItem,
    is_trait: bool,
) -> Option<AssocItem> {
    match &item.kind {
        AssocItemKind::Fn(f) => {
            let vattrs = get_verifier_attrs(&item.attrs).expect("get_verifier_attrs");
            if vattrs.external {
                return Some(item.clone());
            }
            if vattrs.is_variant.is_some() || vattrs.get_variant.is_some() {
                return None;
            }
            let erased = erase_fn(ctxt, mctxt, f, vattrs.external_body, is_trait);
            erased.map(|f| update_item(item, AssocItemKind::Fn(Box::new(f))))
        }
        AssocItemKind::TyAlias(_) => Some(item.clone()),
        _ => panic!("unsupported AssocItemKind"),
    }
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

fn erase_fields(ctxt: &Ctxt, mctxt: &mut MCtxt, old_fields: &Vec<FieldDef>) -> Vec<FieldDef> {
    let mut fields: Vec<FieldDef> = Vec::new();
    for field in old_fields {
        let mode = get_mode(Mode::Exec, &field.attrs[..]);
        if keep_mode(ctxt, mode) {
            fields.push(field.clone());
        } else {
            // Replace erased field of type t with std::marker::PhantomData<t>
            let span = field.span;
            let mut field = field.clone();
            let arg = GenericArg::Type(field.ty.clone());
            let arg = AngleBracketedArg::Arg(arg);
            let args = AngleBracketedArgs { span, args: vec![arg] };
            let args = GenericArgs::AngleBracketed(args);
            let mut segments = phantom_data_segments(mctxt, span);
            segments.last_mut().unwrap().args = Some(P(args));
            let path = rustc_ast::Path { span, segments, tokens: None };
            let kind = TyKind::Path(None, path);
            let id = mctxt.next_node_id();
            field.ty = P(Ty { id, kind, span, tokens: None });
            fields.push(field.clone());
        }
    }
    fields
}

fn erase_variant_data(ctxt: &Ctxt, mctxt: &mut MCtxt, variant: &VariantData) -> VariantData {
    match variant {
        VariantData::Struct(fields, recovered) => {
            VariantData::Struct(erase_fields(ctxt, mctxt, fields), *recovered)
        }
        VariantData::Tuple(fields, id) => {
            VariantData::Tuple(erase_fields(ctxt, mctxt, fields), *id)
        }
        VariantData::Unit(_) => variant.clone(),
    }
}

fn erase_variant(ctxt: &Ctxt, mctxt: &mut MCtxt, variant: &Variant) -> Variant {
    let Variant { id, span, ident, is_placeholder, .. } = *variant;
    let Variant { attrs, vis, data, disr_expr, .. } = variant;
    let attrs = attrs.clone();
    let vis = vis.clone();
    let data = erase_variant_data(ctxt, mctxt, data);
    let disr_expr = disr_expr.clone();
    Variant { attrs, id, span, vis, ident, data, disr_expr, is_placeholder }
}

fn erase_trait(ctxt: &Ctxt, mctxt: &mut MCtxt, tr: &Trait) -> Box<Trait> {
    let Trait { unsafety, is_auto, .. } = *tr;
    let Trait { generics, bounds, .. } = tr;
    let generics = generics.clone();
    let bounds = bounds.clone();
    let mut items: Vec<P<AssocItem>> = Vec::new();
    for item in &tr.items {
        if let Some(item) = erase_assoc_item(ctxt, mctxt, &item, true) {
            items.push(P(item));
        }
    }
    let tr = Trait { unsafety, is_auto, generics, bounds, items };
    Box::new(tr.clone())
}

fn erase_item(ctxt: &Ctxt, mctxt: &mut MCtxt, item: &Item) -> Vec<P<Item>> {
    let kind = match &item.kind {
        ItemKind::ExternCrate(_) => item.kind.clone(),
        ItemKind::Use(_) => item.kind.clone(),
        ItemKind::Mod(unsafety, kind) => ItemKind::Mod(*unsafety, erase_mod(ctxt, mctxt, kind)),
        ItemKind::ForeignMod { .. } => item.kind.clone(),
        ItemKind::Struct(variant, generics) => {
            ItemKind::Struct(erase_variant_data(ctxt, mctxt, variant), generics.clone())
        }
        ItemKind::Enum(EnumDef { variants }, generics) => {
            let variants = vec_map(&variants, |v| erase_variant(ctxt, mctxt, v));
            ItemKind::Enum(EnumDef { variants }, generics.clone())
        }
        ItemKind::Fn(kind) => {
            let vattrs = get_verifier_attrs(&item.attrs).expect("get_verifier_attrs");
            if vattrs.external {
                return vec![P(item.clone())];
            }
            match erase_fn(ctxt, mctxt, kind, vattrs.external_body, false) {
                None => return vec![],
                Some(kind) => ItemKind::Fn(Box::new(kind)),
            }
        }
        ItemKind::Impl(kind) => {
            let vattrs = get_verifier_attrs(&item.attrs).expect("get_verifier_attrs");
            if vattrs.external {
                ItemKind::Impl(kind.clone())
            } else {
                let mut items: Vec<P<AssocItem>> = Vec::new();
                for item in &kind.items {
                    if let Some(item) = erase_assoc_item(ctxt, mctxt, &item, false) {
                        items.push(P(item));
                    }
                }
                // TODO we may need to erase some generic params
                // for asymptotic efficiency, don't call kind.clone():
                let Impl {
                    unsafety,
                    polarity,
                    defaultness,
                    constness,
                    ref generics,
                    ref of_trait,
                    ref self_ty,
                    ..
                } = **kind;
                let kind = Impl {
                    unsafety,
                    polarity,
                    defaultness,
                    constness,
                    generics: generics.clone(),
                    of_trait: of_trait.clone(),
                    self_ty: self_ty.clone(),
                    items,
                };
                ItemKind::Impl(Box::new(kind))
            }
        }
        ItemKind::Static(..) => item.kind.clone(),
        ItemKind::Const(..) => {
            if let Some(f_vir) = &ctxt.functions_by_span[&item.span] {
                if keep_mode(ctxt, f_vir.x.ret.x.mode) {
                    item.kind.clone()
                } else {
                    return vec![];
                }
            } else {
                item.kind.clone()
            }
        }
        ItemKind::MacroDef(..) => item.kind.clone(),
        ItemKind::TyAlias(..) => item.kind.clone(),
        ItemKind::Trait(tr) => ItemKind::Trait(erase_trait(ctxt, mctxt, tr)),
        ItemKind::GlobalAsm(..) => item.kind.clone(),
        _ => {
            unsupported!("unsupported item", item)
        }
    };
    vec![P(update_item(item, kind))]
}

fn erase_crate(ctxt: &Ctxt, mctxt: &mut MCtxt, krate: &Crate) -> Crate {
    let Crate { attrs, items, span } = krate;
    let mut new_items: Vec<P<Item>> = Vec::new();
    for item in items {
        new_items.extend(erase_item(ctxt, mctxt, item));
    }
    Crate { items: new_items, attrs: attrs.clone(), span: *span }
}

fn mk_ctxt(erasure_hints: &ErasureHints, known_spans: &HashSet<Span>, keep_proofs: bool) -> Ctxt {
    let mut functions = HashMap::new();
    let mut functions_by_span = HashMap::new();
    let mut datatypes = HashMap::new();
    let mut calls: HashMap<Span, ResolvedCall> = HashMap::new();
    let mut resolved_exprs: HashMap<Span, vir::ast::Expr> = HashMap::new();
    let mut resolved_pats: HashMap<Span, Pattern> = HashMap::new();
    for f in &erasure_hints.vir_crate.functions {
        functions.insert(f.x.name.clone(), Some(f.clone())).map(|_| panic!("{:?}", &f.x.name));
        let span = from_raw_span(&f.span.raw_span);
        assert!(known_spans.contains(&span));
        functions_by_span.insert(span, Some(f.clone())).map(|_| panic!("{:?}", &f.span));
    }
    for name in &erasure_hints.external_functions {
        functions.insert(name.clone(), None).map(|_| panic!("{:?}", name));
    }
    for span in &erasure_hints.ignored_functions {
        assert!(known_spans.contains(&span.span()));
        functions_by_span.insert(span.span(), None).map(|v| v.map(|_| panic!("{:?}", span)));
    }
    for d in &erasure_hints.vir_crate.datatypes {
        datatypes.insert(d.x.path.clone(), d.clone()).map(|_| panic!("{:?}", &d.x.path));
    }
    for (span, call) in &erasure_hints.resolved_calls {
        assert!(known_spans.contains(&span.span()));
        calls.insert(span.span(), call.clone()).map(|_| panic!("{:?}", span));
    }
    for (span, expr) in &erasure_hints.resolved_exprs {
        assert!(known_spans.contains(&span.span()));
        resolved_exprs.insert(span.span(), expr.clone()).map(|_| panic!("{:?}", span));
    }
    for (span, expr) in &erasure_hints.resolved_pats {
        assert!(known_spans.contains(&span.span()));
        resolved_pats.insert(span.span(), expr.clone()).map(|_| panic!("{:?}", span));
    }
    let mut condition_modes: HashMap<Span, Mode> = HashMap::new();
    let mut var_modes: HashMap<Span, Mode> = HashMap::new();
    for (span, mode) in &erasure_hints.erasure_modes.condition_modes {
        let span = from_raw_span(&span.raw_span);
        assert!(known_spans.contains(&span));
        condition_modes.insert(span, *mode).map(|_| panic!("{:?}", span));
    }
    for (span, mode) in &erasure_hints.erasure_modes.var_modes {
        let span = from_raw_span(&span.raw_span);
        assert!(known_spans.contains(&span));
        var_modes.insert(span, *mode).map(|v| panic!("{:?} {:?}", span, v));
    }
    Ctxt {
        _vir_crate: erasure_hints.vir_crate.clone(),
        functions,
        functions_by_span,
        datatypes,
        calls,
        resolved_exprs,
        resolved_pats,
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
    pub print: bool,
    pub time_erasure: Arc<Mutex<Duration>>,
}

impl CompilerCallbacks {
    fn maybe_print<'tcx>(
        &self,
        compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) {
        if self.print {
            let krate = &queries.expansion().expect("expansion").peek().0;
            rustc_driver::pretty::print_after_parsing(
                &compiler.session(),
                &compiler.input(),
                krate,
                rustc_session::config::PpMode::Source(rustc_session::config::PpSourceMode::Normal),
                None,
            );
        }
    }
}

/// Implement the callback from Rust that rewrites the AST
/// (Rust will call rewrite_crate just before transforming AST into HIR).
impl rustc_lint::FormalVerifierRewrite for CompilerCallbacks {
    fn rewrite_crate(
        &mut self,
        krate: &rustc_ast::ast::Crate,
        next_node_id: &mut dyn FnMut() -> NodeId,
    ) -> rustc_ast::ast::Crate {
        use crate::rustc_ast::mut_visit::MutVisitor;
        let mut krate = krate.clone();
        let mut visitor = crate::erase_rewrite::Visitor::new();
        visitor.visit_crate(&mut krate);

        let ctxt = mk_ctxt(&self.erasure_hints, &visitor.spans, self.lifetimes_only);
        let mut mctxt = MCtxt {
            f_next_node_id: next_node_id,
            remap_parens: HashMap::new(),
            ret_mode: None,
            external_body: false,
        };
        let time0 = Instant::now();
        let krate = crate::erase::erase_crate(&ctxt, &mut mctxt, &krate);
        let time1 = Instant::now();
        (*self.time_erasure.lock().unwrap()) += time1 - time0;
        krate
    }
}

impl rustc_driver::Callbacks for CompilerCallbacks {
    fn after_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
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
            self.maybe_print(compiler, queries);
            crate::lifetime::check(queries);
            rustc_driver::Compilation::Stop
        } else {
            rustc_driver::Compilation::Continue
        }
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        self.maybe_print(compiler, queries);
        rustc_driver::Compilation::Continue
    }
}
