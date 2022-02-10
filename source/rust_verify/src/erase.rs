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
use crate::context::ExternalBodyErasureInfo;
use crate::rust_to_vir_expr::attrs_is_invariant_block;
use crate::util::{from_raw_span, vec_map};
use crate::{unsupported, unsupported_unless};

use rustc_ast::ast::{
    AngleBracketedArg, AngleBracketedArgs, Arm, AssocItem, AssocItemKind, BinOpKind, Block, Crate,
    EnumDef, Expr, ExprKind, Field, FieldPat, FnDecl, FnKind, FnRetTy, FnSig, GenericArg,
    GenericArgs, GenericParam, GenericParamKind, Generics, ImplKind, Item, ItemKind, Lit,
    LitIntType, LitKind, Local, ModKind, NodeId, Param, Pat, PatKind, PathSegment, Stmt, StmtKind,
    StructField, StructRest, UnOp, Variant, VariantData,
};
use rustc_ast::ptr::P;
use rustc_data_structures::thin_vec::ThinVec;
use rustc_interface::interface::Compiler;
use rustc_span::symbol::{Ident, Symbol};
use rustc_span::{Span, SpanData};

use std::cell::Cell;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use vir::ast::{
    BinaryOp, CallTarget, Datatype, ExprX, Fun, Function, GenericBoundX, Krate, Mode, Path,
    PatternX, StmtX, UnaryOp, UnaryOpr,
};
use vir::ast_util::get_field;
use vir::modes::{mode_join, ErasureModes};

#[derive(Clone)]
pub struct ErasureHints {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    pub vir_crate: Krate,
    /// Results of mode (spec/proof/exec) inference from first run's VIR
    pub erasure_modes: ErasureModes,
    /// List of #[verifier(external)] functions.  (These don't appear in vir_crate,
    /// so we need to record them separately here.)
    pub external_functions: Vec<Fun>,
    /// List of function spans ignored by the verifier. These should not be erased
    pub ignored_functions: Vec<SpanData>,
    /// List of external_body functions. We need to erase their headers.
    pub external_body_functions: Vec<(SpanData, ExternalBodyErasureInfo)>,
}

#[derive(Clone)]
pub struct Ctxt {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    vir_crate: Krate,
    /// Map each function path to its VIR Function, or to None if it is a #[verifier(external)]
    /// function
    functions: HashMap<Fun, Option<Function>>,
    /// Map each datatype path to its VIR Datatype
    datatypes: HashMap<Path, Datatype>,
    /// Map each function span to its VIR Function, excluding #[verifier(external)] functions.
    /// Spans of functions ignored by the verifier map to None.
    functions_by_span: HashMap<Span, Option<Function>>,
    /// Information about erasing an external_body function
    external_body_functions: HashMap<Span, ExternalBodyErasureInfo>,
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
    // Mode of current function's return value
    ret_mode: Option<Mode>,
}

impl<'a> MCtxt<'a> {
    fn next_node_id(&mut self) -> NodeId {
        (self.f_next_node_id)()
    }

    fn find_span_opt<'m, A>(
        &self,
        map: &'m HashMap<Span, A>,
        span: &air::ast::Span,
    ) -> Option<&'m A> {
        let span = from_raw_span(&span.raw_span);
        map.get(&span)
    }

    fn find_span<'m, A>(&self, map: &'m HashMap<Span, A>, span: &air::ast::Span) -> &'m A {
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
        let block = Block { stmts, id, rules, span, tokens: None };
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

fn erase_field_pat(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    fpat: &FieldPat,
    vir_pat: &vir::ast::Pattern,
) -> FieldPat {
    let FieldPat { ident, is_shorthand, id, span, is_placeholder, .. } = *fpat;
    let pat = P(erase_pat(ctxt, mctxt, &fpat.pat, vir_pat));
    FieldPat { ident, pat, is_shorthand, attrs: fpat.attrs.clone(), id, span, is_placeholder }
}

fn erase_pat(ctxt: &Ctxt, mctxt: &mut MCtxt, pat: &Pat, vir_pat: &vir::ast::Pattern) -> Pat {
    let kind = match (&pat.kind, &vir_pat.x) {
        (PatKind::Wild, PatternX::Wildcard) => return pat.clone(),
        (PatKind::Ident(_, _, None), PatternX::Var { .. }) => return pat.clone(),
        (
            PatKind::Struct(path, fields, recovered),
            PatternX::Constructor(vir_path, variant, vir_binders),
        ) => {
            let mut vir_binder_map = HashMap::new();
            for arg in vir_binders.iter() {
                vir_binder_map.insert(arg.name.clone(), &arg.a);
            }

            let datatype = &ctxt.datatypes[vir_path];
            let variant = &datatype.x.get_variant(variant).a;
            let mut fpats: Vec<FieldPat> = Vec::new();
            for fpat in fields {
                let name = Arc::new(fpat.ident.as_str().to_string());
                let (_, mode, _) = get_field(variant, &name).a;
                if keep_mode(ctxt, mode) {
                    let vir_p = vir_binder_map.get(&name).expect("vir_binder_map.get");
                    fpats.push(erase_field_pat(ctxt, mctxt, fpat, vir_p));
                }
            }
            PatKind::Struct(path.clone(), fpats, *recovered)
        }
        (
            PatKind::TupleStruct(path, pats0),
            PatternX::Constructor(vir_path, variant, vir_binders),
        ) => {
            let datatype = &ctxt.datatypes[vir_path];
            let variant = &datatype.x.get_variant(variant).a;
            let mut pats: Vec<P<Pat>> = Vec::new();
            assert!(pats0.len() == vir_binders.len());
            for ((field, pat), vir_binder) in
                variant.iter().zip(pats0.iter()).zip(vir_binders.iter())
            {
                let (_, mode, _) = field.a;
                if keep_mode(ctxt, mode) {
                    pats.push(P(erase_pat(ctxt, mctxt, pat, &vir_binder.a)));
                }
            }
            PatKind::TupleStruct(path.clone(), pats)
        }
        (PatKind::Path(..), PatternX::Constructor(_, _, vir_binders)) => {
            assert!(vir_binders.len() == 0);
            return pat.clone();
        }
        (PatKind::Tuple(pats), PatternX::Tuple(vir_pats)) => {
            assert!(pats.len() == vir_pats.len());
            let pats = pats
                .iter()
                .zip(vir_pats.iter())
                .map(|(p, vir_p)| P(erase_pat(ctxt, mctxt, p, vir_p)))
                .collect();
            PatKind::Tuple(pats)
        }
        (PatKind::Paren(pat), _) => PatKind::Paren(P(erase_pat(ctxt, mctxt, pat, vir_pat))),
        _ => panic!("erase_pat: unable to match:\nRust AST: {:#?}\nVIR: {:#?}\n", pat, vir_pat),
    };
    let Pat { id, span, .. } = *pat; // for asymptotic efficiency, don't call pat.clone()
    Pat { id, kind, span, tokens: pat.tokens.clone() }
}

fn erase_arm(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    expect: Mode,
    arm: &Arm,
    vir_arm: &vir::ast::Arm,
) -> Arm {
    let pat = P(erase_pat(ctxt, mctxt, &*arm.pat, &vir_arm.x.pattern));
    let guard = arm.guard.as_ref().map(|e| P(erase_expr(ctxt, mctxt, expect, e, &vir_arm.x.guard)));
    let body = P(erase_expr(ctxt, mctxt, expect, &*arm.body, &vir_arm.x.body));
    // for asymptotic efficiency, don't call arm.clone()
    let Arm { span, id, is_placeholder, .. } = *arm;
    let Arm { attrs, .. } = arm;
    Arm { attrs: attrs.clone(), pat, guard, body, span, id, is_placeholder }
}

// TODO use an enum instead of Option<Option<...>>
fn erase_call(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    segment: &PathSegment,
    f_name: &Fun,
    args: &Vec<P<Expr>>,
    vir_args: &Vec<vir::ast::Expr>,
) -> Option<Option<(PathSegment, Vec<P<Expr>>)>> {
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
                                    GenericBoundX::None => new_args.push(arg.clone()),
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
            assert!(vir_args.len() == args.len());
            for ((arg, param), vir_arg) in args.iter().zip(f.x.params.iter()).zip(vir_args.iter()) {
                if keep_mode(ctxt, param.x.mode) {
                    new_args.push(P(erase_expr(ctxt, mctxt, param.x.mode, arg, vir_arg)));
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

fn erase_expr(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    expect: Mode,
    expr: &Expr,
    vir_expr: &vir::ast::Expr,
) -> Expr {
    erase_expr_opt(ctxt, mctxt, expect, expr, vir_expr).expect("erase_expr")
}

/// Erase ghost code from expr, and return Some resulting expression.
/// If the entire expression is ghost, return None.
fn erase_expr_opt(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    expect: Mode,
    expr: &Expr,
    vir_expr: &vir::ast::Expr,
) -> Option<Expr> {
    let kind = match (&expr.kind, &vir_expr.x) {
        (ExprKind::Lit(_), ExprX::Const(..)) => {
            if keep_mode(ctxt, expect) {
                expr.kind.clone()
            } else {
                return None;
            }
        }
        (ExprKind::Path(None, path), ExprX::Var(vir_ident))
        | (ExprKind::Path(None, path), ExprX::VarLoc(vir_ident)) => {
            assert!(path.segments.len() == 1);
            assert!(path.segments[0].ident.as_str() == **vir_ident);
            if keep_mode(ctxt, *mctxt.find_span(&ctxt.var_modes, &vir_expr.span))
                && keep_mode(ctxt, expect)
            {
                expr.kind.clone()
            } else {
                return None;
            }
        }
        (ExprKind::Path(_qself, _path), ExprX::ConstVar(_)) => {
            if keep_mode(ctxt, *mctxt.find_span(&ctxt.var_modes, &vir_expr.span))
                && keep_mode(ctxt, expect)
            {
                expr.kind.clone()
            } else {
                return None;
            }
        }
        (ExprKind::Path(_qself, _path), ExprX::Ctor(..)) => {
            // nullary constructor
            // REVIEW: why do we not check the mode here?
            expr.kind.clone()
        }
        (ExprKind::Paren(e), _) => {
            // Paren in Rust AST can be ignored
            return erase_expr_opt(ctxt, mctxt, expect, e, vir_expr);
        }
        (_, ExprX::Loc(vir_expr)) => {
            // Loc in Verus AST can be ignored
            return erase_expr_opt(ctxt, mctxt, expect, expr, vir_expr);
        }
        (_, ExprX::Unary(UnaryOp::Clip(..), vir_expr)) => {
            // Clip in Verus AST can be ignored
            return erase_expr_opt(ctxt, mctxt, expect, expr, vir_expr);
        }
        (ExprKind::Cast(e1, ty), _) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_expr);
                ExprKind::Cast(P(e1), ty.clone())
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_expr);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        (ExprKind::AddrOf(borrow, mutability, e1), _) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_expr);
                ExprKind::AddrOf(*borrow, *mutability, P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_expr);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        (ExprKind::Box(e1), _) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_expr);
                ExprKind::Box(P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_expr);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        (ExprKind::Unary(UnOp::Deref, e1), _) => {
            // REVIEW: is this always the right way to handle Deref?
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_expr);
                ExprKind::Unary(UnOp::Deref, P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_expr);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        (ExprKind::Unary(op, e1), ExprX::Unary(_, vir_e1)) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_e1);
                ExprKind::Unary(*op, P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        (ExprKind::Unary(UnOp::Neg, e1), ExprX::Binary(BinaryOp::Sub, const_zero, vir_e1)) => {
            match &const_zero.x {
                ExprX::Const(vir::ast::Constant::Nat(s)) if **s == "0" => {}
                _ => {
                    panic!("cannot match UnaryOp with BinaryOp");
                }
            }
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_e1);
                ExprKind::Unary(UnOp::Neg, P(e1))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        (ExprKind::Binary(op, e1, e2), ExprX::Binary(_vir_op, vir_e1, vir_e2)) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_e1);
                let e2 = erase_expr(ctxt, mctxt, expect, e2, vir_e2);
                ExprKind::Binary(*op, P(e1), P(e2))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_e1);
                let e2 = erase_expr_opt(ctxt, mctxt, expect, e2, vir_e2);
                return replace_with_exprs(mctxt, expr, vec![e1, e2]);
            }
        }
        (
            ExprKind::AssignOp(
                op @ rustc_span::source_map::Spanned { node: BinOpKind::Shr, .. },
                e1,
                e2,
            ),
            ExprX::Binary(BinaryOp::Implies, vir_e1, vir_e2),
        ) => {
            if keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_e1);
                let e2 = erase_expr(ctxt, mctxt, expect, e2, vir_e2);
                ExprKind::AssignOp(*op, P(e1), P(e2))
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_e1);
                let e2 = erase_expr_opt(ctxt, mctxt, expect, e2, vir_e2);
                return replace_with_exprs(mctxt, expr, vec![e1, e2]);
            }
        }
        (ExprKind::Assign(e1, e2, span), ExprX::Assign(vir_e1, vir_e2)) => {
            let mode1 = *mctxt.find_span(&ctxt.var_modes, &vir_e1.span);
            if keep_mode(ctxt, mode1) {
                let e1 = erase_expr(ctxt, mctxt, mode1, e1, vir_e1);
                let e2 = erase_expr(ctxt, mctxt, mode1, e2, vir_e2);
                ExprKind::Assign(P(e1), P(e2), *span)
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, mode1, e1, vir_e1);
                let e2 = erase_expr_opt(ctxt, mctxt, expect, e2, vir_e2);
                return replace_with_exprs(mctxt, expr, vec![e1, e2]);
            }
        }
        (ExprKind::Call(..), ExprX::Admit) => {
            return None;
        }
        (ExprKind::Call(..), ExprX::AssertBV(..)) => {
            return None;
        }
        (ExprKind::Call(..), ExprX::Choose { .. }) => {
            return None;
        }
        (ExprKind::Call(..), ExprX::Fuel(..)) => {
            return None;
        }
        (ExprKind::Call(..), ExprX::Forall { .. }) => {
            return None;
        }
        (ExprKind::Call(..), ExprX::HeaderStub) => {
            return None;
        }
        (ExprKind::Call(..), ExprX::Quant(..)) => {
            return None;
        }
        (ExprKind::Call(_f_expr, _args), ExprX::Call(CallTarget::FnSpec(..), _vir_args)) => {
            // This case is only supported for 'spec' right now
            return None;
        }
        (
            ExprKind::Call(f_expr, args),
            ExprX::Call(CallTarget::Static(f_name, _typs), vir_args),
        ) => {
            let (qself, path) = match &f_expr.kind {
                ExprKind::Path(qself, path) => (qself, path),
                _ => {
                    unsupported!("complex function call", f_expr)
                }
            };
            let segment = path.segments.last().expect("path with segments");
            match erase_call(ctxt, mctxt, segment, f_name, args, vir_args) {
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
        (ExprKind::Call(f_expr, args), ExprX::Ctor(path, variant, vir_binders, None)) => {
            // This is a tuple-style constructor: args are "0", "1", ...
            assert!(args.len() == vir_binders.len());
            if keep_mode(ctxt, expect) {
                let datatype = &ctxt.datatypes[path];
                let mut new_args: Vec<P<Expr>> = Vec::new();
                let variant = datatype.x.get_variant(variant);
                for ((field, arg), vir_binder) in
                    variant.a.iter().zip(args.iter()).zip(vir_binders.iter())
                {
                    let (_, field_mode, _) = field.a;
                    if keep_mode(ctxt, field_mode) {
                        new_args.push(P(erase_expr(
                            ctxt,
                            mctxt,
                            mode_join(expect, field_mode),
                            &arg,
                            &vir_binder.a,
                        )));
                    }
                }
                // TODO: instantiate any type parameters left unused after erasure
                ExprKind::Call(f_expr.clone(), new_args)
            } else {
                return None;
            }
        }
        (
            ExprKind::MethodCall(m_path, args, span),
            ExprX::Call(CallTarget::Static(f_name, _typs), vir_args),
        ) => match erase_call(ctxt, mctxt, m_path, f_name, args, vir_args) {
            None => return Some(expr.clone()),
            Some(None) => return None,
            Some(Some((segment, args))) => ExprKind::MethodCall(segment, args, *span),
        },
        (ExprKind::Tup(exprs), ExprX::Tuple(vir_exprs)) => {
            assert!(exprs.len() == vir_exprs.len());
            if keep_mode(ctxt, expect) {
                ExprKind::Tup(
                    exprs
                        .iter()
                        .zip(vir_exprs.iter())
                        .map(|(e, vir_e)| P(erase_expr(ctxt, mctxt, expect, e, vir_e)))
                        .collect(),
                )
            } else {
                let exprs = exprs
                    .iter()
                    .zip(vir_exprs.iter())
                    .map(|(e, vir_e)| erase_expr_opt(ctxt, mctxt, expect, e, vir_e))
                    .collect();
                return replace_with_exprs(mctxt, expr, exprs);
            }
        }
        (
            ExprKind::Struct(path, fields, rest),
            ExprX::Ctor(vir_path, variant, vir_binders, vir_rest_opt),
        ) => {
            let mut vir_binder_map = HashMap::new();
            for arg in vir_binders.iter() {
                vir_binder_map.insert(arg.name.clone(), &arg.a);
            }

            if keep_mode(ctxt, expect) {
                let rest = match (rest, vir_rest_opt) {
                    (StructRest::None, None) | (StructRest::Rest(_), None) => rest.clone(),
                    (StructRest::Base(e), Some(vir_rest)) => {
                        StructRest::Base(P(erase_expr(ctxt, mctxt, expect, e, vir_rest)))
                    }
                    _ => panic!("AST and VIR 'rest' doesn't match"),
                };
                let datatype = &ctxt.datatypes[vir_path];
                let mut new_fields: Vec<Field> = Vec::new();
                let variant = datatype.x.get_variant(variant);

                for field in fields {
                    let name = Arc::new(field.ident.as_str().to_string());
                    let (_, field_mode, _) = get_field(&variant.a, &name).a;
                    if keep_mode(ctxt, field_mode) {
                        let vir_e = vir_binder_map.get(&name).expect("vir_binder_map.get");
                        let e = erase_expr(
                            ctxt,
                            mctxt,
                            mode_join(expect, field_mode),
                            &field.expr,
                            vir_e,
                        );
                        // for asymptotic efficiency, don't call field.clone():
                        let Field { attrs, .. } = field;
                        let Field { id, span, ident, is_shorthand, is_placeholder, .. } = *field;
                        let field = Field {
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
                }
                // TODO: instantiate any type parameters left unused after erasure
                ExprKind::Struct(path.clone(), new_fields, rest)
            } else {
                let mut exprs = vec_map(fields, |field| {
                    let name = Arc::new(field.ident.as_str().to_string());
                    let vir_e = vir_binder_map.get(&name).expect("vir_binder_map.get");
                    erase_expr_opt(ctxt, mctxt, expect, &field.expr, vir_e)
                });
                match (rest, vir_rest_opt) {
                    (StructRest::None, None) | (StructRest::Rest(_), None) => {}
                    (StructRest::Base(e), Some(vir_rest)) => {
                        exprs.push(erase_expr_opt(ctxt, mctxt, expect, e, vir_rest))
                    }
                    _ => panic!("AST and VIR 'rest' doesn't match"),
                }
                return replace_with_exprs(mctxt, expr, exprs);
            }
        }
        (ExprKind::Field(e1, field), _) => {
            let (field_mode, vir_e1) = match &vir_expr.x {
                ExprX::UnaryOpr(UnaryOpr::Field { datatype, variant, field }, vir_e1) => {
                    let datatype = &ctxt.datatypes[datatype];
                    let variant = datatype.x.get_variant(variant);
                    (get_field(&variant.a, field).a.1, vir_e1)
                }
                ExprX::UnaryOpr(UnaryOpr::TupleField { .. }, vir_e1) => (Mode::Exec, vir_e1),
                _ => panic!("internal error: expected Field"),
            };
            if keep_mode(ctxt, field_mode) && keep_mode(ctxt, expect) {
                let e1 = erase_expr(ctxt, mctxt, expect, e1, vir_e1);
                ExprKind::Field(P(e1), field.clone())
            } else {
                let e1 = erase_expr_opt(ctxt, mctxt, expect, e1, vir_e1);
                return replace_with_exprs(mctxt, expr, vec![e1]);
            }
        }
        (ExprKind::Closure(..), ExprX::Closure(..)) => return None,
        (ExprKind::If(eb, e1, e2_opt), _) => {
            let modeb = *mctxt.find_span(&ctxt.condition_modes, &vir_expr.span);
            let (eb_erase, vir_e1, vir_e2_opt) = match &eb.kind {
                ExprKind::Let(pat, eb1) => {
                    // An 'if-let' expression de-sugars to a 'match' expression
                    // Rust AST:
                    //    if $pat = $eb1 {
                    //        e1
                    //    } else {
                    //        e2_opt
                    //    }
                    // VIR:
                    //    match $vir_eb {
                    //        $vir_arms[0].pattern => { $vir_arms[0].body }
                    //        _                    => { $vir_arms[1].body }
                    //    }
                    //
                    // Thus:
                    //       `eb1` matches `vir_eb`,
                    //       `pat` matches `vir_arms[0].pattern`
                    //       `e1` matches `vir_arms[0].body`
                    //       `e2_opt` matches `vir_arms[1].body`
                    // If e2_opt=None, then we expect `vir_arms[1].body` to be empty
                    // so we just ignore it in that case.
                    match &vir_expr.x {
                        ExprX::Match(vir_eb, vir_arms) => {
                            assert!(vir_arms.len() == 2);
                            let vir_e1 = vir_arms[0].x.body.clone();
                            let vir_e2_opt = if e2_opt.is_some() {
                                Some(vir_arms[1].x.body.clone())
                            } else {
                                None
                            };

                            let eb1 = erase_expr_opt(ctxt, mctxt, modeb, eb1, vir_eb);
                            let eb_erase = if let Some(eb1) = eb1 {
                                let pat = erase_pat(ctxt, mctxt, pat, &vir_arms[0].x.pattern);
                                let Expr { id, span, .. } = **eb; // for asymptotic efficiency, don't call eb.clone()
                                let kind = ExprKind::Let(P(pat), P(eb1));
                                let attrs = eb.attrs.clone();
                                Some(Expr { id, kind, span, attrs, tokens: eb.tokens.clone() })
                            } else {
                                None
                            };

                            (eb_erase, vir_e1, vir_e2_opt)
                        }
                        _ => {
                            panic!("could not match 'if-let' with de-sugared 'match'");
                        }
                    }
                }
                _ => match &vir_expr.x {
                    ExprX::If(vir_eb, vir_e1, vir_e2_opt) => {
                        let eb_erase = erase_expr_opt(ctxt, mctxt, modeb, eb, vir_eb);
                        (eb_erase, vir_e1.clone(), vir_e2_opt.clone())
                    }
                    _ => {
                        panic!("could not match If with If");
                    }
                },
            };
            let keep = |mctxt: &mut MCtxt, eb| {
                let e1 = erase_block(ctxt, mctxt, expect, e1, &vir_e1);
                let e2_opt = match (e2_opt, vir_e2_opt) {
                    (None, None) => None,
                    (Some(e2), Some(vir_e2)) => {
                        Some(P(erase_expr(ctxt, mctxt, expect, e2, &vir_e2)))
                    }
                    _ => panic!("mismatched if statements"),
                };
                ExprKind::If(P(eb), P(e1), e2_opt)
            };
            if modeb == Mode::Exec {
                let eb = eb_erase.expect("erase_expr");
                keep(mctxt, eb)
            } else {
                assert!(expect != Mode::Exec);
                if !ctxt.keep_proofs {
                    return eb_erase;
                } else if ctxt.keep_proofs && modeb == Mode::Spec {
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
        (ExprKind::Match(e0, arms0), ExprX::Match(vir_e0, vir_arms0)) => {
            let mode0 = *mctxt.find_span(&ctxt.condition_modes, &vir_expr.span);
            assert!(arms0.len() == vir_arms0.len());
            let keep = |mctxt: &mut MCtxt, e0| {
                let arms = arms0
                    .iter()
                    .zip(vir_arms0.iter())
                    .map(|(arm, vir_arm)| erase_arm(ctxt, mctxt, expect, arm, vir_arm))
                    .collect();
                ExprKind::Match(P(e0), arms)
            };
            if mode0 == Mode::Exec {
                let e0 = erase_expr(ctxt, mctxt, mode0, e0, vir_e0);
                keep(mctxt, e0)
            } else {
                assert!(expect != Mode::Exec);
                if !ctxt.keep_proofs {
                    return erase_expr_opt(ctxt, mctxt, mode0, e0, vir_e0);
                } else if ctxt.keep_proofs && mode0 == Mode::Spec {
                    let e0_erase = erase_expr_opt(ctxt, mctxt, mode0, e0, vir_e0);
                    // We erase e0, so we have no value to match on.
                    // Create nondeterministic booleans to take e0's place
                    // and a series of if/else to replace the match.
                    // if non_det1 e1 else if non_det2 e2 else ... else en
                    let mut if_else: Option<Expr> = None;
                    assert!(arms0.len() > 0); // already enforced by mode checker
                    for i in (0..arms0.len()).rev() {
                        // Turn arms0[i].body into block
                        let arm = &arms0[i];
                        let vir_arm = &vir_arms0[i];
                        let span = expr.span;
                        let body = erase_expr(ctxt, mctxt, expect, &arm.body, &vir_arm.x.body);
                        let kind = StmtKind::Expr(P(body));
                        let id = mctxt.next_node_id();
                        let stmt = Stmt { id, kind, span };
                        let id = mctxt.next_node_id();
                        let rules = rustc_ast::BlockCheckMode::Default;
                        let block = Block { stmts: vec![stmt], id, rules, span, tokens: None };
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
                    let e0 = erase_expr(ctxt, mctxt, mode0, e0, vir_e0);
                    keep(mctxt, e0)
                }
            }
        }
        (
            ExprKind::While(eb, block, None),
            ExprX::While { cond: vir_cond, body: vir_body, invs: _ },
        ) => {
            // The mode checker only allows While for Mode::Exec
            let eb = erase_expr(ctxt, mctxt, Mode::Exec, eb, vir_cond);
            let block = erase_block(ctxt, mctxt, Mode::Exec, block, vir_body);
            ExprKind::While(P(eb), P(block), None)
        }
        (ExprKind::Ret(None), ExprX::Return(None)) => ExprKind::Ret(None),
        (ExprKind::Ret(Some(e1)), ExprX::Return(Some(vir_e1))) => {
            let e1 = erase_expr(ctxt, mctxt, mctxt.ret_mode.expect("erase: ret_mode"), e1, vir_e1);
            ExprKind::Ret(Some(P(e1)))
        }
        (ExprKind::Block(block, None), _) => {
            let is_inv_block = attrs_is_invariant_block(&expr.attrs).expect("attrs fail");
            if is_inv_block {
                ExprKind::Block(P(erase_inv_block(ctxt, mctxt, expect, block, vir_expr)), None)
            } else {
                ExprKind::Block(P(erase_block(ctxt, mctxt, expect, block, vir_expr)), None)
            }
        }

        _ => {
            panic!("erase_expr: unable to match:\nRust AST: {:#?}\nVIR: {:#?}\n", expr, vir_expr)
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
    stmt: &Stmt,
    vir_stmt: &vir::ast::Stmt,
) -> Option<Stmt> {
    let kind: Option<StmtKind> = match (&stmt.kind, &vir_stmt.x) {
        (StmtKind::Local(local), StmtX::Decl { pattern: vir_pattern, init: vir_init_opt, .. }) => {
            let mode1 = *mctxt.find_span(&ctxt.var_modes, &vir_pattern.span);
            if keep_mode(ctxt, mode1) {
                let init = match (&local.init, vir_init_opt) {
                    (None, None) => None,
                    (Some(local_init), Some(vir_init)) => {
                        Some(P(erase_expr(ctxt, mctxt, mode1, &*local_init, vir_init)))
                    }
                    _ => {
                        panic!("Local init options do not match");
                    }
                };
                let Local { id, span, .. } = **local; // for asymptotic efficiency, don't call local.clone()
                let Local { ty, attrs, tokens, .. } = &**local;
                let pat = P(erase_pat(ctxt, mctxt, &local.pat, vir_pattern));
                let ty = ty.clone();
                let attrs = attrs.clone();
                let tokens = tokens.clone();
                let local = Local { id, pat, ty, init, span, attrs, tokens };
                Some(StmtKind::Local(P(local)))
            } else {
                match (&local.init, vir_init_opt) {
                    (None, None) => None,
                    (Some(local_init), Some(vir_init)) => {
                        match erase_expr_opt(ctxt, mctxt, mode1, &*local_init, vir_init) {
                            None => None,
                            Some(expr) => Some(StmtKind::Semi(P(expr))),
                        }
                    }
                    _ => {
                        panic!("Local init options do not match");
                    }
                }
            }
        }
        (StmtKind::Expr(expr), StmtX::Expr(vir_expr)) => {
            erase_expr_opt(ctxt, mctxt, Mode::Spec, expr, vir_expr).map(|e| StmtKind::Expr(P(e)))
        }
        (StmtKind::Semi(expr), StmtX::Expr(vir_expr)) => {
            erase_expr_opt(ctxt, mctxt, Mode::Spec, expr, vir_expr).map(|e| StmtKind::Semi(P(e)))
        }
        _ => {
            panic!("erase_stmt: unable to match:\nRust AST: {:#?}\nVIR: {:#?}\n", stmt, vir_stmt)
        }
    };
    let Stmt { id, span, .. } = *stmt; // for asymptotic efficiency, don't call stmt.clone()
    kind.map(|kind| Stmt { id, kind, span })
}

fn erase_stmt_matched_with_expr(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    expect: Mode,
    stmt: &Stmt,
    vir_expr: &vir::ast::Expr,
) -> Option<Stmt> {
    let kind: Option<StmtKind> = match &stmt.kind {
        StmtKind::Expr(expr) => {
            erase_expr_opt(ctxt, mctxt, expect, expr, vir_expr).map(|e| StmtKind::Expr(P(e)))
        }
        _ => {
            panic!(
                "erase_stmt_matched_with_expr: unable to match:\nRust AST: {:#?}\nVIR: {:#?}\n",
                stmt, vir_expr
            )
        }
    };
    let Stmt { id, span, .. } = *stmt; // for asymptotic efficiency, don't call stmt.clone()
    kind.map(|kind| Stmt { id, kind, span })
}

fn erase_inv_block(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    expect: Mode,
    block: &Block,
    vir_expr: &vir::ast::Expr,
) -> Block {
    let (vir_arg, vir_body) = match &vir_expr.x {
        ExprX::OpenInvariant(vir_arg, _vir_binder, vir_body) => (vir_arg, vir_body),
        _ => panic!("expected OpenInvariant"),
    };

    if block.stmts.len() != 3 {
        panic!(
            "erase_inv_block: the checks in invariant_block_to_vir should ensure the block has exactly 3 statements"
        );
    }

    let mut result_stmts = Vec::new();

    // First statement:
    // let (guard, mut ident) = open_invariant_begin(arg);

    // first, pattern match to get at the arg

    let open_stmt = &block.stmts[0];
    match &open_stmt.kind {
        StmtKind::Local(local) => {
            match &**local.init.as_ref().expect("erase_inv_block: the checks in invariant_block_to_vir should ensure the first statement is an initializer") {
                Expr { kind: ExprKind::Call(callfn, args), span, id, attrs, tokens } => {
                    let arg = &args[0];
                    let expr_opt = erase_expr_opt(ctxt, mctxt, Mode::Proof, arg, vir_arg);
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
                            init: Some(P(Expr {
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
    if let Some(stmt) = erase_stmt_matched_with_expr(ctxt, mctxt, expect, &block.stmts[1], vir_body)
    {
        result_stmts.push(stmt);
    }

    // Final statement:
    // open_invariant_end(guard, ident);
    // This is purely proof code. Keep it iff we keep proof-code.
    if ctxt.keep_proofs {
        result_stmts.push(block.stmts[2].clone());
    }

    let Block { id, rules, span, .. } = *block;
    Block { stmts: result_stmts, id, rules, span, tokens: block.tokens.clone() }
}

fn erase_block_external_body(block: &Block, info: &ExternalBodyErasureInfo) -> Block {
    assert!(info.num_header_stmts <= block.stmts.len());
    let stmts: Vec<Stmt> = block
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(i, stmt)| {
            if i < info.num_header_stmts {
                match &stmt.kind {
                    StmtKind::Semi(e) => match &e.kind {
                        ExprKind::Call(..) => {}
                        _ => {
                            panic!("expected something that looks like a header");
                        }
                    },
                    _ => {
                        panic!("expected something that looks like a header: {:#?}", stmt);
                    }
                }
                None
            } else {
                Some(stmt.clone())
            }
        })
        .collect();
    let Block { id, rules, span, .. } = *block; // for asymptotic efficiency, don't call block.clone()
    Block { stmts, id, rules, span, tokens: block.tokens.clone() }
}

fn erase_block(
    ctxt: &Ctxt,
    mctxt: &mut MCtxt,
    expect: Mode,
    block: &Block,
    vir_expr: &vir::ast::Expr,
) -> Block {
    match &vir_expr.x {
        ExprX::Block(vir_stmts, vir_expr_opt) => {
            let stmts: Vec<Stmt> = block
                .stmts
                .iter()
                .enumerate()
                .filter_map(|(i, stmt)| {
                    if i == vir_stmts.len() {
                        match vir_expr_opt {
                            Some(vir_expr) => {
                                erase_stmt_matched_with_expr(ctxt, mctxt, expect, stmt, vir_expr)
                            }
                            None => panic!("expected vir_expr"), // see above assert
                        }
                    } else {
                        erase_stmt(ctxt, mctxt, stmt, &vir_stmts[i])
                    }
                })
                .collect();

            let Block { id, rules, span, .. } = *block; // for asymptotic efficiency, don't call block.clone()
            Block { stmts, id, rules, span, tokens: block.tokens.clone() }
        }
        _ => {
            panic!("tried to match block with unexpected Expr");
        }
    }
}

fn erase_fn(ctxt: &Ctxt, mctxt: &mut MCtxt, f: &FnKind, external_body: bool) -> Option<FnKind> {
    let FnKind(defaultness, sig, generics, body_opt) = f;
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
                    GenericBoundX::None => new_params.push(param.clone()),
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

    match &f_vir.x.body {
        Some(vir_body) => {
            let body_opt = body_opt
                .as_ref()
                .map(|body| P(erase_block(ctxt, mctxt, ret_mode, &**body, vir_body)));
            mctxt.ret_mode = None;
            Some(FnKind(*defaultness, sig, generics, body_opt))
        }
        _ => {
            assert!(external_body);
            let info = &ctxt.external_body_functions[&sig.span];
            let body_opt =
                body_opt.as_ref().map(|body| P(erase_block_external_body(&**body, info)));
            Some(FnKind(*defaultness, sig, generics, body_opt))
        }
    }
}

fn erase_assoc_item(ctxt: &Ctxt, mctxt: &mut MCtxt, item: &AssocItem) -> Option<AssocItem> {
    match &item.kind {
        AssocItemKind::Fn(f) => {
            let vattrs = get_verifier_attrs(&item.attrs).expect("get_verifier_attrs");
            if vattrs.external {
                return Some(item.clone());
            }
            if vattrs.is_variant {
                return None;
            }
            let erased = erase_fn(ctxt, mctxt, f, vattrs.external_body);
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

fn erase_fields(ctxt: &Ctxt, old_fields: &Vec<StructField>) -> Vec<StructField> {
    let mut fields: Vec<StructField> = Vec::new();
    for field in old_fields {
        let mode = get_mode(Mode::Exec, &field.attrs[..]);
        if keep_mode(ctxt, mode) {
            fields.push(field.clone())
        }
    }
    fields
}

fn erase_variant_data(ctxt: &Ctxt, variant: &VariantData) -> VariantData {
    match variant {
        VariantData::Struct(fields, recovered) => {
            VariantData::Struct(erase_fields(ctxt, fields), *recovered)
        }
        VariantData::Tuple(fields, id) => VariantData::Tuple(erase_fields(ctxt, fields), *id),
        VariantData::Unit(_) => variant.clone(),
    }
}

fn erase_variant(ctxt: &Ctxt, variant: &Variant) -> Variant {
    let Variant { id, span, ident, is_placeholder, .. } = *variant;
    let Variant { attrs, vis, data, disr_expr, .. } = variant;
    let attrs = attrs.clone();
    let vis = vis.clone();
    let data = erase_variant_data(ctxt, data);
    let disr_expr = disr_expr.clone();
    Variant { attrs, id, span, vis, ident, data, disr_expr, is_placeholder }
}

fn erase_item(ctxt: &Ctxt, mctxt: &mut MCtxt, item: &Item) -> Vec<P<Item>> {
    let kind = match &item.kind {
        ItemKind::ExternCrate(_) => item.kind.clone(),
        ItemKind::Use(_) => item.kind.clone(),
        ItemKind::Mod(unsafety, kind) => ItemKind::Mod(*unsafety, erase_mod(ctxt, mctxt, kind)),
        ItemKind::ForeignMod { .. } => item.kind.clone(),
        ItemKind::Struct(variant, generics) => {
            ItemKind::Struct(erase_variant_data(ctxt, variant), generics.clone())
        }
        ItemKind::Enum(EnumDef { variants }, generics) => {
            let variants = vec_map(&variants, |v| erase_variant(ctxt, v));
            ItemKind::Enum(EnumDef { variants }, generics.clone())
        }
        ItemKind::Fn(kind) => {
            let vattrs = get_verifier_attrs(&item.attrs).expect("get_verifier_attrs");
            if vattrs.external {
                return vec![P(item.clone())];
            }
            match erase_fn(ctxt, mctxt, kind, vattrs.external_body) {
                None => return vec![],
                Some(kind) => ItemKind::Fn(Box::new(kind)),
            }
        }
        ItemKind::Impl(kind) => {
            let mut items: Vec<P<AssocItem>> = Vec::new();
            for item in &kind.items {
                if let Some(item) = erase_assoc_item(ctxt, mctxt, &item) {
                    items.push(P(item));
                }
            }
            // TODO we may need to erase some generic params
            // for asymptotic efficiency, don't call kind.clone():
            let ImplKind { unsafety, polarity, defaultness, constness, .. } = **kind;
            let ImplKind { generics, of_trait, self_ty, .. } = &**kind;
            let kind = ImplKind {
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
        _ => {
            unsupported!("unsupported item", item)
        }
    };
    vec![P(update_item(item, kind))]
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
    let mut external_body_functions = HashMap::new();
    let mut datatypes = HashMap::new();
    for f in &erasure_hints.vir_crate.functions {
        functions.insert(f.x.name.clone(), Some(f.clone())).map(|_| panic!("{:?}", &f.x.name));
        functions_by_span
            .insert(from_raw_span(&f.span.raw_span), Some(f.clone()))
            .map(|_| panic!("{:?}", &f.span));
    }
    for name in &erasure_hints.external_functions {
        functions.insert(name.clone(), None).map(|_| panic!("{:?}", name));
    }
    for span in &erasure_hints.ignored_functions {
        functions_by_span.insert(span.span(), None).map(|v| v.map(|_| panic!("{:?}", span)));
    }
    for (span, info) in &erasure_hints.external_body_functions {
        external_body_functions.insert(span.span(), info.clone());
    }
    for d in &erasure_hints.vir_crate.datatypes {
        datatypes.insert(d.x.path.clone(), d.clone()).map(|_| panic!("{:?}", &d.x.path));
    }
    let mut condition_modes: HashMap<Span, Mode> = HashMap::new();
    let mut var_modes: HashMap<Span, Mode> = HashMap::new();
    for (span, mode) in &erasure_hints.erasure_modes.condition_modes {
        condition_modes.insert(from_raw_span(&span.raw_span), *mode).map(|_| panic!("{:?}", span));
    }
    for (span, mode) in &erasure_hints.erasure_modes.var_modes {
        var_modes
            .insert(from_raw_span(&span.raw_span), *mode)
            .map(|v| panic!("{:?} {:?}", span, v));
    }
    Ctxt {
        vir_crate: erasure_hints.vir_crate.clone(),
        functions,
        functions_by_span,
        external_body_functions,
        datatypes,
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
        let ctxt = mk_ctxt(&self.erasure_hints, self.lifetimes_only);
        let mut mctxt = MCtxt { f_next_node_id: next_node_id, ret_mode: None };
        let time0 = Instant::now();
        let krate = crate::erase::erase_crate(&ctxt, &mut mctxt, krate);
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
            crate::lifetime::check(queries);
            self.maybe_print(compiler, queries);
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
