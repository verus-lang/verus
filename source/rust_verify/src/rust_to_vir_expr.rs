use crate::attributes::{
    Attr, GhostBlockAttr, get_custom_err_annotations, get_ghost_block_opt, get_trigger,
    get_var_mode, parse_attrs, parse_attrs_opt,
};
use crate::context::{BodyCtxt, Context};
use crate::erase::{CompilableOperator, ResolvedCall};
use crate::rust_intrinsics_to_vir::int_intrinsic_constant_to_vir;
use crate::rust_to_vir_base::{
    auto_deref_supported_for_ty, bitwidth_and_signedness_of_integer_type, def_id_to_vir_path,
    get_impl_paths_for_clauses, get_range, is_smt_arith, is_smt_equality, local_to_var,
    mid_ty_simplify, mid_ty_to_vir, mid_ty_to_vir_ghost, mk_range, typ_of_node,
    typ_of_node_expect_mut_ref,
};
use crate::rust_to_vir_ctor::{AdtKind, resolve_braces_ctor, resolve_ctor};
use crate::spans::err_air_span;
use crate::util::{err_span, err_span_bare, slice_vec_map_result, vec_map_result};
use crate::verus_items::{
    self, CompilableOprItem, DummyCaptureItem, InvariantItem, OpenInvariantBlockItem,
    SpecGhostTrackedItem, UnaryOpItem, VerusItem, VstdItem,
};
use crate::{fn_call_to_vir::fn_call_to_vir, unsupported_err, unsupported_err_unless};
use air::ast::Binder;
use air::ast_util::str_ident;
use rustc_ast::LitKind;
use rustc_hir::def::{CtorKind, DefKind, Res};
use rustc_hir::{
    AssignOpKind, BinOpKind, Block, Closure, Destination, Expr, ExprKind, HirId, ItemKind, LetExpr,
    LetStmt, Lit, LoopSource, Node, Pat, PatExpr, PatExprKind, PatKind, QPath, Stmt, StmtKind,
    StructTailExpr, UnOp,
};
use rustc_hir::{Attribute, BindingMode, BorrowKind, ByRef, Mutability};
use rustc_middle::ty::adjustment::{
    Adjust, Adjustment, AutoBorrow, AutoBorrowMutability, PointerCoercion,
};
use rustc_middle::ty::{
    AdtDef, ClauseKind, GenericArg, TraitPredicate, TraitRef, TyCtxt, TyKind, TypingEnv, Upcast,
};
use rustc_mir_build_verus::verus::BodyErasure;
use rustc_span::Span;
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use std::sync::Arc;
use vir::ast::{
    ArithOp, ArmX, AutospecUsage, BinaryOp, BitwiseOp, CallTarget, Constant, Dt, ExprX, FieldOpr,
    FunX, HeaderExprX, ImplPath, InequalityOp, IntRange, InvAtomicity, Mode, PatternX, Primitive,
    SpannedTyped, StmtX, Stmts, Typ, TypX, UnaryOp, UnaryOpr, VarBinder, VarBinderX, VarIdent,
    VariantCheck, VirErr,
};
use vir::ast_util::{
    bool_typ, ident_binder, mk_tuple_field_x, mk_tuple_typ, mk_tuple_x, str_unique_var,
    typ_to_diagnostic_str, types_equal, undecorate_typ,
};
use vir::def::{field_ident_from_rust, positional_field_ident};

pub(crate) fn pat_to_mut_var<'tcx>(pat: &Pat) -> Result<(bool, VarIdent), VirErr> {
    let Pat { hir_id: _, kind, span, default_binding_modes } = pat;
    unsupported_err_unless!(default_binding_modes, *span, "default_binding_modes");
    match kind {
        PatKind::Binding(annotation, id, ident, _subpat) => {
            let BindingMode(_, mutability) = annotation;
            let mutable = match mutability {
                rustc_hir::Mutability::Mut => true,
                rustc_hir::Mutability::Not => false,
            };
            Ok((mutable, local_to_var(ident, id.local_id)))
        }
        _ => {
            unsupported_err!(*span, "only variables are supported here, not general patterns")
        }
    }
}

pub(crate) fn pat_to_var<'tcx>(pat: &Pat) -> Result<VarIdent, VirErr> {
    let (_, name) = pat_to_mut_var(pat)?;
    Ok(name)
}

pub(crate) fn extract_array<'tcx>(expr: &'tcx Expr<'tcx>) -> Vec<&'tcx Expr<'tcx>> {
    match &expr.kind {
        ExprKind::Array(fields) => fields.iter().collect(),
        _ => vec![expr],
    }
}

pub(crate) fn extract_tuple<'tcx>(expr: &'tcx Expr<'tcx>) -> Vec<&'tcx Expr<'tcx>> {
    match &expr.kind {
        ExprKind::Tup(exprs) => exprs.iter().collect(),
        _ => vec![expr],
    }
}

pub(crate) fn closure_param_typs<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<Vec<Typ>, VirErr> {
    let node_type = bctx.types.node_type(expr.hir_id);
    match node_type.kind() {
        TyKind::Closure(_def, substs) => {
            let sig = substs.as_closure().sig();
            let mut args: Vec<Typ> = Vec::new();
            // REVIEW: rustc docs refer to skip_binder as "dangerous"
            for t in sig.inputs().skip_binder().iter() {
                args.push(mid_ty_to_vir(
                    bctx.ctxt.tcx,
                    &bctx.ctxt.verus_items,
                    bctx.fun_id,
                    expr.span,
                    t,
                    false, /* allow_mut_ref */
                )?);
            }
            assert!(args.len() == 1);
            match &*args[0] {
                TypX::Datatype(Dt::Tuple(_), typs, ..) => Ok((**typs).clone()),
                _ => panic!("expected tuple type"),
            }
        }
        _ => panic!("closure_param_types expected Closure type"),
    }
}

fn closure_ret_typ<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr<'tcx>) -> Result<Typ, VirErr> {
    let node_type = bctx.types.node_type(expr.hir_id);
    match node_type.kind() {
        TyKind::Closure(_def, substs) => {
            let sig = substs.as_closure().sig();
            let t = sig.output().skip_binder();
            mid_ty_to_vir(
                bctx.ctxt.tcx,
                &bctx.ctxt.verus_items,
                bctx.fun_id,
                expr.span,
                &t,
                false, /* allow_mut_ref */
            )
        }
        _ => panic!("closure_param_types expected Closure type"),
    }
}

fn mk_clip<'tcx>(
    range: &IntRange,
    expr: &vir::ast::Expr,
    recommends_assume_truncate: bool,
) -> vir::ast::Expr {
    match range {
        IntRange::Int => expr.clone(),
        range => SpannedTyped::new(
            &expr.span,
            &Arc::new(TypX::Int(*range)),
            ExprX::Unary(
                UnaryOp::Clip { range: *range, truncate: recommends_assume_truncate },
                expr.clone(),
            ),
        ),
    }
}

pub(crate) fn mk_ty_clip<'tcx>(
    typ: &Typ,
    expr: &vir::ast::Expr,
    recommends_assume_truncate: bool,
) -> vir::ast::Expr {
    mk_clip(&get_range(typ), expr, recommends_assume_truncate)
}

pub(crate) fn check_lit_int(
    ctxt: &Context,
    span: Span,
    in_negative_literal: bool,
    i: u128,
    typ: &Typ,
) -> Result<(), VirErr> {
    let i_bump = if in_negative_literal { 1 } else { 0 };
    if let TypX::Int(range) = *undecorate_typ(typ) {
        match range {
            IntRange::Int | IntRange::Nat => Ok(()),
            IntRange::U(n) if n == 128 || (n < 128 && i < (1u128 << n)) => Ok(()),
            IntRange::I(n) if n - 1 < 128 && i < (1u128 << (n - 1)) + i_bump => Ok(()),
            IntRange::USize
                if i < (1u128
                    << (ctxt.arch_word_bits.expect("unkown arch_word_bits").min_bits()
                        as u128)) =>
            {
                Ok(())
            }
            IntRange::ISize
                if i < (1u128
                    << (ctxt.arch_word_bits.expect("unkown arch_word_bits").min_bits() - 1))
                    + i_bump =>
            {
                Ok(())
            }
            _ => {
                return err_span(span, format!("integer literal out of range {:?}", range));
            }
        }
    } else {
        return err_span(span, "expected integer type");
    }
}

pub(crate) fn expr_to_vir_inner<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = expr.peel_drop_temps();

    if bctx.external_body {
        // we want just requires/ensures, not the whole body
        match &expr.kind {
            ExprKind::Block(..) | ExprKind::Call(..) | ExprKind::Closure(_) => {}
            _ => {
                return Ok(bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Block(Arc::new(vec![]), None),
                ));
            }
        }
    }

    let adjustments = bctx.types.expr_adjustments(expr);

    expr_to_vir_with_adjustments(bctx, expr, modifier, adjustments, adjustments.len())
}

pub(crate) fn expr_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let mut vir_expr = expr_to_vir_inner(bctx, expr, modifier)?;
    let attrs = bctx.ctxt.tcx.hir_attrs(expr.hir_id);
    for group in get_trigger(attrs)? {
        vir_expr = vir_expr.new_x(ExprX::Unary(UnaryOp::Trigger(group), vir_expr.clone()));
    }
    for err_msg in get_custom_err_annotations(attrs)? {
        vir_expr = vir_expr
            .new_x(ExprX::UnaryOpr(UnaryOpr::CustomErr(Arc::new(err_msg)), vir_expr.clone()));
    }
    Ok(vir_expr)
}

pub(crate) fn patexpr_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    pat: &Pat<'tcx>,
    pat_typ: &Typ,
    pat_expr: &PatExpr<'tcx>,
) -> Result<PatternX, VirErr> {
    let tcx = bctx.ctxt.tcx;
    match pat_expr.kind {
        PatExprKind::Lit { lit, negated } => {
            Ok(PatternX::Expr(lit_to_vir(bctx, span, &lit, negated, pat_typ, None)?))
        }
        PatExprKind::Path(qpath) => {
            let res = bctx.types.qpath_res(&qpath, pat_expr.hir_id);
            match res {
                Res::Def(DefKind::Const, id) => {
                    let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, id);
                    let fun = FunX { path };
                    let autospec_usage =
                        if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };
                    let x = ExprX::ConstVar(Arc::new(fun), autospec_usage);

                    let expr = bctx.spanned_typed_new(pat.span, &pat_typ, x);

                    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                    erasure_info.hir_vir_ids.push((pat_expr.hir_id, expr.span.id));

                    Ok(PatternX::Expr(expr))
                }
                Res::Err => err_span(span, format!("Couldn't resolve {qpath:#?}")),
                _ => match resolve_ctor(bctx.ctxt.tcx, res) {
                    Some((ctor, CtorKind::Const)) => {
                        let variant_name = str_ident(&ctor.variant_def.ident(tcx).as_str());
                        let vir_path = def_id_to_vir_path(
                            bctx.ctxt.tcx,
                            &bctx.ctxt.verus_items,
                            ctor.adt_def_id,
                        );
                        Ok(PatternX::Constructor(
                            Dt::Path(vir_path),
                            variant_name,
                            Arc::new(vec![]),
                        ))
                    }
                    _ => {
                        crate::internal_err!(pat.span, "expected const constructor")
                    }
                },
            }
        }
        PatExprKind::ConstBlock(_) => err_span(span, "PatExprKind::ConstBlock"),
    }
}

pub(crate) fn get_fn_path<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Fun, VirErr> {
    match &expr.kind {
        ExprKind::Path(qpath) => {
            let id = bctx.types.qpath_res(qpath, expr.hir_id).def_id();
            if let Some(_) =
                bctx.ctxt.tcx.impl_of_method(id).and_then(|ii| bctx.ctxt.tcx.trait_id_of_impl(ii))
            {
                unsupported_err!(expr.span, format!("Fn {:?}", id))
            } else {
                let path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, id);
                Ok(Arc::new(FunX { path }))
            }
        }
        _ => unsupported_err!(expr.span, format!("{:?}", expr)),
    }
}

pub(crate) fn expr_tuple_datatype_ctor_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    ctor: crate::rust_to_vir_ctor::Ctor,
    args_slice: &[Expr<'tcx>],
    fun_span: Span,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let expr_typ = typ_of_node(bctx, expr.span, &expr.hir_id, false)?;

    let variant_name = str_ident(&ctor.variant_def.ident(tcx).as_str());
    let vir_path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, ctor.adt_def_id);

    let vir_fields = Arc::new(
        args_slice
            .iter()
            .enumerate()
            .map(|(i, e)| -> Result<_, VirErr> {
                let vir = expr_to_vir(bctx, e, modifier)?;
                Ok(ident_binder(&positional_field_ident(i), &vir))
            })
            .collect::<Result<Vec<_>, _>>()?,
    );
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    let resolved_call = ResolvedCall::Ctor(vir_path.clone(), variant_name.clone());
    erasure_info.resolved_calls.push((expr.hir_id, fun_span.data(), resolved_call));
    let exprx = ExprX::Ctor(Dt::Path(vir_path), variant_name, vir_fields, None);
    Ok(bctx.spanned_typed_new(expr.span, &expr_typ, exprx))
}

fn handle_dot_dot(
    num_entries_in_pat: usize,
    total_entries: usize,
    dot_dot_pos: &rustc_hir::DotDotPos,
) -> (usize, usize) {
    match dot_dot_pos.as_opt_usize() {
        None => {
            assert!(num_entries_in_pat == total_entries);
            (0, 0)
        }
        Some(pos) => {
            assert!(pos <= num_entries_in_pat);
            assert!(num_entries_in_pat <= total_entries);
            let n_wildcards = total_entries - num_entries_in_pat;
            (n_wildcards, pos)
        }
    }
}

pub(crate) fn pattern_to_vir_inner<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pat: &Pat<'tcx>,
) -> Result<vir::ast::Pattern, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let pat_typ = typ_of_node(bctx, pat.span, &pat.hir_id, false)?;
    unsupported_err_unless!(pat.default_binding_modes, pat.span, "complex pattern");
    let pattern = match &pat.kind {
        PatKind::Wild => PatternX::Wildcard(false),
        PatKind::Binding(BindingMode(_, mutability), canonical, x, subpat) => {
            let mutable = match mutability {
                Mutability::Not => false,
                Mutability::Mut => true,
            };

            // In new-mut-refs, we need to treat a variable as 'mutable' if it's a
            // mutable reference (or if it contains a nested mutable reference),
            // even if the variable is not marked 'mut'.
            // Conservatively mark all variables non-mutable for now
            // TODO be more precise about this.
            let mutable = mutable || bctx.ctxt.cmd_line_args.new_mut_ref;

            let name = local_to_var(x, canonical.local_id);
            match subpat {
                None => PatternX::Var { name, mutable },
                Some(subpat) => {
                    PatternX::Binding { name, mutable, sub_pat: pattern_to_vir(bctx, subpat)? }
                }
            }
        }
        PatKind::Expr(expr) => patexpr_to_vir(bctx, expr.span, pat, &pat_typ, expr)?,
        PatKind::Tuple(pats, dot_dot_pos) => {
            let n = match &*pat_typ {
                TypX::Datatype(Dt::Tuple(n), typs, ..) => {
                    assert!(typs.len() == *n);
                    *n
                }
                _ => {
                    crate::internal_err!(pat.span, "expected tuple type")
                }
            };

            let (n_wildcards, pos_to_insert_wildcards) =
                handle_dot_dot(pats.len(), n, &dot_dot_pos);

            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for (i, pat) in pats.iter().enumerate() {
                let actual_idx = if i < pos_to_insert_wildcards { i } else { i + n_wildcards };

                let pattern = pattern_to_vir(bctx, pat)?;
                let binder = ident_binder(&positional_field_ident(actual_idx), &pattern);
                binders.push(binder);
            }

            let variant_name = vir::def::prefix_tuple_variant(n);
            PatternX::Constructor(Dt::Tuple(n), variant_name, Arc::new(binders))
        }
        PatKind::TupleStruct(qpath, pats, dot_dot_pos) => {
            let res = bctx.types.qpath_res(qpath, pat.hir_id);
            let ctor = resolve_ctor(bctx.ctxt.tcx, res);
            let Some((ctor, CtorKind::Fn)) = ctor else {
                crate::internal_err!(pat.span, "expected Fn constructor")
            };

            let variant_name = str_ident(&ctor.variant_def.ident(tcx).as_str());
            let vir_path =
                def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, ctor.adt_def_id);

            let (n_wildcards, pos_to_insert_wildcards) =
                handle_dot_dot(pats.len(), ctor.variant_def.fields.len(), &dot_dot_pos);

            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for (i, pat) in pats.iter().enumerate() {
                let actual_idx = if i < pos_to_insert_wildcards { i } else { i + n_wildcards };

                let pattern = pattern_to_vir(bctx, pat)?;
                let binder = ident_binder(&positional_field_ident(actual_idx), &pattern);
                binders.push(binder);
            }

            PatternX::Constructor(Dt::Path(vir_path), variant_name, Arc::new(binders))
        }
        PatKind::Struct(qpath, pats, _) => {
            let res = bctx.types.qpath_res(qpath, pat.hir_id);
            let ty = bctx.types.node_type(pat.hir_id);
            let ctor = resolve_braces_ctor(tcx, res, ty, false, pat.span)?;
            let variant_name = str_ident(&ctor.variant_def.ident(tcx).as_str());
            let vir_path =
                def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, ctor.adt_def_id);

            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for fpat in pats.iter() {
                let pattern = pattern_to_vir(bctx, &fpat.pat)?;
                let ident = field_ident_from_rust(fpat.ident.as_str());
                let binder = ident_binder(&ident, &pattern);
                binders.push(binder);
            }
            PatternX::Constructor(Dt::Path(vir_path), variant_name, Arc::new(binders))
        }
        PatKind::Box(pat) => {
            return pattern_to_vir(bctx, pat);
        }
        PatKind::Or(pats) => {
            if pats.len() == 1 {
                return pattern_to_vir(bctx, &pats[0]);
            }

            assert!(pats.len() >= 2);

            let mut patterns: Vec<vir::ast::Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(pattern_to_vir(bctx, pat)?);
            }

            // Arrange it like Or(a, Or(b, Or(c, d)))
            // Also, make sure to preserve the order.

            let mut pat_iter = patterns.into_iter().rev();
            let plast = pat_iter.next().unwrap();
            let plast2 = pat_iter.next().unwrap();
            let mut pat_or = PatternX::Or(plast2, plast);
            while let Some(p) = pat_iter.next() {
                pat_or = PatternX::Or(p, bctx.spanned_typed_new(pat.span, &pat_typ, pat_or));
            }
            pat_or
        }
        PatKind::Range(expr1_opt, expr2_opt, range_end) => {
            let e1 = match expr1_opt {
                None => None,
                Some(expr1) => {
                    let e1 = patexpr_to_vir(bctx, expr1.span, pat, &pat_typ, expr1)?;
                    if let PatternX::Expr(e1) = e1 {
                        if !matches!(&*e1.typ, TypX::Int(_)) {
                            unsupported_err!(expr1.span, "range pattern with non-int type");
                        }
                        Some(e1)
                    } else {
                        return err_span(expr1.span, "range pattern with unsupported type");
                    }
                }
            };
            let e2 = match expr2_opt {
                None => None,
                Some(expr2) => {
                    let e2 = patexpr_to_vir(bctx, expr2.span, pat, &pat_typ, expr2)?;
                    if let PatternX::Expr(e2) = e2 {
                        if !matches!(&*e2.typ, TypX::Int(_)) {
                            unsupported_err!(expr2.span, "range pattern with non-int type");
                        }
                        let ineq = match range_end {
                            rustc_hir::RangeEnd::Included => InequalityOp::Le,
                            rustc_hir::RangeEnd::Excluded => InequalityOp::Lt,
                        };
                        Some((e2, ineq))
                    } else {
                        return err_span(expr2.span, "range pattern with unsupported type");
                    }
                }
            };
            PatternX::Range(e1, e2)
        }
        PatKind::Guard(..) => unsupported_err!(pat.span, "pattern guards", pat),
        PatKind::Ref(..) => unsupported_err!(pat.span, "ref patterns", pat),
        PatKind::Slice(..) => unsupported_err!(pat.span, "slice patterns", pat),
        PatKind::Never => unsupported_err!(pat.span, "never patterns", pat),
        PatKind::Deref(_) => unsupported_err!(pat.span, "deref patterns", pat),
        PatKind::Err(_) => unsupported_err!(pat.span, "err patterns", pat),
        PatKind::Missing => unsupported_err!(pat.span, "missing patterns", pat),
    };
    let pattern = bctx.spanned_typed_new(pat.span, &pat_typ, pattern);
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.resolved_pats.push((pat.span.data(), pattern.clone()));
    Ok(pattern)
}

pub(crate) fn pattern_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pat: &Pat<'tcx>,
) -> Result<vir::ast::Pattern, VirErr> {
    let vir_pat = pattern_to_vir_inner(bctx, pat)?;
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.hir_vir_ids.push((pat.hir_id, vir_pat.span.id));
    Ok(vir_pat)
}

pub(crate) fn block_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    block: &Block<'tcx>,
    span: &Span,
    ty: &Typ,
    mut modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let mut vir_stmts: Vec<vir::ast::Stmt> = Vec::new();
    let mut stmts_iter = block.stmts.iter();
    while let Some(mut some_stmts) = stmts_to_vir(bctx, &mut stmts_iter)? {
        vir_stmts.append(&mut some_stmts);
    }
    if block.stmts.len() != 0 {
        modifier = ExprModifier { deref_mut: false, ..modifier };
    }
    let vir_expr = block.expr.map(|expr| expr_to_vir(bctx, &expr, modifier)).transpose()?;

    let x = ExprX::Block(Arc::new(vir_stmts), vir_expr);
    Ok(bctx.spanned_typed_new(span.clone(), ty, x))
}

/// Check for the #[verifier(invariant_block)] attribute
pub fn attrs_is_invariant_block(attrs: &[Attribute]) -> Result<bool, VirErr> {
    let attrs_vec = parse_attrs(attrs, None)?;
    for attr in &attrs_vec {
        match attr {
            Attr::InvariantBlock => {
                return Ok(true);
            }
            _ => {}
        }
    }
    Ok(false)
}

/// Check for the #[verifier(invariant_block)] attribute on a block
fn is_invariant_block(bctx: &BodyCtxt, expr: &Expr) -> Result<bool, VirErr> {
    let attrs = bctx.ctxt.tcx.hir_attrs(expr.hir_id);
    attrs_is_invariant_block(attrs)
}

fn malformed_inv_block_err<'tcx>(expr: &Expr<'tcx>) -> Result<vir::ast::Expr, VirErr> {
    err_span(
        expr.span,
        "malformed invariant block; use `open_atomic_invariant!` or `open_local_invariant!` macro instead",
    )
}

pub(crate) fn is_spend_open_invariant_credit_call(
    verus_items: &verus_items::VerusItems,
    spend_stmt: &Stmt,
) -> bool {
    match spend_stmt.kind {
        StmtKind::Semi(Expr {
            kind:
                ExprKind::Call(
                    Expr {
                        kind:
                            ExprKind::Path(QPath::Resolved(
                                None,
                                rustc_hir::Path { res: Res::Def(_, fun_id), .. },
                            )),
                        ..
                    },
                    [Expr { .. }],
                ),
            ..
        }) => match verus_items.id_to_name.get(&fun_id) {
            Some(&VerusItem::Vstd(
                VstdItem::Invariant(InvariantItem::SpendOpenInvariantCredit),
                _,
            )) => true,
            Some(&VerusItem::Vstd(
                VstdItem::Invariant(InvariantItem::SpendOpenInvariantCreditInProof),
                _,
            )) => true,
            _ => false,
        },
        _ => false,
    }
}

pub(crate) fn invariant_block_open<'a>(
    verus_items: &verus_items::VerusItems,
    open_stmt: &'a Stmt,
) -> Option<(HirId, HirId, &'a rustc_hir::Pat<'a>, &'a rustc_hir::Expr<'a>, InvAtomicity)> {
    match open_stmt.kind {
        StmtKind::Let(LetStmt {
            pat:
                Pat {
                    kind:
                        PatKind::Tuple(
                            [
                                Pat {
                                    kind:
                                        PatKind::Binding(
                                            BindingMode(_, Mutability::Not),
                                            guard_hir,
                                            _,
                                            None,
                                        ),
                                    default_binding_modes: true,
                                    ..
                                },
                                inner_pat @ Pat {
                                    kind:
                                        PatKind::Binding(
                                            BindingMode(_, Mutability::Mut),
                                            inner_hir,
                                            _,
                                            None,
                                        ),
                                    default_binding_modes: true,
                                    ..
                                },
                            ],
                            dot_dot_pos,
                        ),
                    ..
                },
            init:
                Some(Expr {
                    kind:
                        ExprKind::Call(
                            Expr {
                                kind:
                                    ExprKind::Path(QPath::Resolved(
                                        None,
                                        rustc_hir::Path {
                                            res: Res::Def(DefKind::Fn, fun_id), ..
                                        },
                                    )),
                                ..
                            },
                            [arg],
                        ),
                    ..
                }),
            els: None,
            ..
        }) if dot_dot_pos.as_opt_usize().is_none() => {
            let verus_item = verus_items.id_to_name.get(fun_id);
            let atomicity = match verus_item {
                Some(VerusItem::OpenInvariantBlock(
                    OpenInvariantBlockItem::OpenAtomicInvariantBegin,
                )) => InvAtomicity::Atomic,
                Some(VerusItem::OpenInvariantBlock(
                    OpenInvariantBlockItem::OpenLocalInvariantBegin,
                )) => InvAtomicity::NonAtomic,
                _ => {
                    return None;
                }
            };
            Some((*guard_hir, *inner_hir, inner_pat, arg, atomicity))
        }
        _ => {
            dbg!(&open_stmt);
            None
        }
    }
}

pub(crate) fn invariant_block_close(close_stmt: &Stmt) -> Option<(HirId, HirId, DefId)> {
    match close_stmt.kind {
        StmtKind::Semi(Expr {
            kind:
                ExprKind::Call(
                    Expr {
                        kind:
                            ExprKind::Path(QPath::Resolved(
                                None,
                                rustc_hir::Path { res: Res::Def(_, fun_id), .. },
                            )),
                        ..
                    },
                    [
                        Expr {
                            kind:
                                ExprKind::Path(QPath::Resolved(
                                    None,
                                    rustc_hir::Path { res: Res::Local(hir_id1), .. },
                                )),
                            ..
                        },
                        Expr {
                            kind:
                                ExprKind::Path(QPath::Resolved(
                                    None,
                                    rustc_hir::Path { res: Res::Local(hir_id2), .. },
                                )),
                            ..
                        },
                    ],
                ),
            ..
        }) => Some((*hir_id1, *hir_id2, *fun_id)),
        _ => None,
    }
}

fn invariant_block_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    // The open_atomic_invariant! macro produces code that looks like this
    // (and similarly for open_local_invariant!)
    //
    // #[verifier(invariant_block)] {
    //      spend_open_invariant_credit($credit_expr);
    //      let (guard, mut $inner) = open_atomic_invariant_begin($eexpr);
    //      $bblock
    //      open_invariant_end(guard, $inner);
    //  }
    //
    // We need to check that it really does have this form, including
    // that the identifiers `guard` and `inner` used in the last statement
    // are the same as in the first statement. This is what the giant
    // `match` statements below are for.
    //
    // We also need to "recover" the $inner, $eexpr, and $bblock for conversion to VIR.
    //
    // If the AST doesn't look exactly like we expect, print an error asking the user
    // to use the open_atomic_invariant! macro.

    let body = match &expr.kind {
        ExprKind::Block(body, _) => body,
        _ => panic!("invariant_block_to_vir called with non-Body expression"),
    };

    if body.stmts.len() != 4 || body.expr.is_some() {
        return malformed_inv_block_err(expr);
    }

    let spend_stmt = &body.stmts[0];
    let open_stmt = &body.stmts[1];
    let mid_stmt = &body.stmts[2];
    let close_stmt = &body.stmts[3];

    if !is_spend_open_invariant_credit_call(&bctx.ctxt.verus_items, spend_stmt) {
        return malformed_inv_block_err(expr);
    }

    let (guard_hir, inner_hir, inner_pat, inv_arg, atomicity) = {
        if let Some(block_open) = invariant_block_open(&bctx.ctxt.verus_items, open_stmt) {
            block_open
        } else {
            return malformed_inv_block_err(expr);
        }
    };

    if let Some((hir_id1, hir_id2, fun_id)) = invariant_block_close(close_stmt) {
        let verus_item = bctx.ctxt.verus_items.id_to_name.get(&fun_id);
        if verus_item
            != Some(&VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenInvariantEnd))
        {
            return malformed_inv_block_err(expr);
        }

        if hir_id1 != guard_hir || hir_id2 != inner_hir {
            return malformed_inv_block_err(expr);
        }
    } else {
        return malformed_inv_block_err(expr);
    }

    let vir_body = match mid_stmt.kind {
        StmtKind::Expr(e @ Expr { kind: ExprKind::Block(body, _), .. }) => {
            assert!(!is_invariant_block(bctx, e)?);
            let vir_stmts: Stmts = Arc::new(
                slice_vec_map_result(body.stmts, |stmt| stmt_to_vir(bctx, stmt))?
                    .into_iter()
                    .flatten()
                    .collect(),
            );
            let vir_expr = body.expr.map(|expr| expr_to_vir(bctx, &expr, modifier)).transpose()?;
            let ty = typ_of_node(bctx, e.span, &e.hir_id, false)?;
            // NOTE: we use body.span here instead of e.span
            // body.span leads to better error messages
            // (e.g., the "Cannot show invariant holds at end of block" error)
            // (e.span or mid_stmt.span would expose macro internals)
            bctx.spanned_typed_new(body.span, &ty, ExprX::Block(vir_stmts, vir_expr))
        }
        _ => {
            return malformed_inv_block_err(expr);
        }
    };

    let vir_arg = expr_to_vir(bctx, &inv_arg, modifier)?;

    let name = pat_to_var(inner_pat)?;
    let inner_ty = typ_of_node(bctx, inner_pat.span, &inner_hir, false)?;
    let vir_binder = Arc::new(VarBinderX { name, a: inner_ty });

    let mid_exp = bctx.spanned_typed_new(
        mid_stmt.span,
        &typ_of_node(bctx, expr.span, &expr.hir_id, false)?,
        ExprX::OpenInvariant(vir_arg, vir_binder, vir_body, atomicity),
    );
    let spend_stmt_vir = stmt_to_vir(&bctx, spend_stmt)
        .expect("could not convert spend_open_invariant_credit call to vir");
    Ok(bctx.spanned_typed_new(
        expr.span,
        &typ_of_node(bctx, expr.span, &expr.hir_id, false)?,
        ExprX::Block(Arc::new(spend_stmt_vir), Some(mid_exp)),
    ))
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) struct ExprModifier {
    /// dereferencing a mutable reference
    pub(crate) deref_mut: bool,
    /// taking a mutable reference
    pub(crate) addr_of_mut: bool,
}

impl ExprModifier {
    pub(crate) const REGULAR: Self = Self { deref_mut: false, addr_of_mut: false };

    pub(crate) const DEREF_MUT: Self = Self { deref_mut: true, addr_of_mut: false };

    pub(crate) const ADDR_OF_MUT: Self = Self { deref_mut: false, addr_of_mut: true };
}

pub(crate) fn is_expr_typ_mut_ref<'tcx>(
    ty: rustc_middle::ty::Ty<'tcx>,
    modifier: ExprModifier,
) -> Result<ExprModifier, VirErr> {
    match ty.kind() {
        TyKind::Ref(_, _tys, rustc_ast::Mutability::Mut) => {
            Ok(ExprModifier { deref_mut: true, ..modifier })
        }
        _ => Ok(modifier),
    }
}

pub(crate) fn expr_to_vir_with_adjustments<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    current_modifier: ExprModifier,
    adjustments: &[Adjustment<'tcx>],
    adjustment_idx: usize,
) -> Result<vir::ast::Expr, VirErr> {
    // Implicit conversions are stored in the "adjustments" for each node
    // See: https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/adjustment/struct.Adjustment.html
    //
    // For example, suppose the user writes the expression `v` but Rust
    // inserts a borrow a deref so that we have to treat the node like `&*v`.
    //
    // Then we'd have:
    //
    //    adjustments[0] = Deref (*)
    //    adjustments[1] = Borrow (&)
    //
    // That is, the higher indices mean adjustments that are farther on the outside.
    //
    // The adjustment objects also have the type after each is applied, e.g.,
    //
    //    expr_ty(expr)                                    type of `v`
    //    adjustments[0].target                            type of `*v`
    //    adjumstmens[1].target = expr_ty_adjusted(expr)   type of `&*v`
    //
    // Since we're recursing inwards, we start with adjustment_idx = adjustments.len()
    // and decrement to recurse.
    // Specifically, the node (expr, i) means expr with the first i adjustments
    // applied. So (expr, i) has child node (expr, i - 1) which is obtained by
    // peeling off the adjustment (i-1).
    // Whereas the node (expr, 0) is just expr by itself.

    let expr_typ = || {
        mid_ty_to_vir(
            bctx.ctxt.tcx,
            &bctx.ctxt.verus_items,
            bctx.fun_id,
            expr.span,
            &adjustments[adjustment_idx - 1].target,
            false,
        )
    };

    if adjustment_idx == 0 {
        let vir_expr = expr_to_vir_innermost(bctx, expr, current_modifier)?;

        let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
        erasure_info.hir_vir_ids.push((expr.hir_id, vir_expr.span.id));
        return Ok(vir_expr);
    }

    // Gets the type of the *child* of the current node
    //
    // The `target` field gives the type *after* adjustment, so we need to get the
    // target of the previous adjustment. If this is already the first adjustment,
    // Use `expr_ty` which is the type of the expression with no adjustments applied.
    let get_inner_ty = || {
        if adjustment_idx == 1 {
            bctx.types.expr_ty(expr)
        } else {
            adjustments[adjustment_idx - 2].target
        }
    };

    let get_inner2_ty = || {
        if adjustment_idx == 2 {
            bctx.types.expr_ty(expr)
        } else {
            adjustments[adjustment_idx - 3].target
        }
    };

    let adjustment = &adjustments[adjustment_idx - 1];

    match &adjustment.kind {
        Adjust::NeverToAny => {
            let e = expr_to_vir_with_adjustments(
                bctx,
                expr,
                current_modifier,
                adjustments,
                adjustment_idx - 1,
            )?;
            let x = ExprX::NeverToAny(e);
            Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, x))
        }
        Adjust::Deref(None) => {
            // handle same way as the UnOp::Deref case
            let new_modifier = is_expr_typ_mut_ref(get_inner_ty(), current_modifier)?;
            let inner_expr = expr_to_vir_with_adjustments(
                bctx,
                expr,
                new_modifier,
                adjustments,
                adjustment_idx - 1,
            )?;
            let inner_ty = get_inner_ty();
            if bctx.ctxt.cmd_line_args.new_mut_ref
                && matches!(inner_ty.kind(), TyKind::Ref(_, _, rustc_ast::Mutability::Mut))
            {
                let t = match &*inner_expr.typ {
                    TypX::MutRef(t) => t.clone(),
                    _ => panic!("expected mut ref"),
                };
                Ok(bctx.spanned_typed_new(expr.span, &t, ExprX::DerefMut(inner_expr)))
            } else {
                Ok(strip_vir_ref_decoration(inner_expr))
            }
        }
        Adjust::Deref(Some(deref)) => {
            // note: deref has signature (&self) -> &Self::Target
            // and deref_mut has signature (&mut self) -> &mut Self::Target
            // The adjustment, though, goes from self -> Self::Target
            // without the refs.
            let inner = expr_to_vir_with_adjustments(
                bctx,
                expr,
                current_modifier,
                adjustments,
                adjustment_idx - 1,
            );
            if auto_deref_supported_for_ty(bctx.ctxt.tcx, &get_inner_ty()) {
                inner
            } else {
                crate::fn_call_to_vir::deref_to_vir(
                    bctx,
                    expr,
                    deref.method_call(bctx.ctxt.tcx),
                    inner?,
                    expr_typ()?,
                    get_inner_ty(),
                    expr.span,
                )
            }
        }
        Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Not)) => {
            // Similar to ExprKind::AddrOf
            let mut new_expr: Arc<SpannedTyped<vir::ast::ExprX>> = expr_to_vir_with_adjustments(
                bctx,
                expr,
                ExprModifier::REGULAR,
                adjustments,
                adjustment_idx - 1,
            )?;
            let typ =
                Arc::new(TypX::Decorate(vir::ast::TypDecoration::Ref, None, new_expr.typ.clone()));
            Arc::make_mut(&mut new_expr).typ = typ;
            Ok(new_expr)
        }
        Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Mut { .. })) => {
            if bctx.ctxt.cmd_line_args.new_mut_ref {
                // Rust often inserts &mut* adjustments in argument positions.
                // e.g., `foo(a)` where `a: &mut T` really becomes `foo(&mut *a)`.
                // (This is done to force a reborrow.)
                // We actually don't want this in spec contexts, so we detect this
                // case and skip it.
                if adjustment_idx >= 2
                    && matches!(&adjustments[adjustment_idx - 2].kind, Adjust::Deref(None))
                {
                    let inner_inner_ty = get_inner2_ty();
                    if inner_inner_ty != adjustment.target {
                        panic!("Verus Internal Error: Implicit &mut * expected the same type");
                    }
                    // TODO: we need to improve this condition to work for tracked code
                    if bctx.in_ghost {
                        return expr_to_vir_with_adjustments(
                            bctx,
                            expr,
                            current_modifier,
                            adjustments,
                            adjustment_idx - 2,
                        );
                    }
                }

                let e = expr_to_vir_with_adjustments(
                    bctx,
                    expr,
                    current_modifier,
                    adjustments,
                    adjustment_idx - 1,
                )?;
                let place = crate::places::expr_to_place_for_mut_ref(&e)?;
                let x = ExprX::BorrowMut(place);
                let typ = Arc::new(TypX::MutRef(e.typ.clone()));
                Ok(bctx.spanned_typed_new(expr.span, &typ, x))
            } else if current_modifier.deref_mut {
                // * &mut cancels out
                let mut new_modifier = current_modifier;
                new_modifier.deref_mut = false;
                expr_to_vir_with_adjustments(
                    bctx,
                    expr,
                    new_modifier,
                    adjustments,
                    adjustment_idx - 1,
                )
            } else {
                unsupported_err!(
                    expr.span,
                    format!(
                        "&mut dereference in this position (note: &mut dereference is implicit here)"
                    )
                )
            }
        }
        Adjust::Borrow(AutoBorrow::RawPtr(_)) => {
            // Despite the name 'borrow', the docs seem to indicate this is a dereference
            unsupported_err!(
                expr.span,
                "dereferencing a pointer (here the dereference is implicit)"
            )
        }
        Adjust::Pointer(PointerCoercion::Unsize) => {
            let ty1 = get_inner_ty();
            let ty2 = adjustment.target;

            if current_modifier.deref_mut != false || current_modifier.addr_of_mut != false {
                unsupported_err!(
                    expr.span,
                    format!("unsizing operation from `{ty1:}` to `{ty2:}`")
                );
            }

            let arg = expr_to_vir_with_adjustments(
                bctx,
                expr,
                current_modifier,
                adjustments,
                adjustment_idx - 1,
            )?;

            let f = match (ty1.kind(), ty2.kind()) {
                (TyKind::RawPtr(t1, _), TyKind::RawPtr(t2, _)) => {
                    match (t1.kind(), t2.kind()) {
                        (TyKind::Array(el_ty1, _const_len), TyKind::Slice(el_ty2)) => {
                            if el_ty1 == el_ty2 {
                                // coercing from *mut [el_ty, const_len] -> *mut [el_ty]
                                // (either *mut or *const is ok)
                                if bctx.ctxt.no_vstd {
                                    return err_span(
                                        expr.span,
                                        "Coercing an array to a slice is not supported with --no-vstd",
                                    );
                                }
                                let fun =
                                    vir::fun!("vstd" => "raw_ptr", "cast_array_ptr_to_slice_ptr");

                                let arg_typ = undecorate_typ(&arg.typ);
                                let array_typ = match &*arg_typ {
                                    TypX::Primitive(Primitive::Ptr, typs) => &typs[0],
                                    _ => {
                                        crate::internal_err!(expr.span, "expected Primitive::Ptr")
                                    }
                                };
                                let typ_args = match &*undecorate_typ(array_typ) {
                                    TypX::Primitive(Primitive::Array, typs) => typs.clone(),
                                    _ => {
                                        crate::internal_err!(expr.span, "expected array")
                                    }
                                };
                                Some((fun, typ_args))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                }
                _ => {
                    let (ty1, ty2) = remove_decoration_typs_for_unsizing(bctx.ctxt.tcx, ty1, ty2);
                    match (ty1.kind(), ty2.kind()) {
                        (TyKind::Array(el_ty1, _const_len), TyKind::Slice(el_ty2)) => {
                            if el_ty1 == el_ty2 {
                                // coercing from &[el_ty, const_len] -> &[el_ty]
                                if bctx.ctxt.no_vstd {
                                    return err_span(
                                        expr.span,
                                        "Coercing an array to a slice is not supported with --no-vstd",
                                    );
                                }
                                let fun = vir::fun!("vstd" => "array", "array_as_slice");
                                let typ_args = match &*undecorate_typ(&arg.typ) {
                                    TypX::Primitive(Primitive::Array, typs) => typs.clone(),
                                    _ => {
                                        crate::internal_err!(expr.span, "expected array")
                                    }
                                };
                                Some((fun, typ_args))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                }
            };

            if let Some((fun, typ_args)) = f {
                let autospec_usage =
                    if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };
                let call_target = CallTarget::Fun(
                    vir::ast::CallTargetKind::Static,
                    fun,
                    typ_args,
                    Arc::new(vec![]),
                    autospec_usage,
                );
                let args = Arc::new(vec![arg.clone()]);
                let x = ExprX::Call(call_target, args);
                let expr_typ = mid_ty_to_vir(
                    bctx.ctxt.tcx,
                    &bctx.ctxt.verus_items,
                    bctx.fun_id,
                    expr.span,
                    &ty2,
                    false,
                )?;
                Ok(bctx.spanned_typed_new(expr.span, &expr_typ, x))
            } else {
                unsupported_err!(
                    expr.span,
                    format!("unsizing operation from `{ty1:}` to `{ty2:}`")
                );
            }
        }
        Adjust::Pointer(PointerCoercion::MutToConstPointer) => {
            let mut new_expr: Arc<SpannedTyped<vir::ast::ExprX>> = expr_to_vir_with_adjustments(
                bctx,
                expr,
                ExprModifier::REGULAR,
                adjustments,
                adjustment_idx - 1,
            )?;
            let typ = Arc::new(TypX::Decorate(
                vir::ast::TypDecoration::ConstPtr,
                None,
                new_expr.typ.clone(),
            ));
            Arc::make_mut(&mut new_expr).typ = typ;
            Ok(new_expr)
        }
        Adjust::Pointer(_cast) => {
            unsupported_err!(expr.span, "casting a pointer (here the cast is implicit)")
        }
        Adjust::ReborrowPin(_mut) => {
            unsupported_err!(expr.span, "reborrowing a pinned reference")
        }
    }
}

enum OpKind {
    UnOp(rustc_hir::UnOp),
    BinOp(rustc_hir::BinOp),
    AssignOp(rustc_hir::AssignOp),
}

// Add lang_item_for_op from rust/compiler/rustc_hir_typeck/src/op.rs
// Returns the required traits to use op
// Note: comparison operators are defined only by PartialEq and PartialOrd
fn lang_item_for_op(
    tcx: TyCtxt<'_>,
    op: OpKind,
    span: Span,
) -> Result<(rustc_span::Symbol, Option<rustc_hir::def_id::DefId>), VirErr> {
    let lang = tcx.lang_items();
    use rustc_span::symbol::sym;
    let ret = match op {
        OpKind::AssignOp(op) => match op.node {
            AssignOpKind::AddAssign => (sym::add_assign, lang.add_assign_trait()),
            AssignOpKind::SubAssign => (sym::sub_assign, lang.sub_assign_trait()),
            AssignOpKind::MulAssign => (sym::mul_assign, lang.mul_assign_trait()),
            AssignOpKind::DivAssign => (sym::div_assign, lang.div_assign_trait()),
            AssignOpKind::RemAssign => (sym::rem_assign, lang.rem_assign_trait()),
            AssignOpKind::BitXorAssign => (sym::bitxor_assign, lang.bitxor_assign_trait()),
            AssignOpKind::BitAndAssign => (sym::bitand_assign, lang.bitand_assign_trait()),
            AssignOpKind::BitOrAssign => (sym::bitor_assign, lang.bitor_assign_trait()),
            AssignOpKind::ShlAssign => (sym::shl_assign, lang.shl_assign_trait()),
            AssignOpKind::ShrAssign => (sym::shr_assign, lang.shr_assign_trait()),
        },
        OpKind::BinOp(op) => match op.node {
            BinOpKind::Add => (sym::add, lang.add_trait()),
            BinOpKind::Sub => (sym::sub, lang.sub_trait()),
            BinOpKind::Mul => (sym::mul, lang.mul_trait()),
            BinOpKind::Div => (sym::div, lang.div_trait()),
            BinOpKind::Rem => (sym::rem, lang.rem_trait()),
            BinOpKind::BitXor => (sym::bitxor, lang.bitxor_trait()),
            BinOpKind::BitAnd => (sym::bitand, lang.bitand_trait()),
            BinOpKind::BitOr => (sym::bitor, lang.bitor_trait()),
            BinOpKind::Shl => (sym::shl, lang.shl_trait()),
            BinOpKind::Shr => (sym::shr, lang.shr_trait()),
            BinOpKind::Lt => (sym::lt, lang.partial_ord_trait()),
            BinOpKind::Le => (sym::le, lang.partial_ord_trait()),
            BinOpKind::Ge => (sym::ge, lang.partial_ord_trait()),
            BinOpKind::Gt => (sym::gt, lang.partial_ord_trait()),
            BinOpKind::Eq => (sym::eq, lang.eq_trait()), // PartialEq
            BinOpKind::Ne => (sym::ne, lang.eq_trait()), // PartialEq
            BinOpKind::And | BinOpKind::Or => {
                crate::internal_err!(span, "&& and || are not overloadable")
            }
        },
        OpKind::UnOp(op) => match op {
            UnOp::Not => (sym::not, lang.not_trait()),
            UnOp::Neg => (sym::neg, lang.neg_trait()),
            UnOp::Deref => {
                crate::internal_err!(span, "unexpected Deref")
            }
        },
    };
    Ok(ret)
}

/// Return None if we do not want to overload the operator.
/// We do not replace operators for some primitive types so that we still see
/// consistent errors for integer overflow/underflow.
fn operator_overload_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    current_modifier: ExprModifier,
) -> Result<Option<vir::ast::Expr>, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let span = expr.span;
    let (op, bin_args) = match expr.kind {
        ExprKind::Unary(UnOp::Deref, _) => {
            return Ok(None);
        }
        ExprKind::Unary(op @ (UnOp::Not | UnOp::Neg), arg) => {
            let ty = bctx.types.expr_ty_adjusted(arg);
            match ty.kind() {
                TyKind::Adt(_, _) | TyKind::Uint(_) | TyKind::Int(_) | TyKind::Bool => {
                    return Ok(None);
                }
                _ => {}
            }
            (OpKind::UnOp(op), None)
        }
        ExprKind::Binary(op, lhs, rhs) => {
            match op.node {
                BinOpKind::Eq | BinOpKind::Ne => {
                    if is_smt_equality(bctx, expr.span, &lhs.hir_id, &rhs.hir_id)? {
                        return Ok(None);
                    }
                }
                BinOpKind::Add
                | BinOpKind::Sub
                | BinOpKind::Mul
                | BinOpKind::BitXor
                | BinOpKind::BitAnd
                | BinOpKind::BitOr
                | BinOpKind::Shl
                | BinOpKind::Shr
                | BinOpKind::Le
                | BinOpKind::Ge
                | BinOpKind::Lt
                | BinOpKind::Gt => {
                    if is_smt_arith(bctx, lhs.span, rhs.span, &lhs.hir_id, &rhs.hir_id)? {
                        return Ok(None);
                    }
                }
                BinOpKind::Div | BinOpKind::Rem => {
                    if is_smt_arith(bctx, lhs.span, rhs.span, &lhs.hir_id, &rhs.hir_id)? {
                        let tc = bctx.types;
                        match mk_range(&bctx.ctxt.verus_items, &tc.node_type(expr.hir_id)) {
                            IntRange::I(_) | IntRange::ISize => {
                                // Let trait impls handle signed div/rem
                            }
                            _ => {
                                return Ok(None);
                            }
                        }
                    }
                }
                BinOpKind::And | BinOpKind::Or => {
                    return Ok(None);
                }
            };
            (OpKind::BinOp(op), Some((lhs, rhs)))
        }
        ExprKind::AssignOp(op, lhs, rhs) => {
            if is_smt_arith(bctx, lhs.span, rhs.span, &lhs.hir_id, &rhs.hir_id)? {
                return Ok(None);
            }
            // This should work, except for lacking external specifications
            (OpKind::AssignOp(op), Some((lhs, rhs)))
        }
        _ => return Ok(None),
    };

    let (trait_id, fun_sym, args, substs) = if let Some((lhs, rhs)) = bin_args {
        let (fun_sym, Some(trait_id)) = lang_item_for_op(tcx, op, span)? else {
            crate::internal_err!(span, "operator needs an accessible trait");
        };
        let lhs_ty = bctx.types.node_type(lhs.hir_id);
        let rhs_ty = bctx.types.node_type(rhs.hir_id);
        let substs = tcx.mk_args(&[lhs_ty.into(), rhs_ty.into()]);

        let args = vec![lhs, rhs];
        (trait_id, fun_sym, args, substs)
    } else if let ExprKind::Unary(_, arg) = expr.kind {
        let (fun_sym, Some(trait_id)) = lang_item_for_op(tcx, op, span)? else {
            crate::internal_err!(span, "Needs to import trait for operator");
        };

        let args = vec![arg];
        let arg_ty = bctx.types.node_type(arg.hir_id);
        let substs = tcx.mk_args(&[arg_ty.into()]);
        (trait_id, fun_sym, args, substs)
    } else {
        return Ok(None);
    };
    let Some(assoc_fn) = tcx
        .associated_items(trait_id)
        .filter_by_name_unhygienic(fun_sym)
        .find(|item| matches!(item.kind, rustc_middle::ty::AssocKind::Fn { .. }))
    else {
        panic!("could not find function");
    };
    let fun_def_id = assoc_fn.def_id;
    Ok(Some(fn_call_to_vir(
        bctx,
        expr,
        fun_def_id,
        substs,
        expr.span,
        args,
        current_modifier,
        true,
    )?))
}

/// Callers must guarantee that expr_vir is a vir representation of expr.
pub(crate) fn expr_cast_enum_int_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
    expr_vir: vir::ast::Expr,
    mk_expr: impl Fn(ExprX) -> Result<vir::ast::Expr, vir::messages::Message>,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let ty = bctx.types.node_type(expr.hir_id);
    assert!(ty.is_enum());

    if let ExprKind::Path(qpath) = &expr.kind {
        let res = bctx.types.qpath_res(&qpath, expr.hir_id);
        if let Some((ctor, CtorKind::Const)) = resolve_ctor(bctx.ctxt.tcx, res) {
            assert!(ctor.kind == AdtKind::Enum);
            let adt = tcx.adt_def(ctor.adt_def_id);
            let idx = adt.variant_index_with_id(ctor.variant_def.def_id);
            let val = adt.discriminant_for_variant(tcx, idx).val;
            return mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(val)));
        }
    }

    let TyKind::Adt(adt, _) = ty.kind() else {
        unreachable!();
    };
    let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
    for (idx, vdef) in adt.variants().iter_enumerated() {
        let val = adt.discriminant_for_variant(tcx, idx).val;
        let cast_to = mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(val)))?;
        unsupported_err_unless!(
            vdef.fields.len() == 0,
            expr.span,
            "Enum variant should not contain any fields."
        );
        let variant_name = vdef.name.to_string();
        let (adt_path, _) =
            crate::fn_call_to_vir::check_variant_field(bctx, expr.span, expr, &variant_name, None)?;

        let pattern = bctx.spanned_typed_new(
            expr.span,
            &expr_vir.typ,
            PatternX::Constructor(adt_path, Arc::new(variant_name), Arc::new(vec![])),
        );
        let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
        erasure_info.hir_vir_ids.push((expr.hir_id, pattern.span.id));
        let guard =
            bctx.spanned_typed_new(expr.span, &bool_typ(), ExprX::Const(Constant::Bool(true)));
        let body = cast_to;
        let vir_arm = bctx.spanned_new(expr.span, ArmX { pattern, guard, body });
        vir_arms.push(vir_arm);
    }
    unsupported_err_unless!(vir_arms.len() > 0, expr.span, "Zero-sized empty Enum expr");
    return Ok(mk_expr(ExprX::Match(expr_vir, Arc::new(vir_arms)))?);
}

pub(crate) fn expr_to_vir_innermost<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    current_modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let tc = bctx.types;
    let expr_typ = || {
        if current_modifier.deref_mut {
            typ_of_node_expect_mut_ref(bctx, expr.span, &expr.hir_id)
        } else {
            typ_of_node(bctx, expr.span, &expr.hir_id, false)
        }
    };
    let mk_expr = move |x: ExprX| Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, x));

    let modifier = ExprModifier { deref_mut: false, ..current_modifier };

    let mk_lit_int = |in_negative_literal: bool, i: u128, typ: Typ| {
        check_lit_int(&bctx.ctxt, expr.span, in_negative_literal, i, &typ)?;
        let c = vir::ast_util::const_int_from_u128(i);
        mk_expr(ExprX::Const(c))
    };

    let expr_attrs = bctx.ctxt.tcx.hir_attrs(expr.hir_id);
    let expr_vattrs = bctx.ctxt.get_verifier_attrs(expr_attrs)?;
    if expr_vattrs.truncate {
        if !match &expr.kind {
            ExprKind::Cast(_, _) => true,
            ExprKind::Call(target, _) => match &target.kind {
                ExprKind::Path(qpath) => {
                    let def = bctx.types.qpath_res(&qpath, expr.hir_id);
                    match def {
                        rustc_hir::def::Res::Def(_, def_id) => {
                            bctx.ctxt.verus_items.id_to_name.get(&def_id)
                                == Some(&VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger))
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        } {
            return err_span(
                expr.span,
                "the attribute #[verifier::truncate] is only allowed on casts (you may need parentheses around the cast)",
            );
        }
    }

    let loop_isolation = || {
        if let Some(flag) = expr_vattrs.loop_isolation {
            flag
        } else if let Some(flag) =
            crate::attributes::get_loop_isolation_walk_parents(bctx.ctxt.tcx, bctx.fun_id)
        {
            flag
        } else {
            true
        }
    };

    match &expr.kind {
        ExprKind::Block(body, _) => {
            if is_invariant_block(bctx, expr)? {
                invariant_block_to_vir(bctx, expr, modifier)
            } else if let Some(g_attr) = get_ghost_block_opt(bctx.ctxt.tcx.hir_attrs(expr.hir_id)) {
                let bctx = &BodyCtxt { in_ghost: true, ..bctx.clone() };
                let block = block_to_vir(bctx, body, &expr.span, &expr_typ()?, current_modifier);
                let tracked = match g_attr {
                    GhostBlockAttr::Proof => false,
                    GhostBlockAttr::Tracked => true,
                    GhostBlockAttr::GhostWrapped | GhostBlockAttr::TrackedWrapped => {
                        return block;
                    }
                    GhostBlockAttr::Wrapper => {
                        return err_span(expr.span, "unexpected ghost block wrapper");
                    }
                };
                mk_expr(ExprX::Ghost { alloc_wrapper: false, tracked, expr: block? })
            } else {
                let block = block_to_vir(bctx, body, &expr.span, &expr_typ()?, modifier);
                if crate::attributes::is_proof_in_spec(bctx.ctxt.tcx.hir_attrs(expr.hir_id)) {
                    mk_expr(ExprX::ProofInSpec(block?))
                } else {
                    block
                }
            }
        }
        ExprKind::Call(fun, args_slice) => {
            let res = match &fun.kind {
                ExprKind::Path(qpath) => {
                    let res = bctx.types.qpath_res(&qpath, fun.hir_id);
                    let ctor_opt = resolve_ctor(bctx.ctxt.tcx, res);
                    match (res, ctor_opt) {
                        (_, Some((ctor, CtorKind::Fn))) => Some(expr_tuple_datatype_ctor_to_vir(
                            bctx,
                            expr,
                            ctor,
                            *args_slice,
                            fun.span,
                            modifier,
                        )),
                        // a statically resolved function
                        (rustc_hir::def::Res::Def(_, def_id), _) => {
                            // this is necessary because we seemingly are skipping the deprecation check
                            // for free functions
                            tcx.check_stability(def_id, Some(expr.hir_id), expr.span, None);

                            let args = args_slice.iter().collect();
                            Some(fn_call_to_vir(
                                bctx,
                                expr,
                                def_id,
                                bctx.types.node_args(fun.hir_id),
                                fun.span,
                                args,
                                modifier,
                                false,
                            ))
                        }
                        (rustc_hir::def::Res::Local(_), _) => {
                            None // dynamically computed function, see below
                        }
                        _ => {
                            unsupported_err!(
                                expr.span,
                                format!("function call {:?} {:?}", res, expr)
                            )
                        }
                    }
                }
                _ => {
                    None // dynamically computed function, see below
                }
            };
            match res {
                Some(res) => res,
                None => {
                    // a dynamically computed function
                    if bctx.external_body {
                        return mk_expr(ExprX::Block(Arc::new(vec![]), None));
                    }

                    // For FnMut, Rust automatically inserts a mutable reference, e.g.,
                    // (&mut f).call(...)
                    // We currently don't encode this as a mutation on the caller's side, though.
                    // So here, we pretend to dereference the object if it's a mut reference.
                    let fun_ty = bctx.types.expr_ty_adjusted(fun);
                    let is_mut = match fun_ty.kind() {
                        TyKind::Ref(_, _, Mutability::Mut) => true,
                        _ => false,
                    };
                    let fun_modifier =
                        if is_mut { ExprModifier::DEREF_MUT } else { ExprModifier::REGULAR };
                    let vir_fun = expr_to_vir(bctx, fun, fun_modifier)?;

                    let args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();
                    let vir_args = vec_map_result(&args, |arg| expr_to_vir(bctx, arg, modifier))?;
                    let expr_typ = typ_of_node(bctx, expr.span, &expr.hir_id, false)?;

                    let proof_fn = crate::rust_to_vir_base::try_get_proof_fn_modes(
                        &bctx.ctxt, expr.span, &fun_ty,
                    )?;
                    let is_proof_fun = proof_fn.is_some();
                    let is_spec_fn = match &*undecorate_typ(&vir_fun.typ) {
                        TypX::SpecFn(..) => true,
                        _ => false,
                    };

                    let (target, vir_args, resolved_call) = if is_spec_fn {
                        (CallTarget::FnSpec(vir_fun), vir_args, ResolvedCall::Spec)
                    } else {
                        if bctx.ctxt.no_vstd {
                            return err_span(
                                expr.span,
                                "Non-static calls are not supported with --no-vstd",
                            );
                        }

                        // non-static calls are translated into a static call to
                        // `exec_nonstatic_call` which is defined in the vstd lib.
                        let span = bctx.ctxt.spans.to_air_span(expr.span.clone());
                        let tup = vir::ast_util::mk_tuple(&span, &Arc::new(vir_args));
                        let helper_fun =
                            vir::def::nonstatic_call_fun(&bctx.ctxt.vstd_crate_name, is_proof_fun);
                        let ret_typ = expr_typ.clone();

                        // Anything that goes in `typ_args` needs to have the correct
                        // decoration, so call mid_ty_to_vir for these
                        // Compute `tup_typ` with the correct decoration:
                        let mut arg_typs = vec![];
                        for arg in args.iter() {
                            arg_typs.push(mid_ty_to_vir(
                                tcx,
                                &bctx.ctxt.verus_items,
                                bctx.fun_id,
                                arg.span,
                                &bctx.types.expr_ty_adjusted(arg),
                                false,
                            )?);
                        }
                        let tup_typ = mk_tuple_typ(&Arc::new(arg_typs));

                        // Compute fun_typ with the correct decoration
                        // (technically not needed since the fun_typ decoration gets
                        // ignored later, but for consistency with other typ_args I
                        // decided to get the decorated version)
                        // Also, allow &mut refs here since that can happen for FnMut.
                        let fun_typ = mid_ty_to_vir(
                            tcx,
                            &bctx.ctxt.verus_items,
                            bctx.fun_id,
                            fun.span,
                            &fun_ty,
                            true,
                        )?;

                        let (kind, rcall) = if let Some((arg_modes, ret_mode)) = proof_fn {
                            if arg_modes.len() != args.len() {
                                return err_span(
                                    expr.span,
                                    "could not read mode annotations from proof_fn type",
                                );
                            }
                            let arg_modes = Arc::new(arg_modes);
                            let r = ResolvedCall::NonStaticProof(arg_modes.clone());
                            let k = vir::ast::CallTargetKind::ProofFn(arg_modes, ret_mode);
                            (k, r)
                        } else {
                            (vir::ast::CallTargetKind::Static, ResolvedCall::NonStaticExec)
                        };

                        // Get impl_paths for the trait bound
                        // fun_ty : FnOnce<Args>
                        let generic_arg0 = GenericArg::from(fun_ty);
                        let generic_arg1 = GenericArg::from(
                            tcx.mk_ty_from_kind(TyKind::Tuple(
                                tcx.mk_type_list(
                                    &args
                                        .iter()
                                        .map(|arg| bctx.types.expr_ty_adjusted(arg))
                                        .collect::<Vec<_>>(),
                                ),
                            )),
                        );
                        let clause =
                            rustc_middle::ty::Binder::dummy(ClauseKind::Trait(TraitPredicate {
                                trait_ref: TraitRef::new(
                                    tcx,
                                    tcx.lang_items().fn_once_trait().unwrap(),
                                    [generic_arg0, generic_arg1],
                                ),
                                polarity: rustc_middle::ty::PredicatePolarity::Positive,
                            }))
                            .upcast(tcx);
                        let impl_paths = get_impl_paths_for_clauses(
                            tcx,
                            &bctx.ctxt.verus_items,
                            bctx.fun_id,
                            vec![(None, clause)],
                            None,
                        );

                        let typ_args = Arc::new(vec![tup_typ, ret_typ, fun_typ]);
                        (
                            CallTarget::Fun(
                                kind,
                                helper_fun,
                                typ_args,
                                impl_paths,
                                AutospecUsage::Final,
                            ),
                            vec![vir_fun, tup],
                            rcall,
                        )
                    };

                    {
                        let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                        erasure_info.resolved_calls.push((
                            expr.hir_id,
                            fun.span.data(),
                            resolved_call,
                        ));
                    }

                    Ok(bctx.spanned_typed_new(
                        expr.span,
                        &expr_typ,
                        ExprX::Call(target, Arc::new(vir_args)),
                    ))
                }
            }
        }
        ExprKind::Tup(exprs) => {
            let args: Result<Vec<vir::ast::Expr>, VirErr> =
                exprs.iter().map(|e| expr_to_vir(bctx, e, modifier)).collect();
            mk_expr(mk_tuple_x(&Arc::new(args?)))
        }
        ExprKind::Array(exprs) => {
            if bctx.ctxt.no_vstd {
                return err_span(expr.span, "Array literals are not supported with --no-vstd");
            }
            let args: Result<Vec<vir::ast::Expr>, VirErr> =
                exprs.iter().map(|e| expr_to_vir(bctx, e, modifier)).collect();
            mk_expr(ExprX::ArrayLiteral(Arc::new(args?)))
        }
        ExprKind::Repeat(e, _array_len) => {
            if bctx.ctxt.no_vstd {
                return err_span(expr.span, "Array literals are not supported with --no-vstd");
            }
            let ty = bctx.types.expr_ty_adjusted(e);
            let is_copy =
                tcx.type_is_copy_modulo_regions(TypingEnv::post_analysis(tcx, bctx.fun_id), ty);
            if is_copy {
                let arg_vir = expr_to_vir(bctx, e, modifier)?;
                let fun = vir::fun!("vstd" => "array", "array_fill_for_copy_types");
                let array_vir_typ = mid_ty_to_vir(
                    bctx.ctxt.tcx,
                    &bctx.ctxt.verus_items,
                    bctx.fun_id,
                    expr.span,
                    &bctx.types.expr_ty(expr),
                    false,
                )?;
                let typ_args = match &*array_vir_typ {
                    TypX::Primitive(Primitive::Array, typs) => typs.clone(),
                    _ => {
                        crate::internal_err!(expr.span, "expected Primitive::Array")
                    }
                };
                let autospec_usage =
                    if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };
                let call_target = CallTarget::Fun(
                    vir::ast::CallTargetKind::Static,
                    fun,
                    typ_args,
                    Arc::new(vec![]),
                    autospec_usage,
                );
                let args = Arc::new(vec![arg_vir.clone()]);
                mk_expr(ExprX::Call(call_target, args))
            } else {
                // Could be a const. In this case the array needs to be translated like:
                //    forall |i| array[i] satisfies post-condition of const
                unsupported_err!(expr.span, format!("array-fill expresion with non-copy type"))
            }
        }
        ExprKind::Lit(lit) => lit_to_vir(
            bctx,
            expr.span,
            lit,
            false,
            &typ_of_node(bctx, expr.span, &expr.hir_id, false)?,
            Some(bctx.types.node_type(expr.hir_id)),
        ),
        ExprKind::Cast(source, _) => {
            let source_vir = expr_to_vir(bctx, source, modifier)?;

            if let Some(expr) = maybe_do_ptr_cast(bctx, expr, source, &source_vir)? {
                return Ok(expr);
            }

            let source_vir_ty = &source_vir.typ;
            let to_vir_ty = expr_typ()?;
            match (&*undecorate_typ(source_vir_ty), &*undecorate_typ(&to_vir_ty)) {
                (TypX::Int(_), TypX::Int(_)) => {
                    Ok(mk_ty_clip(&to_vir_ty, &source_vir, expr_vattrs.truncate))
                }
                (TypX::Bool, TypX::Int(_)) => {
                    let zero = mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(0)))?;
                    let one = mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(1)))?;
                    mk_expr(ExprX::If(source_vir, one, Some(zero)))
                }
                (_, TypX::Int(_)) if bctx.types.node_type(source.hir_id).is_enum() => {
                    let cast_to = expr_cast_enum_int_to_vir(bctx, source, source_vir, mk_expr)?;
                    Ok(mk_ty_clip(&to_vir_ty, &cast_to, expr_vattrs.truncate))
                }
                _ => {
                    let source_ty = bctx.types.expr_ty_adjusted(source);
                    let to_ty = bctx.types.expr_ty(expr);
                    return err_span(
                        expr.span,
                        format!(
                            "Verus does not support this cast: `{:#?}` to `{:#?}`",
                            source_ty, to_ty
                        ),
                    );
                }
            }
        }
        ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, e) => {
            let mut new_expr = expr_to_vir_inner(bctx, e, ExprModifier::REGULAR)?;
            let typ = &mut Arc::make_mut(&mut new_expr).typ;
            *typ = Arc::new(TypX::Decorate(vir::ast::TypDecoration::Ref, None, typ.clone()));
            Ok(new_expr)
        }
        ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e) => {
            if bctx.ctxt.cmd_line_args.new_mut_ref {
                let e = expr_to_vir(bctx, e, modifier)?;
                let place = crate::places::expr_to_place_for_mut_ref(&e)?;
                let x = ExprX::BorrowMut(place);
                let typ = Arc::new(TypX::MutRef(e.typ.clone()));
                Ok(bctx.spanned_typed_new(expr.span, &typ, x))
            } else if current_modifier.deref_mut {
                // * &mut cancels out
                let mut new_modifier = current_modifier;
                new_modifier.deref_mut = false;
                expr_to_vir_inner(bctx, e, new_modifier)
            } else {
                unsupported_err!(expr.span, format!("&mut dereference in this position"))
            }
        }
        ExprKind::AddrOf(BorrowKind::Raw, _, _) => {
            unsupported_err!(expr.span, format!("raw borrows"))
        }
        ExprKind::OffsetOf(_container, _fields) => {
            unsupported_err!(expr.span, format!("offset_of!()"))
        }
        ExprKind::Unary(op, arg) => match op {
            UnOp::Not => {
                let ty = tc.expr_ty_adjusted(arg);
                let not_op = match ty.kind() {
                    TyKind::Adt(_, _) | TyKind::Uint(_) | TyKind::Int(_) => {
                        let (Some(w), s) = bitwidth_and_signedness_of_integer_type(
                            &bctx.ctxt.verus_items,
                            bctx.types.expr_ty(expr),
                        ) else {
                            return err_span(
                                expr.span,
                                "expected bool or finite integer width for !",
                            );
                        };
                        UnaryOp::BitNot(if s { None } else { Some(w) })
                    }
                    TyKind::Bool => UnaryOp::Not,
                    _ => {
                        let ret = operator_overload_to_vir(bctx, expr, modifier)?;
                        if ret.is_some() {
                            return Ok(ret.unwrap());
                        }
                        unsupported_err!(
                            expr.span,
                            format!("applying `!` operator to type {:}", ty)
                        )
                    }
                };
                let varg = expr_to_vir(bctx, arg, modifier)?;
                mk_expr(ExprX::Unary(not_op, varg))
            }
            UnOp::Neg => {
                let zero_const = vir::ast_util::const_int_from_u128(0);
                let zero = mk_expr(ExprX::Const(zero_const))?;
                let varg = if let ExprKind::Lit(Spanned { node: LitKind::Int(i, _), .. }) =
                    &arg.kind
                {
                    mk_lit_int(true, i.get(), typ_of_node(bctx, expr.span, &expr.hir_id, false)?)?
                } else if let ExprKind::Lit(lit @ Spanned { node: LitKind::Float(..), .. }) =
                    &arg.kind
                {
                    return lit_to_vir(
                        bctx,
                        expr.span,
                        lit,
                        true,
                        &typ_of_node(bctx, expr.span, &arg.hir_id, false)?,
                        Some(bctx.types.node_type(arg.hir_id)),
                    );
                } else {
                    expr_to_vir(bctx, arg, modifier)?
                };
                let mode_for_ghostness = if bctx.in_ghost { Mode::Spec } else { Mode::Exec };
                mk_expr(ExprX::Binary(
                    BinaryOp::Arith(ArithOp::Sub, mode_for_ghostness),
                    zero,
                    varg,
                ))
            }
            UnOp::Deref => deref_expr_to_vir(bctx, expr, arg, modifier),
        },
        ExprKind::Binary(op, lhs, rhs) => {
            let vlhs = expr_to_vir(bctx, lhs, modifier)?;
            let vrhs = expr_to_vir(bctx, rhs, modifier)?;
            let ret = operator_overload_to_vir(bctx, expr, modifier)?;
            if ret.is_some() {
                return Ok(ret.unwrap());
            }
            let mode_for_ghostness = if bctx.in_ghost { Mode::Spec } else { Mode::Exec };
            let vop = binopkind_to_binaryop(bctx, op, tc, lhs, rhs, mode_for_ghostness)?;
            let e = mk_expr(ExprX::Binary(vop, vlhs, vrhs))?;
            match op.node {
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul => {
                    Ok(mk_ty_clip(&expr_typ()?, &e, true))
                }
                BinOpKind::Div | BinOpKind::Rem => {
                    match mk_range(&bctx.ctxt.verus_items, &tc.node_type(expr.hir_id)) {
                        IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::USize => {
                            // Euclidean division
                            Ok(mk_ty_clip(&expr_typ()?, &e, true))
                        }
                        IntRange::I(_) | IntRange::ISize => {
                            // Handled by operator_overload_to_vir
                            unreachable!("signed fixed-width div/mod handled by traits")
                        }
                        IntRange::Char => {
                            unsupported_err!(expr.span, "div/mod on char type")
                        }
                    }
                }
                _ => Ok(e),
            }
        }
        ExprKind::Path(qpath) => {
            let res = bctx.types.qpath_res(&qpath, expr.hir_id);
            let ctor_opt = resolve_ctor(bctx.ctxt.tcx, res);
            match (res, ctor_opt) {
                (Res::Local(id), _) => match tcx.hir_node(id) {
                    Node::Pat(pat) => mk_expr(if modifier.addr_of_mut {
                        ExprX::VarLoc(pat_to_var(pat)?)
                    } else {
                        ExprX::Var(pat_to_var(pat)?)
                    }),
                    node => unsupported_err!(expr.span, format!("Path {:?}", node)),
                },
                (_, Some((ctor, ctor_kind))) => {
                    if ctor_kind != CtorKind::Const {
                        unsupported_err!(
                            expr.span,
                            "using a datatype constructor as a function value"
                        );
                    }
                    expr_tuple_datatype_ctor_to_vir(bctx, expr, ctor, &[], expr.span, modifier)
                }
                (Res::Def(DefKind::AssocConst, id), _) => {
                    if let Some(vir_expr) =
                        int_intrinsic_constant_to_vir(&bctx.ctxt, expr.span, &expr_typ()?, id)
                    {
                        let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                        erasure_info.resolved_calls.push((
                            expr.hir_id,
                            expr.span.data(),
                            ResolvedCall::CompilableOperator(CompilableOperator::IntIntrinsic),
                        ));
                        return Ok(vir_expr);
                    } else {
                        let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, id);
                        let fun = FunX { path };
                        let autospec_usage = if bctx.in_ghost {
                            AutospecUsage::IfMarked
                        } else {
                            AutospecUsage::Final
                        };
                        mk_expr(ExprX::ConstVar(Arc::new(fun), autospec_usage))
                    }
                }
                (Res::Def(DefKind::Const, id), _) => {
                    let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, id);
                    let fun = FunX { path };
                    let autospec_usage =
                        if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };
                    mk_expr(ExprX::ConstVar(Arc::new(fun), autospec_usage))
                }
                (
                    Res::Def(
                        DefKind::Static { mutability: Mutability::Not, nested: false, .. },
                        id,
                    ),
                    _,
                ) => {
                    let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, id);
                    let fun = FunX { path };
                    mk_expr(ExprX::StaticVar(Arc::new(fun)))
                }
                (Res::Def(DefKind::Fn, id) | Res::Def(DefKind::AssocFn, id), _) => {
                    let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, id);
                    let fun = Arc::new(vir::ast::FunX { path });
                    mk_expr(ExprX::ExecFnByName(fun))
                }
                (Res::Def(DefKind::ConstParam, id), _) => {
                    let gparam = if let Some(local_id) = id.as_local() {
                        let hir_id = tcx.local_def_id_to_hir_id(local_id);
                        match tcx.hir_node(hir_id) {
                            Node::GenericParam(rustc_hir::GenericParam {
                                name,
                                kind: rustc_hir::GenericParamKind::Const { .. },
                                ..
                            }) => Some(name),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    match *undecorate_typ(&expr_typ()?) {
                        TypX::Int(_) => {}
                        TypX::Bool => {}
                        _ => {
                            unsupported_err!(expr.span, format!("non-int ConstParam {:?}", id))
                        }
                    }
                    if let Some(name) = gparam {
                        let typ = Arc::new(TypX::TypParam(Arc::new(name.ident().to_string())));
                        let opr = vir::ast::NullaryOpr::ConstGeneric(typ);
                        mk_expr(ExprX::NullaryOpr(opr))
                    } else {
                        unsupported_err!(expr.span, format!("ConstParam {:?}", id))
                    }
                }
                (res, _) => unsupported_err!(expr.span, format!("Path {:?}", res)),
            }
        }
        ExprKind::Assign(lhs, rhs, _) => {
            expr_assign_to_vir_innermost(bctx, tc, lhs, mk_expr, rhs, modifier, None)
        }
        ExprKind::Field(lhs, name) => {
            let lhs_modifier = is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(lhs), modifier)?;
            let vir_lhs = expr_to_vir(bctx, lhs, lhs_modifier)?;
            let lhs_ty = tc.expr_ty_adjusted(lhs);
            let lhs_ty = mid_ty_simplify(tcx, &bctx.ctxt.verus_items, &lhs_ty, true);
            let (datatype, variant_name, field_name, check) = if let Some(adt_def) =
                lhs_ty.ty_adt_def()
            {
                unsupported_err_unless!(
                    current_modifier == ExprModifier::REGULAR || !adt_def.is_union(),
                    expr.span,
                    "assigning to or taking &mut of a union field",
                    expr
                );
                unsupported_err_unless!(
                    adt_def.variants().len() == 1,
                    expr.span,
                    "field_of_adt_with_multiple_variants",
                    expr
                );
                let datatype_path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, adt_def.did());
                let hir_def = bctx.ctxt.tcx.adt_def(adt_def.did());
                let variant = hir_def.variants().iter().next().unwrap();
                let field_name = field_ident_from_rust(&name.as_str());
                match variant.ctor_kind() {
                    Some(rustc_hir::def::CtorKind::Fn) => {}
                    None => {}
                    Some(rustc_hir::def::CtorKind::Const) => panic!("unexpected tuple constructor"),
                }
                let variant_name = if adt_def.is_union() {
                    str_ident(name.as_str())
                } else {
                    str_ident(&variant.ident(tcx).as_str())
                };
                let check = if adt_def.is_union() { VariantCheck::Yes } else { VariantCheck::None };
                (datatype_path, variant_name, field_name, check)
            } else {
                let lhs_typ = typ_of_node(bctx, lhs.span, &lhs.hir_id, true)?;
                let lhs_typ = undecorate_typ(&lhs_typ);
                if let TypX::Datatype(Dt::Tuple(_), ts, _) = &*lhs_typ {
                    let field: usize =
                        str::parse(&name.as_str()).expect("integer index into tuple");
                    let vir = mk_expr(mk_tuple_field_x(&vir_lhs, ts.len(), field))?;
                    return Ok(vir);
                }
                unsupported_err!(expr.span, "field_of_non_adt", expr)
            };
            let field_type = expr_typ()?.clone();
            let vir = bctx.spanned_typed_new(
                expr.span,
                &field_type,
                ExprX::UnaryOpr(
                    UnaryOpr::Field(FieldOpr {
                        datatype: Dt::Path(datatype),
                        variant: variant_name,
                        field: field_name,
                        get_variant: false,
                        check,
                    }),
                    vir_lhs,
                ),
            );
            Ok(vir)
        }
        ExprKind::If(cond, lhs, rhs) => {
            let cond = cond.peel_drop_temps();
            match cond.kind {
                ExprKind::Let(LetExpr { pat, init: expr, ty: _, span: _, recovered: _ }) => {
                    // if let
                    let vir_expr = expr_to_vir(bctx, expr, modifier)?;
                    let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
                    /* lhs */
                    {
                        let pattern = pattern_to_vir(bctx, pat)?;
                        let guard = bctx.spanned_typed_new(
                            expr.span,
                            &bool_typ(),
                            ExprX::Const(Constant::Bool(true)),
                        );
                        let body = expr_to_vir(bctx, &lhs, modifier)?;
                        let vir_arm = ArmX { pattern, guard, body };
                        vir_arms.push(bctx.spanned_new(lhs.span, vir_arm));
                    }
                    /* rhs */
                    {
                        let pat_typ = typ_of_node(bctx, pat.span, &pat.hir_id, false)?;
                        let pattern =
                            bctx.spanned_typed_new(cond.span, &pat_typ, PatternX::Wildcard(false));
                        {
                            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                            erasure_info.hir_vir_ids.push((cond.hir_id, pattern.span.id));
                        }
                        let guard = bctx.spanned_typed_new(
                            expr.span,
                            &bool_typ(),
                            ExprX::Const(Constant::Bool(true)),
                        );
                        let body = if let Some(rhs) = rhs {
                            expr_to_vir(bctx, &rhs, modifier)?
                        } else {
                            mk_expr(ExprX::Block(Arc::new(Vec::new()), None))?
                        };
                        let vir_arm = ArmX { pattern, guard, body };
                        vir_arms.push(bctx.spanned_new(lhs.span, vir_arm));
                    }
                    mk_expr(ExprX::Match(vir_expr, Arc::new(vir_arms)))
                }
                _ => {
                    let vir_cond = expr_to_vir(bctx, cond, modifier)?;
                    let vir_lhs = expr_to_vir(bctx, lhs, modifier)?;
                    let vir_rhs = rhs.map(|e| expr_to_vir(bctx, e, modifier)).transpose()?;
                    mk_expr(ExprX::If(vir_cond, vir_lhs, vir_rhs))
                }
            }
        }
        ExprKind::Match(expr, arms, _match_source) => {
            let vir_expr = expr_to_vir(bctx, expr, modifier)?;
            let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
            for arm in arms.iter() {
                let pattern = pattern_to_vir(bctx, &arm.pat)?;
                let guard = match &arm.guard {
                    None => bctx.spanned_typed_new(
                        expr.span,
                        &bool_typ(),
                        ExprX::Const(Constant::Bool(true)),
                    ),
                    Some(guard_expr) => expr_to_vir(bctx, guard_expr, modifier)?,
                };
                let body = expr_to_vir(bctx, &arm.body, modifier)?;
                let vir_arm = ArmX { pattern, guard, body };
                vir_arms.push(bctx.spanned_new(arm.span, vir_arm));
            }
            mk_expr(ExprX::Match(vir_expr, Arc::new(vir_arms)))
        }
        ExprKind::Loop(block, label, LoopSource::Loop, header_span) => {
            let loop_isolation = loop_isolation();
            let bctx = &BodyCtxt { loop_isolation, ..bctx.clone() };
            let typ = typ_of_node(bctx, block.span, &block.hir_id, false)?;
            let mut body = block_to_vir(bctx, block, &expr.span, &typ, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut body, &vir::headers::HeaderAllows::Loop)?;
            let label = label.map(|l| l.ident.to_string());
            use crate::attributes::get_allow_exec_allows_no_decreases_clause_walk_parents;
            let allow_no_decreases =
                get_allow_exec_allows_no_decreases_clause_walk_parents(bctx.ctxt.tcx, bctx.fun_id);
            let decrease = if expr_vattrs.auto_decreases && allow_no_decreases {
                Arc::new(vec![])
            } else {
                header.decrease.clone()
            };
            Ok(bctx.spanned_typed_new(
                *header_span,
                &expr_typ()?,
                ExprX::Loop {
                    loop_isolation,
                    is_for_loop: expr_vattrs.for_loop,
                    label,
                    cond: None,
                    body,
                    invs: header.loop_invariants(),
                    decrease,
                },
            ))
        }
        ExprKind::Loop(
            Block {
                stmts: [], expr: Some(Expr { kind: ExprKind::If(cond, body, other), .. }), ..
            },
            label,
            LoopSource::While,
            header_span,
        ) => {
            // rustc desugars a while loop of the form `while cond { body }`
            // to `loop { if cond { body } else { break; } }`
            // We want to "un-desugar" it to represent it as a while loop.
            // (We also need to retrieve the invariants from the body inside the If.)
            // We already got `body` from the if-branch; now sanity check that the
            // 'else' branch really has a 'break' statement as expected.
            if let Some(Expr {
                kind:
                    ExprKind::Block(
                        Block {
                            stmts:
                                [
                                    Stmt {
                                        kind:
                                            StmtKind::Expr(Expr {
                                                kind:
                                                    ExprKind::Break(
                                                        Destination { label: None, .. },
                                                        None,
                                                    ),
                                                ..
                                            }),
                                        ..
                                    },
                                ],
                            expr: None,
                            ..
                        },
                        None,
                    ),
                ..
            }) = other
            {
            } else {
                unsupported_err!(expr.span, "loop else");
            }
            assert!(modifier == ExprModifier::REGULAR);
            let cond = Some(expr_to_vir(bctx, cond, ExprModifier::REGULAR)?);
            let mut body = expr_to_vir(bctx, body, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut body, &vir::headers::HeaderAllows::Loop)?;
            let label = label.map(|l| l.ident.to_string());
            Ok(bctx.spanned_typed_new(
                *header_span,
                &expr_typ()?,
                ExprX::Loop {
                    loop_isolation: loop_isolation(),
                    is_for_loop: false,
                    label,
                    cond,
                    body,
                    invs: header.loop_invariants(),
                    decrease: header.decrease,
                },
            ))
        }
        ExprKind::Ret(expr) => {
            let expr = match expr {
                None => None,
                Some(expr) => Some(expr_to_vir(bctx, expr, modifier)?),
            };
            mk_expr(ExprX::Return(expr))
        }
        ExprKind::Break(dest, None) => {
            let label = dest.label.map(|l| l.ident.to_string());
            mk_expr(ExprX::BreakOrContinue { label, is_break: true })
        }
        ExprKind::Continue(dest) => {
            let label = dest.label.map(|l| l.ident.to_string());
            mk_expr(ExprX::BreakOrContinue { label, is_break: false })
        }
        ExprKind::Struct(qpath, fields, struct_tail) => {
            let update = match struct_tail {
                // Some(update) => Some(expr_to_vir(bctx, update, modifier)?),
                StructTailExpr::Base(expr) => Some(expr_to_vir(bctx, expr, modifier)?),
                StructTailExpr::DefaultFields(..) => {
                    unsupported_err!(
                        expr.span,
                        "default fields in struct expression not supported"
                    );
                }
                _ => None,
            };

            let res = bctx.types.qpath_res(qpath, expr.hir_id);
            let ty = bctx.types.node_type(expr.hir_id);
            let ctor = resolve_braces_ctor(bctx.ctxt.tcx, res, ty, true, expr.span)?;
            let variant_name = ctor.variant_name(bctx.ctxt.tcx, fields);
            let path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, ctor.adt_def_id);

            let vir_fields = Arc::new(
                fields
                    .iter()
                    .map(|f| -> Result<_, VirErr> {
                        let vir = expr_to_vir(bctx, f.expr, modifier)?;
                        let ident = field_ident_from_rust(f.ident.as_str());
                        Ok(ident_binder(&ident, &vir))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );

            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
            let resolved_call = ResolvedCall::BracesCtor(
                path.clone(),
                variant_name.clone(),
                Arc::new(vir_fields.iter().map(|f| f.name.clone()).collect::<Vec<_>>()),
                update.is_some(),
            );
            erasure_info.resolved_calls.push((expr.hir_id, expr.span.data(), resolved_call));
            mk_expr(ExprX::Ctor(Dt::Path(path), variant_name, vir_fields, update))
        }
        ExprKind::MethodCall(_name_and_generics, receiver, other_args, fn_span) => {
            let fn_def_id = bctx
                .types
                .type_dependent_def_id(expr.hir_id)
                .expect("def id of the method definition");

            let all_args = std::iter::once(*receiver).chain(other_args.iter()).collect::<Vec<_>>();
            fn_call_to_vir(
                bctx,
                expr,
                fn_def_id,
                bctx.types.node_args(expr.hir_id),
                *fn_span,
                all_args,
                modifier,
                true,
            )
        }
        ExprKind::Closure(Closure { fn_decl: _, .. }) => {
            closure_to_vir(bctx, expr, expr_typ()?, false, None, modifier)
        }
        ExprKind::Index(tgt_expr, idx_expr, _span) => {
            // Determine if this is Index or IndexMut
            // Based on ./rustc_mir_build/src/thir/cx/expr.rs in rustc
            // this is apparently determined by the (adjusted) type of the receiver
            let tgt_ty = bctx.types.expr_ty_adjusted(tgt_expr);
            let is_index_mut = match tgt_ty.kind() {
                TyKind::Array(_, _) => false,
                TyKind::Slice(_) => false,
                TyKind::Ref(_, _, Mutability::Not) => false,
                TyKind::Ref(_, _, Mutability::Mut) => true,
                _ => {
                    crate::internal_err!(expr.span, "index operator expected & or &mut")
                }
            };
            if is_index_mut || current_modifier != ExprModifier::REGULAR {
                unsupported_err!(expr.span, "index for &mut not supported")
            }

            let tgt_vir = expr_to_vir(bctx, tgt_expr, modifier)?;
            let idx_vir = expr_to_vir(bctx, idx_expr, ExprModifier::REGULAR)?;

            // We only support for the special case of (Vec, usize) arguments
            let t1 = &tgt_vir.typ;
            let t1 = match &**t1 {
                TypX::Decorate(_, _, t) => t,
                _ => t1,
            };
            let (fun, typ_args) = match &**t1 {
                TypX::Datatype(Dt::Path(p), typ_args, _impl_paths)
                    if p == &vir::path!("alloc" => "vec", "Vec") =>
                {
                    let fun = vir::fun!("vstd" => "std_specs", "vec", "vec_index");
                    (fun, typ_args.clone())
                }
                TypX::Primitive(vir::ast::Primitive::Array, typ_args) => {
                    let fun = vir::fun!("vstd" => "array", "array_index_get");
                    (fun, typ_args.clone())
                }
                TypX::Primitive(vir::ast::Primitive::Slice, typ_args) => {
                    let fun = vir::fun!("vstd" => "slice", "slice_index_get");
                    (fun, typ_args.clone())
                }
                _ => {
                    return err_span(
                        expr.span,
                        "in exec code, Verus only supports the index operator for Vec, array, and slice types",
                    );
                }
            };
            if !matches!(&*idx_vir.typ, TypX::Int(IntRange::USize)) {
                return Err(err_span_bare(
                    expr.span,
                    "in exec code, the index operator is only supported for usize index",
                )
                .secondary_label(
                    &err_air_span(idx_expr.span),
                    format!("expected usize, found {}", typ_to_diagnostic_str(&idx_vir.typ)),
                ));
            }

            let call_target = CallTarget::Fun(
                vir::ast::CallTargetKind::Static,
                fun,
                typ_args,
                // arbitrary impl_path
                // REVIEW: why is this needed?
                Arc::new(vec![ImplPath::TraitImplPath(vir::def::prefix_spec_fn_type(0))]),
                AutospecUsage::Final,
            );
            let args = Arc::new(vec![tgt_vir.clone(), idx_vir.clone()]);
            mk_expr(ExprX::Call(call_target, args))
        }
        ExprKind::Loop(..) => unsupported_err!(expr.span, format!("complex loop expressions")),
        ExprKind::Break(..) => unsupported_err!(expr.span, format!("complex break expressions")),
        ExprKind::AssignOp(op, lhs, rhs) => {
            if matches!(op.node, AssignOpKind::DivAssign | AssignOpKind::RemAssign) {
                let range = mk_range(&bctx.ctxt.verus_items, &tc.expr_ty_adjusted(lhs));
                if matches!(range, IntRange::I(_) | IntRange::ISize) {
                    // Non-Euclidean division, which will need more encoding
                    unsupported_err!(expr.span, "div/mod on signed finite-width integers");
                }
            }
            expr_assign_to_vir_innermost(bctx, tc, lhs, mk_expr, rhs, modifier, Some(op))
        }
        ExprKind::ConstBlock(..) => unsupported_err!(expr.span, format!("const block expressions")),
        ExprKind::Type(..) => unsupported_err!(expr.span, format!("type expressions")),
        ExprKind::DropTemps(..) => unsupported_err!(expr.span, format!("drop-temps expressions")),
        ExprKind::Let(..) => unsupported_err!(expr.span, format!("let expressions")),
        ExprKind::Yield(..) => unsupported_err!(expr.span, format!("yield expressions")),
        ExprKind::InlineAsm(..) => unsupported_err!(expr.span, format!("inline-asm expressions")),
        ExprKind::Err(..) => unsupported_err!(expr.span, format!("Err expressions")),
        ExprKind::Become(..) => unsupported_err!(expr.span, format!("Become expressions")),
        ExprKind::UnsafeBinderCast(..) => {
            unsupported_err!(expr.span, format!("unsafe binder cast"))
        }
        ExprKind::Use(..) => unsupported_err!(expr.span, "use expressions"),
    }
}

fn lit_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    lit: &'tcx Lit,
    negated: bool,
    typ: &Typ,
    ty: Option<rustc_middle::ty::Ty<'tcx>>,
) -> Result<vir::ast::Expr, VirErr> {
    let mk_expr = move |x: ExprX| Ok(bctx.spanned_typed_new(span, &typ, x));
    let mk_lit_int = |in_negative_literal: bool, i: u128, typ: &Typ| {
        check_lit_int(&bctx.ctxt, span, in_negative_literal, i, typ)?;
        let mut big_int = num_bigint::BigInt::from(i);
        if negated {
            big_int = -1 * big_int;
        }
        mk_expr(ExprX::Const(Constant::Int(big_int)))
    };
    match lit.node {
        LitKind::Bool(b) => {
            let c = vir::ast::Constant::Bool(b);
            mk_expr(ExprX::Const(c))
        }
        LitKind::Int(i, _) => mk_lit_int(false, i.get(), typ),
        LitKind::Char(c) => {
            let c = vir::ast::Constant::Char(c);
            mk_expr(ExprX::Const(c))
        }
        LitKind::Str(s, _str_style) => {
            let c = vir::ast::Constant::StrSlice(Arc::new(s.to_string()));
            mk_expr(ExprX::Const(c))
        }
        LitKind::Float(..) => {
            if let Some(ty) = ty {
                use rustc_middle::mir::interpret::LitToConstInput;
                let lit_const = LitToConstInput { lit: &lit.node, ty, neg: negated };
                let c = bctx.ctxt.tcx.lit_to_const(lit_const);
                if let rustc_middle::ty::ConstKind::Value(v) = c.kind() {
                    if let Some(i) = v.valtree.try_to_scalar_int() {
                        match i.size().bytes() {
                            4 => {
                                let c = vir::ast::Constant::Float32(i.to_u32());
                                return mk_expr(ExprX::Const(c));
                            }
                            8 => {
                                let c = vir::ast::Constant::Float64(i.to_u64());
                                return mk_expr(ExprX::Const(c));
                            }
                            _ => {}
                        }
                    }
                }
            }
            return err_span(span, "Unsupported floating point literal");
        }
        _ => {
            return err_span(span, "Unsupported constant type");
        }
    }
}

fn assignop_kind_to_binaryop<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    op: &Spanned<AssignOpKind>,
    tc: &rustc_middle::ty::TypeckResults,
    lhs: &Expr,
    rhs: &Expr,
    mode_for_ghostness: Mode,
) -> Result<BinaryOp, VirErr> {
    let bop: BinOpKind = match op.node {
        AssignOpKind::AddAssign => BinOpKind::Add,
        AssignOpKind::SubAssign => BinOpKind::Sub,
        AssignOpKind::MulAssign => BinOpKind::Mul,
        AssignOpKind::DivAssign => BinOpKind::Div,
        AssignOpKind::RemAssign => BinOpKind::Rem,
        AssignOpKind::BitXorAssign => BinOpKind::BitXor,
        AssignOpKind::BitAndAssign => BinOpKind::BitAnd,
        AssignOpKind::BitOrAssign => BinOpKind::BitOr,
        AssignOpKind::ShlAssign => BinOpKind::Shl,
        AssignOpKind::ShrAssign => BinOpKind::Shr,
    };
    binopkind_to_binaryop_inner(bctx, bop, tc, lhs, rhs, mode_for_ghostness)
}
fn binopkind_to_binaryop_inner<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    op: BinOpKind,
    tc: &rustc_middle::ty::TypeckResults,
    lhs: &Expr,
    rhs: &Expr,
    mode_for_ghostness: Mode,
) -> Result<BinaryOp, VirErr> {
    let vop = match op {
        BinOpKind::And => BinaryOp::And,
        BinOpKind::Or => BinaryOp::Or,
        BinOpKind::Eq => BinaryOp::Eq(Mode::Exec),
        BinOpKind::Ne => BinaryOp::Ne,
        BinOpKind::Le => BinaryOp::Inequality(InequalityOp::Le),
        BinOpKind::Ge => BinaryOp::Inequality(InequalityOp::Ge),
        BinOpKind::Lt => BinaryOp::Inequality(InequalityOp::Lt),
        BinOpKind::Gt => BinaryOp::Inequality(InequalityOp::Gt),
        BinOpKind::Add => BinaryOp::Arith(ArithOp::Add, mode_for_ghostness),
        BinOpKind::Sub => BinaryOp::Arith(ArithOp::Sub, mode_for_ghostness),
        BinOpKind::Mul => BinaryOp::Arith(ArithOp::Mul, mode_for_ghostness),
        BinOpKind::Div => BinaryOp::Arith(ArithOp::EuclideanDiv, mode_for_ghostness),
        BinOpKind::Rem => BinaryOp::Arith(ArithOp::EuclideanMod, mode_for_ghostness),
        BinOpKind::BitXor => {
            match ((tc.expr_ty_adjusted(lhs)).kind(), (tc.expr_ty_adjusted(rhs)).kind()) {
                (TyKind::Bool, TyKind::Bool) => BinaryOp::Xor,
                (TyKind::Int(_), TyKind::Int(_)) => {
                    BinaryOp::Bitwise(BitwiseOp::BitXor, mode_for_ghostness)
                }
                (TyKind::Uint(_), TyKind::Uint(_)) => {
                    BinaryOp::Bitwise(BitwiseOp::BitXor, mode_for_ghostness)
                }
                _ => panic!("bitwise XOR for this type not supported"),
            }
        }
        BinOpKind::BitAnd => {
            match ((tc.expr_ty_adjusted(lhs)).kind(), (tc.expr_ty_adjusted(rhs)).kind()) {
                (TyKind::Bool, TyKind::Bool) => {
                    panic!(
                        "bitwise AND for bools (i.e., the not-short-circuited version) not supported"
                    );
                }
                (TyKind::Int(_), TyKind::Int(_)) => {
                    BinaryOp::Bitwise(BitwiseOp::BitAnd, mode_for_ghostness)
                }
                (TyKind::Uint(_), TyKind::Uint(_)) => {
                    BinaryOp::Bitwise(BitwiseOp::BitAnd, mode_for_ghostness)
                }
                t => panic!("bitwise AND for this type not supported {:#?}", t),
            }
        }
        BinOpKind::BitOr => {
            match ((tc.expr_ty_adjusted(lhs)).kind(), (tc.expr_ty_adjusted(rhs)).kind()) {
                (TyKind::Bool, TyKind::Bool) => {
                    panic!(
                        "bitwise OR for bools (i.e., the not-short-circuited version) not supported"
                    );
                }
                (TyKind::Int(_), TyKind::Int(_)) => {
                    BinaryOp::Bitwise(BitwiseOp::BitOr, mode_for_ghostness)
                }
                (TyKind::Uint(_), TyKind::Uint(_)) => {
                    BinaryOp::Bitwise(BitwiseOp::BitOr, mode_for_ghostness)
                }
                _ => panic!("bitwise OR for this type not supported"),
            }
        }
        BinOpKind::Shl => {
            let (Some(w), s) = bitwidth_and_signedness_of_integer_type(
                &bctx.ctxt.verus_items,
                bctx.types.expr_ty(lhs),
            ) else {
                return err_span(lhs.span, "expected finite integer width for <<");
            };
            BinaryOp::Bitwise(BitwiseOp::Shl(w, s), mode_for_ghostness)
        }
        BinOpKind::Shr => {
            let (Some(w), _s) = bitwidth_and_signedness_of_integer_type(
                &bctx.ctxt.verus_items,
                bctx.types.expr_ty(lhs),
            ) else {
                return err_span(lhs.span, "expected finite integer width for >>");
            };
            BinaryOp::Bitwise(BitwiseOp::Shr(w), mode_for_ghostness)
        }
    };
    Ok(vop)
}

fn binopkind_to_binaryop<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    op: &Spanned<BinOpKind>,
    tc: &rustc_middle::ty::TypeckResults,
    lhs: &Expr,
    rhs: &Expr,
    mode_for_ghostness: Mode,
) -> Result<BinaryOp, VirErr> {
    binopkind_to_binaryop_inner(bctx, op.node, tc, lhs, rhs, mode_for_ghostness)
}

fn expr_assign_to_vir_innermost<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    tc: &rustc_middle::ty::TypeckResults,
    lhs: &Expr<'tcx>,
    mk_expr: impl Fn(ExprX) -> Result<vir::ast::Expr, vir::messages::Message>,
    rhs: &Expr<'tcx>,
    modifier: ExprModifier,
    op_kind: Option<&Spanned<AssignOpKind>>,
) -> Result<vir::ast::Expr, vir::messages::Message> {
    if bctx.ctxt.cmd_line_args.new_mut_ref {
        let vir_lhs = expr_to_vir(bctx, lhs, modifier)?;
        let vir_place = crate::places::expr_to_place_for_mut_ref(&vir_lhs)?;
        let vir_rhs = expr_to_vir(bctx, rhs, modifier)?;

        let mode_for_ghostness = if bctx.in_ghost { Mode::Spec } else { Mode::Exec };
        let op = match op_kind {
            Some(op) => {
                Some(assignop_kind_to_binaryop(bctx, op, tc, lhs, rhs, mode_for_ghostness)?)
            }
            None => None,
        };

        return mk_expr(ExprX::AssignToPlace { place: vir_place, rhs: vir_rhs, op: op });
    }

    fn init_not_mut(bctx: &BodyCtxt, lhs: &Expr) -> Result<bool, VirErr> {
        Ok(match lhs.kind {
            ExprKind::Path(QPath::Resolved(None, rustc_hir::Path { res: Res::Local(id), .. })) => {
                let not_mut = if let Node::Pat(pat) = bctx.ctxt.tcx.hir_node(*id) {
                    let (mutable, _) = pat_to_mut_var(pat)?;
                    let ty = bctx.types.node_type(*id);
                    !(mutable || ty.ref_mutability() == Some(Mutability::Mut))
                } else {
                    panic!("assignment to non-local");
                };
                if not_mut {
                    let mut parent = bctx.ctxt.tcx.hir_parent_iter(*id);
                    let (_, parent) = parent.next().expect("one parent for local");
                    match parent {
                        Node::Param(_) => err_span(lhs.span, "cannot assign to non-mut parameter")?,
                        Node::LetStmt(_) => (),
                        other => unsupported_err!(lhs.span, "assignee node", other),
                    }
                }
                not_mut
            }
            ExprKind::Field(lhs, _) => {
                let deref_ghost = mid_ty_to_vir_ghost(
                    bctx.ctxt.tcx,
                    &bctx.ctxt.verus_items,
                    bctx.fun_id,
                    lhs.span,
                    &bctx.types.expr_ty_adjusted(lhs),
                    true,
                )?
                .1;
                unsupported_err_unless!(!deref_ghost, lhs.span, "assignment through Ghost/Tracked");
                init_not_mut(bctx, lhs)?
            }
            ExprKind::MethodCall(_, receiver, _, span) => {
                let fn_def_id = bctx
                    .types
                    .type_dependent_def_id(lhs.hir_id)
                    .expect("def id of the method definition");
                let verus_item = bctx.ctxt.get_verus_item(fn_def_id);
                if matches!(
                    verus_item,
                    Some(VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut))
                ) {
                    let nm = init_not_mut(bctx, &receiver)?;
                    unsupported_err_unless!(!nm, span, "this call for delayed initialization");
                    nm
                } else {
                    unsupported_err!(span, "this call in assignment");
                }
            }
            ExprKind::Unary(UnOp::Deref, _) => false,
            _ => {
                unsupported_err!(lhs.span, format!("assign lhs {:?}", lhs))
            }
        })
    }
    let mode_for_ghostness = if bctx.in_ghost { Mode::Spec } else { Mode::Exec };
    let op = match op_kind {
        Some(op) => Some(assignop_kind_to_binaryop(bctx, op, tc, lhs, rhs, mode_for_ghostness)?),
        None => None,
    };

    // NOTE: A temparary solution for index_mut until mutable reference support lands.
    if let ExprKind::Index(tgt_expr, idx_expr, _span) = &lhs.kind {
        if bctx.in_ghost {
            unsupported_err!(lhs.span, "index_mut in spec/proof", lhs);
        }
        let tgt_modifier =
            is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(&tgt_expr), ExprModifier::ADDR_OF_MUT)?;
        let tgt_vir = expr_to_vir(bctx, tgt_expr, tgt_modifier)?;
        let idx_vir = expr_to_vir(bctx, idx_expr, ExprModifier::REGULAR)?;

        let mut rhs_vir = expr_to_vir(bctx, rhs, modifier)?;
        let fun = vir::fun!["vstd" => "std_specs", "core", "index_set"];
        let typ_args = Some(Arc::new(vec![
            undecorate_typ(&tgt_vir.typ),
            idx_vir.typ.clone(),
            rhs_vir.typ.clone(),
        ]));
        let tgt_vir =
            bctx.spanned_typed_new(tgt_expr.span, &tgt_vir.typ.clone(), ExprX::Loc(tgt_vir));
        let call_target = CallTarget::Fun(
            vir::ast::CallTargetKind::Static,
            fun,
            typ_args.unwrap(),
            Arc::new(vec![]),
            AutospecUsage::Final,
        );
        if let Some(op) = op {
            // Evaluate tgt and idx twice may have side effects.
            unsupported_err_unless!(
                !tgt_expr.can_have_side_effects() && !idx_expr.can_have_side_effects(),
                lhs.span,
                "assign op to index_mut with tgt/idx that could have side effects",
                lhs
            );
            unsupported_err_unless!(
                is_smt_arith(bctx, lhs.span, rhs.span, &lhs.hir_id, &rhs.hir_id)?,
                lhs.span,
                "assign op to index_mut for non smt arithmetic types",
                lhs
            );
            let lhs_vir = expr_to_vir(bctx, lhs, ExprModifier::REGULAR)?;
            let rhs_ty = &rhs_vir.typ.clone();
            rhs_vir =
                bctx.spanned_typed_new(rhs.span, &rhs_ty, ExprX::Binary(op, lhs_vir, rhs_vir));
        }

        let args = Arc::new(vec![tgt_vir, idx_vir, rhs_vir]);
        let index_set = bctx.spanned_typed_new(
            lhs.span,
            &mk_tuple_typ(&Arc::new(vec![])),
            ExprX::Call(call_target, args),
        );
        // lhs is not recorded and so explicitly add it here.
        let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
        erasure_info.direct_var_modes.push((lhs.hir_id, Mode::Exec));
        return Ok(index_set);
    }
    let init_not_mut = init_not_mut(bctx, lhs)?;
    mk_expr(ExprX::Assign {
        init_not_mut,
        lhs: expr_to_vir(bctx, lhs, ExprModifier::ADDR_OF_MUT)?,
        rhs: expr_to_vir(bctx, rhs, modifier)?,
        op: op,
    })
}

pub(crate) fn let_stmt_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pattern: &rustc_hir::Pat<'tcx>,
    initializer: &Option<&Expr<'tcx>>,
    els: &Option<&Block<'tcx>>,
    attrs: &[Attribute],
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    let mode = get_var_mode(bctx.mode, attrs);
    let infer_mode = parse_attrs_opt(attrs, None).contains(&Attr::InferMode);
    let els = if let Some(els) = els {
        if matches!(mode, Mode::Spec | Mode::Proof) {
            unsupported_err!(els.span, "let-else in spec/proof", els);
        }
        let init = initializer.unwrap();
        let init_type = typ_of_node(bctx, els.span, &init.hir_id, false)?;
        let els_typ = typ_of_node(bctx, els.span, &els.hir_id, false)?;
        let els_block = block_to_vir(bctx, els, &els.span, &els_typ, ExprModifier::REGULAR)?;
        Some(bctx.spanned_typed_new(els.span, &init_type, ExprX::NeverToAny(els_block)))
    } else {
        None
    };
    let init = initializer.map(|e| expr_to_vir(bctx, e, ExprModifier::REGULAR)).transpose()?;

    if parse_attrs_opt(attrs, Some(&mut *bctx.ctxt.diagnostics.borrow_mut()))
        .contains(&Attr::UnwrappedBinding)
    {
        let pat_typ = &bctx.types.node_type(pattern.hir_id);
        if let TyKind::Adt(AdtDef(adt_def_data), _args) = pat_typ.kind() {
            let pat_typ_verus_item = bctx.ctxt.verus_items.id_to_name.get(&adt_def_data.did);
            if pat_typ_verus_item
                == Some(&VerusItem::BuiltinType(verus_items::BuiltinTypeItem::Tracked))
                && mode == Mode::Proof
            {
                bctx.ctxt.diagnostics.borrow_mut().push(
                    vir::ast::VirErrAs::Warning(
                        crate::util::err_span_bare(pattern.span, format!("the right-hand side is already wrapped with `Tracked`, you likely don't need a `tracked` variable"))
                        .help("consider `.get()` on the right-hand side, or removing `tracked` on the left-hand side")));
            } else if pat_typ_verus_item
                == Some(&VerusItem::BuiltinType(verus_items::BuiltinTypeItem::Ghost))
                && mode == Mode::Spec
            {
                bctx.ctxt.diagnostics.borrow_mut().push(
                    vir::ast::VirErrAs::Warning(
                        crate::util::err_span_bare(pattern.span, format!("the right-hand side is already wrapped with `Ghost`, you likely don't need a `ghost` variable"))
                        .help("consider `@` on the right-hand side, or removing `ghost` on the left-hand side")));
            }
        }
    }

    let vir_pattern = pattern_to_vir(bctx, pattern)?;
    let mode = if infer_mode { None } else { Some(mode) };
    Ok(vec![bctx.spanned_new(pattern.span, StmtX::Decl { pattern: vir_pattern, mode, init, els })])
}

fn unwrap_parameter_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    stmt1: &Stmt<'tcx>,
    stmt2: &Stmt<'tcx>,
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    // match "let x;"
    let x = if let StmtKind::Let(LetStmt {
        pat:
            pat @ Pat {
                kind: PatKind::Binding(BindingMode(ByRef::No, Mutability::Not), hir_id, x, None),
                ..
            },
        ty: None,
        init: None,
        els: None,
        ..
    }) = &stmt1.kind
    {
        Some((pat.hir_id, local_to_var(x, hir_id.local_id)))
    } else {
        None
    };
    // match #[verifier(proof_block)]
    let ghost = get_ghost_block_opt(bctx.ctxt.tcx.hir_attrs(stmt2.hir_id));
    // match { x = y.get() } or { x = y.view() }
    let xy_mode = if let StmtKind::Semi(Expr {
        kind:
            ExprKind::Block(
                Block {
                    stmts: [],
                    expr:
                        Some(Expr {
                            kind:
                                ExprKind::Assign(
                                    expr_x @ Expr { kind: ExprKind::Path(path_x), .. },
                                    expr_get @ Expr {
                                        kind:
                                            ExprKind::MethodCall(
                                                _ident,
                                                expr_y @ Expr {
                                                    kind: ExprKind::Path(path_y), ..
                                                },
                                                [],
                                                _span2,
                                            ),
                                        ..
                                    },
                                    _,
                                ),
                            ..
                        }),
                    ..
                },
                None,
            ),
        ..
    }) = &stmt2.kind
    {
        let fn_def_id = bctx
            .types
            .type_dependent_def_id(expr_get.hir_id)
            .expect("def id of the method definition");
        let verus_item = bctx.ctxt.verus_items.id_to_name.get(&fn_def_id);
        let ident_x = crate::rust_to_vir_base::qpath_to_ident(bctx.ctxt.tcx, path_x);
        let ident_y = crate::rust_to_vir_base::qpath_to_ident(bctx.ctxt.tcx, path_y);
        let mode = match verus_item {
            Some(VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(
                SpecGhostTrackedItem::GhostView,
            ))) => Some((Mode::Spec, ResolvedCall::Spec)),
            Some(VerusItem::CompilableOpr(CompilableOprItem::TrackedGet)) => Some((
                Mode::Proof,
                ResolvedCall::CompilableOperator(CompilableOperator::TrackedGet),
            )),
            _ => None,
        };
        Some((expr_x.hir_id, expr_y.hir_id, expr_get.hir_id, ident_x, ident_y, mode))
    } else {
        None
    };
    match (x, ghost, xy_mode) {
        (
            Some((hir_id1, x1)),
            Some(GhostBlockAttr::Proof),
            Some((hir_id2, hir_id_y, hir_id_get, Some(x2), Some(y), Some((mode, resolved_call)))),
        ) if x1 == x2 => {
            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
            erasure_info.direct_var_modes.push((hir_id1, mode));
            erasure_info.direct_var_modes.push((hir_id2, mode));
            erasure_info.direct_var_modes.push((hir_id_y, Mode::Exec));
            erasure_info.resolved_calls.push((hir_id_get, stmt2.span.data(), resolved_call));
            let unwrap = vir::ast::UnwrapParameter { mode, outer_name: y, inner_name: x1 };
            let headerx = HeaderExprX::UnwrapParameter(unwrap);
            let exprx = ExprX::Header(Arc::new(headerx));
            let expr = bctx.spanned_typed_new(stmt1.span, &Arc::new(TypX::Bool), exprx);
            let stmt = bctx.spanned_new(stmt1.span, StmtX::Expr(expr));
            Ok(vec![stmt])
        }
        _ => err_span(stmt1.span, "ill-formed unwrap_parameter header"),
    }
}

pub(crate) fn stmt_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    stmt: &Stmt<'tcx>,
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    if bctx.external_body {
        // we want just requires/ensures, not the whole body
        match &stmt.kind {
            StmtKind::Expr(..) | StmtKind::Semi(..) => {}
            _ => return Ok(vec![]),
        }
    }

    match &stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
            if is_ignorable_dummy_capture_operation(bctx, expr) {
                return Ok(vec![]);
            }

            let vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            Ok(vec![bctx.spanned_new(expr.span, StmtX::Expr(vir_expr))])
        }
        StmtKind::Item(item_id) => {
            let attrs = bctx.ctxt.tcx.hir_attrs(item_id.hir_id());
            let vattrs = bctx.ctxt.get_verifier_attrs(attrs)?;
            if vattrs.internal_reveal_fn {
                dbg!(&item_id.hir_id());
                unreachable!();
            } else if vattrs.internal_const_body {
                dbg!(&item_id.hir_id());
                unreachable!();
            } else if vattrs.open_visibility_qualifier {
                let item = bctx.ctxt.tcx.hir_item(*item_id);
                if !matches!(&item.kind, ItemKind::Use(..)) {
                    crate::internal_err!(
                        item.span,
                        "open_visibility_qualifier should be on a 'use' item"
                    );
                }

                let hir_id = item.hir_id();
                let owner_id = hir_id.expect_owner();
                let def_id = owner_id.to_def_id();

                let vis = bctx.ctxt.tcx.visibility(def_id);
                let vis = crate::rust_to_vir_base::mk_visibility_from_vis(&bctx.ctxt, vis);

                let vir_expr = bctx.spanned_typed_new(
                    stmt.span,
                    &vir::ast_util::unit_typ(),
                    ExprX::Header(Arc::new(HeaderExprX::OpenVisibilityQualifier(vis))),
                );

                Ok(vec![bctx.spanned_new(stmt.span, StmtX::Expr(vir_expr))])
            } else {
                let item = bctx.ctxt.tcx.hir_item(*item_id);
                if matches!(&item.kind, ItemKind::Use(..) | ItemKind::Macro(..)) {
                    return Ok(vec![]);
                }
                unsupported_err!(stmt.span, "internal item statements", stmt)
            }
        }
        StmtKind::Let(LetStmt { pat, ty: _, init, els, .. }) => {
            if let Some(init) = init {
                if is_ignorable_dummy_capture_operation(bctx, init) {
                    return Ok(vec![]);
                }
            }

            let_stmt_to_vir(bctx, pat, init, els, bctx.ctxt.tcx.hir_attrs(stmt.hir_id))
        }
    }
}

pub(crate) fn stmts_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    stmts: &mut impl Iterator<Item = &'tcx Stmt<'tcx>>,
) -> Result<Option<Vec<vir::ast::Stmt>>, VirErr> {
    if let Some(stmt) = stmts.next() {
        let attrs = crate::attributes::parse_attrs_opt(bctx.ctxt.tcx.hir_attrs(stmt.hir_id), None);
        if let [Attr::UnwrapParameter] = attrs[..] {
            if let Some(stmt2) = stmts.next() {
                return Ok(Some(unwrap_parameter_to_vir(bctx, stmt, stmt2)?));
            } else {
                return err_span(stmt.span, "ill-formed unwrap_parameter header");
            }
        }
        Ok(Some(stmt_to_vir(bctx, stmt)?))
    } else {
        Ok(None)
    }
}

pub(crate) fn is_ignorable_dummy_capture_operation<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> bool {
    match &expr.kind {
        ExprKind::Call(fun, _) => match &fun.kind {
            ExprKind::Path(QPath::Resolved(
                None,
                rustc_hir::Path { res: Res::Def(_, fun_id), .. },
            )) => {
                let verus_item = bctx.ctxt.get_verus_item(*fun_id);
                matches!(
                    verus_item,
                    Some(VerusItem::DummyCapture(
                        DummyCaptureItem::New | DummyCaptureItem::Consume
                    ))
                )
            }
            _ => false,
        },
        _ => false,
    }
}

pub(crate) fn closure_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    closure_expr: &Expr<'tcx>,
    closure_vir_typ: Typ,
    is_spec_fn: bool,
    proof_fn_modes: Option<(Arc<Vec<Mode>>, Mode)>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    if let ExprKind::Closure(Closure { fn_decl, body: body_id, def_id, .. }) = &closure_expr.kind {
        unsupported_err_unless!(!fn_decl.c_variadic, closure_expr.span, "c_variadic");
        unsupported_err_unless!(
            matches!(fn_decl.implicit_self, rustc_hir::ImplicitSelfKind::None),
            closure_expr.span,
            "implicit_self in closure"
        );
        let body = bctx.ctxt.tcx.hir_body(*body_id);

        let typs = closure_param_typs(bctx, closure_expr)?;
        assert!(typs.len() == body.params.len());
        let params: Vec<VarBinder<Typ>> = body
            .params
            .iter()
            .zip(typs.clone())
            .map(|(x, t)| {
                let attrs = bctx.ctxt.tcx.hir_attrs(x.hir_id);
                let mode = crate::attributes::get_mode(Mode::Exec, attrs);
                if mode != Mode::Exec {
                    return err_span(x.span, "closures only accept exec-mode parameters");
                }

                let (is_mut, name) = pat_to_mut_var(x.pat)?;
                if is_mut {
                    return err_span(x.span, "Verus does not support 'mut' params for closures");
                }
                Ok(Arc::new(VarBinderX { name, a: t }))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut body = expr_to_vir(bctx, &body.value, modifier)?;

        let header = vir::headers::read_header(&mut body, &vir::headers::HeaderAllows::Closure)?;
        let vir::headers::Header { require, ensure, ensure_id_typ, .. } = header;
        assert!(ensure.1.len() == 0);

        let exprx = if is_spec_fn {
            bctx.ctxt.push_body_erasure(*def_id, BodyErasure { erase_body: true, ret_spec: true });

            if require.len() > 0 || ensure.0.len() > 0 {
                return err_span(
                    closure_expr.span,
                    "SpecFn should not have `requires` clause or `ensures` clause",
                );
            }
            ExprX::Closure(Arc::new(params), body)
        } else {
            bctx.ctxt.push_body_erasure(
                *def_id,
                BodyErasure {
                    erase_body: false,
                    ret_spec: match proof_fn_modes {
                        None => false,
                        Some((_, ret_mode)) => ret_mode == Mode::Spec,
                    },
                },
            );

            let ret_typ = closure_ret_typ(bctx, closure_expr)?;

            let id = match ensure_id_typ {
                Some((id, ensures_typ)) => {
                    if !types_equal(&ensures_typ, &ret_typ) {
                        return err_span(
                            closure_expr.span,
                            "return type given in `ensures` clause should match the actual closure return type",
                        );
                    }
                    id
                }
                None => str_unique_var(
                    vir::def::CLOSURE_RETURN_VALUE_PREFIX,
                    vir::ast::VarIdentDisambiguate::RustcId(body_id.hir_id.local_id.index()),
                ),
            };

            let ret = Arc::new(VarBinderX { name: id, a: ret_typ });

            ExprX::NonSpecClosure {
                params: Arc::new(params),
                proof_fn_modes,
                body,
                requires: require,
                ensures: ensure.0,
                ret: ret,
                external_spec: None, // filled in by ast_simplify
            }
        };
        Ok(bctx.spanned_typed_new(closure_expr.span, &closure_vir_typ, exprx))
    } else {
        panic!("closure_to_vir expects ExprKind::Closure");
    }
}

fn remove_decoration_typs_for_unsizing<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty1: rustc_middle::ty::Ty<'tcx>,
    ty2: rustc_middle::ty::Ty<'tcx>,
) -> (rustc_middle::ty::Ty<'tcx>, rustc_middle::ty::Ty<'tcx>) {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Ref(_, t1, Mutability::Not), TyKind::Ref(_, t2, Mutability::Not)) => {
            remove_decoration_typs_for_unsizing(tcx, *t1, *t2)
        }
        (TyKind::Adt(AdtDef(adt_def_data1), args1), TyKind::Adt(AdtDef(adt_def_data2), args2))
            if verus_items::get_rust_item(tcx, adt_def_data1.did)
                == Some(verus_items::RustItem::Box)
                && verus_items::get_rust_item(tcx, adt_def_data2.did)
                    == Some(verus_items::RustItem::Box) =>
        {
            let rustc_middle::ty::GenericArgKind::Type(t1) = args1[0].unpack() else {
                panic!("unexpected type argument")
            };
            let rustc_middle::ty::GenericArgKind::Type(t2) = args2[0].unpack() else {
                panic!("unexpected type argument")
            };
            remove_decoration_typs_for_unsizing(tcx, t1, t2)
        }
        _ => (ty1, ty2),
    }
}

enum PtrCastKind {
    Trivial,
    Complex(vir::ast::Fun, vir::ast::Typs, bool),
}

fn is_ptr_cast<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    src: rustc_middle::ty::Ty<'tcx>,
    dst: rustc_middle::ty::Ty<'tcx>,
) -> Result<Option<PtrCastKind>, VirErr> {
    // Mutability can always be ignored
    match (src.kind(), dst.kind()) {
        (TyKind::RawPtr(ty1, _), TyKind::RawPtr(ty2, _)) => {
            if ty1 == ty2 {
                return Ok(Some(PtrCastKind::Trivial));
            } else if ty2
                .is_sized(bctx.ctxt.tcx, TypingEnv::post_analysis(bctx.ctxt.tcx, bctx.fun_id))
            {
                let src_ty = mid_ty_to_vir(
                    bctx.ctxt.tcx,
                    &bctx.ctxt.verus_items,
                    bctx.fun_id,
                    span,
                    ty1,
                    false,
                )?;
                let dst_ty = mid_ty_to_vir(
                    bctx.ctxt.tcx,
                    &bctx.ctxt.verus_items,
                    bctx.fun_id,
                    span,
                    ty2,
                    false,
                )?;
                let fun = vir::fun!("vstd" => "raw_ptr", "cast_ptr_to_thin_ptr");
                let typs = Arc::new(vec![src_ty, dst_ty]);
                return Ok(Some(PtrCastKind::Complex(fun, typs, false)));
            }

            //match (ty1.kind(), ty2.kind()) {
            //
            //}
            return Ok(None);
        }
        (TyKind::RawPtr(ty1, _), _ty2)
            if crate::rust_to_vir_base::is_integer_ty(&bctx.ctxt.verus_items, &dst) =>
        {
            let src_ty = mid_ty_to_vir(
                bctx.ctxt.tcx,
                &bctx.ctxt.verus_items,
                bctx.fun_id,
                span,
                ty1,
                false,
            )?;
            let typs = Arc::new(vec![src_ty]);
            let fun = vir::fun!("vstd" => "raw_ptr", "cast_ptr_to_usize");

            // cast_ptr_to_usize casts to a usize; we might need to do an additional
            // clip afterwards, so return with clip=true
            return Ok(Some(PtrCastKind::Complex(fun, typs, true)));
        }
        _ => Ok(None),
    }
}

pub(crate) fn maybe_do_ptr_cast<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    dst_expr: &Expr,
    src_expr: &Expr,
    src_vir: &vir::ast::Expr,
) -> Result<Option<vir::ast::Expr>, VirErr> {
    let source_ty = bctx.types.expr_ty_adjusted(src_expr);
    let to_ty = bctx.types.expr_ty(dst_expr);
    match is_ptr_cast(bctx, dst_expr.span, source_ty, to_ty)? {
        Some(PtrCastKind::Trivial) => {
            return Ok(Some(src_vir.clone()));
        }
        Some(PtrCastKind::Complex(fun, typ_args, clip)) => {
            let autospec_usage =
                if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };
            let call_target = CallTarget::Fun(
                vir::ast::CallTargetKind::Static,
                fun,
                typ_args,
                Arc::new(vec![]),
                autospec_usage,
            );
            let args = Arc::new(vec![src_vir.clone()]);
            let x = ExprX::Call(call_target, args);
            let expr_typ = typ_of_node(bctx, dst_expr.span, &dst_expr.hir_id, false)?;

            if clip {
                let expr_attrs = bctx.ctxt.tcx.hir_attrs(dst_expr.hir_id);
                let expr_vattrs = bctx.ctxt.get_verifier_attrs(expr_attrs)?;

                let expr =
                    bctx.spanned_typed_new(dst_expr.span, &Arc::new(TypX::Int(IntRange::USize)), x);
                return Ok(Some(mk_ty_clip(&expr_typ, &expr, expr_vattrs.truncate)));
            } else {
                let expr = bctx.spanned_typed_new(dst_expr.span, &expr_typ, x);
                return Ok(Some(expr));
            }
        }
        None => Ok(None),
    }
}

fn deref_expr_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    arg: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let arg_ty = bctx.types.expr_ty_adjusted(arg);

    match arg_ty.kind() {
        TyKind::RawPtr(..) => {
            unsupported_err!(
                expr.span,
                format!(
                    "dereferencing a raw pointer. Currently, Verus only supports raw pointers through the permissioned raw_ptr interface: https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/index.html"
                )
            );
        }
        _ => { /* report errors for dereferencing other types later */ }
    }

    let modifier = is_expr_typ_mut_ref(arg_ty, modifier)?;
    let inner_expr = expr_to_vir_inner(bctx, arg, modifier)?;

    if !bctx.types.is_method_call(expr) || auto_deref_supported_for_ty(bctx.ctxt.tcx, &arg_ty) {
        if bctx.ctxt.cmd_line_args.new_mut_ref
            && matches!(arg_ty.kind(), TyKind::Ref(_, _, rustc_ast::Mutability::Mut))
        {
            let t = match &*inner_expr.typ {
                TypX::MutRef(t) => t.clone(),
                _ => panic!("expected mut ref"),
            };
            Ok(bctx.spanned_typed_new(expr.span, &t, ExprX::DerefMut(inner_expr)))
        } else {
            // Normal dereference, just strip the inner expression.
            Ok(strip_vir_ref_decoration(inner_expr))
        }
    } else {
        // Overloaded dereference other than internally implemented ones.
        // Insert a function call to the overloaded method.
        let fn_def_id = bctx
            .types
            .type_dependent_def_id(expr.hir_id)
            .expect("cannot get the function definition id for a deref");
        let res_ty = bctx.types.node_type(expr.hir_id);
        let inner_ty = mid_ty_to_vir(
            bctx.ctxt.tcx,
            &bctx.ctxt.verus_items,
            bctx.fun_id,
            expr.span,
            &res_ty,
            false,
        )?;
        crate::fn_call_to_vir::deref_to_vir(
            bctx, expr, fn_def_id, inner_expr, inner_ty, arg_ty, expr.span,
        )
    }
}

fn strip_vir_ref_decoration<'tcx>(mut inner_expr: vir::ast::Expr) -> vir::ast::Expr {
    let typ = &mut Arc::make_mut(&mut inner_expr).typ;
    if let TypX::Decorate(
        vir::ast::TypDecoration::MutRef
        | vir::ast::TypDecoration::Ref
        | vir::ast::TypDecoration::Box
        | vir::ast::TypDecoration::Rc
        | vir::ast::TypDecoration::Arc,
        _,
        inner_typ,
    ) = &**typ
    {
        *typ = inner_typ.clone();
    }
    inner_expr
}
