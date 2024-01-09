use crate::attributes::{
    get_custom_err_annotations, get_ghost_block_opt, get_trigger, get_var_mode, get_verifier_attrs,
    parse_attrs, parse_attrs_opt, Attr, GhostBlockAttr,
};
use crate::context::{BodyCtxt, Context};
use crate::erase::{CompilableOperator, ResolvedCall};
use crate::rust_intrinsics_to_vir::int_intrinsic_constant_to_vir;
use crate::rust_to_vir_base::{
    auto_deref_supported_for_ty, def_id_to_vir_path, get_range, is_smt_arith, is_smt_equality,
    local_to_var, mid_ty_simplify, mid_ty_to_vir, mid_ty_to_vir_ghost, mk_range, typ_of_node,
    typ_of_node_expect_mut_ref,
};
use crate::spans::err_air_span;
use crate::util::{
    err_span, err_span_bare, slice_vec_map_result, unsupported_err_span, vec_map_result,
};
use crate::verus_items::{
    self, CompilableOprItem, OpenInvariantBlockItem, SpecGhostTrackedItem, UnaryOpItem, VerusItem,
};
use crate::{fn_call_to_vir::fn_call_to_vir, unsupported_err, unsupported_err_unless};
use air::ast::{Binder, BinderX};
use air::ast_util::str_ident;
use rustc_ast::{Attribute, BorrowKind, ByRef, LitKind, Mutability};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    BinOpKind, BindingAnnotation, Block, Closure, Destination, Expr, ExprKind, Guard, HirId, Let,
    Local, LoopSource, Node, Pat, PatKind, QPath, Stmt, StmtKind, UnOp,
};
use rustc_middle::ty::adjustment::{
    Adjust, Adjustment, AutoBorrow, AutoBorrowMutability, PointerCoercion,
};
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind, VariantDef};
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    ArithOp, ArmX, AutospecUsage, BinaryOp, BitwiseOp, CallTarget, Constant, ExprX, FieldOpr, FunX,
    HeaderExprX, InequalityOp, IntRange, InvAtomicity, Mode, PatternX, SpannedTyped, StmtX, Stmts,
    Typ, TypX, UnaryOp, UnaryOpr, VirErr,
};
use vir::ast_util::{ident_binder, typ_to_diagnostic_str, types_equal, undecorate_typ};
use vir::def::positional_field_ident;

pub(crate) fn pat_to_mut_var<'tcx>(pat: &Pat) -> Result<(bool, String), VirErr> {
    let Pat { hir_id: _, kind, span, default_binding_modes } = pat;
    unsupported_err_unless!(default_binding_modes, *span, "default_binding_modes");
    match kind {
        PatKind::Binding(annotation, id, ident, pat) => {
            let BindingAnnotation(_, mutability) = annotation;
            let mutable = match mutability {
                rustc_hir::Mutability::Mut => true,
                rustc_hir::Mutability::Not => false,
            };
            match pat {
                None => {}
                Some(p) => {
                    unsupported_err!(p.span, "expected variable, found @ pattern")
                }
            }
            Ok((mutable, local_to_var(ident, id.local_id)))
        }
        _ => {
            unsupported_err!(*span, "only variables are supported here, not general patterns")
        }
    }
}

pub(crate) fn pat_to_var<'tcx>(pat: &Pat) -> Result<String, VirErr> {
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
                TypX::Tuple(typs) => Ok((**typs).clone()),
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
                return err_span(span, "integer literal out of range");
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
    let adjustments = bctx.types.expr_adjustments(expr);

    let vir_expr =
        expr_to_vir_with_adjustments(bctx, expr, modifier, adjustments, adjustments.len())?;

    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.hir_vir_ids.push((expr.hir_id, vir_expr.span.id));
    Ok(vir_expr)
}

pub(crate) fn expr_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let mut vir_expr = expr_to_vir_inner(bctx, expr, modifier)?;
    let attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
    for group in get_trigger(attrs)? {
        vir_expr = vir_expr.new_x(ExprX::Unary(UnaryOp::Trigger(group), vir_expr.clone()));
    }
    for err_msg in get_custom_err_annotations(attrs)? {
        vir_expr = vir_expr
            .new_x(ExprX::UnaryOpr(UnaryOpr::CustomErr(Arc::new(err_msg)), vir_expr.clone()));
    }
    Ok(vir_expr)
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

/// Gets the DefId of the AdtDef for this Res and the Variant
/// The bool is true if it's an enum, false for struct
pub(crate) fn get_adt_res<'tcx>(
    tcx: TyCtxt<'tcx>,
    res: Res,
    span: Span,
) -> Result<(DefId, &'tcx VariantDef, bool), VirErr> {
    // Based off of implementation of rustc_middle's TyCtxt::expect_variant_res
    // But with a few more cases it didn't handle
    // Also, returns the adt DefId instead of just the VariantDef

    use rustc_hir::def::CtorOf;
    match res {
        Res::Def(DefKind::Variant, did) => {
            let enum_did = tcx.parent(did);
            let variant_def = tcx.adt_def(enum_did).variant_with_id(did);
            Ok((enum_did, variant_def, true))
        }
        Res::Def(DefKind::Struct, did) => {
            let variant_def = tcx.adt_def(did).non_enum_variant();
            Ok((did, variant_def, false))
        }
        Res::Def(DefKind::Ctor(CtorOf::Variant, ..), variant_ctor_did) => {
            let variant_did = tcx.parent(variant_ctor_did);
            let enum_did = tcx.parent(variant_did);
            let variant_def = tcx.adt_def(enum_did).variant_with_ctor_id(variant_ctor_did);
            Ok((enum_did, variant_def, true))
        }
        Res::Def(DefKind::Ctor(CtorOf::Struct, ..), ctor_did) => {
            let struct_did = tcx.parent(ctor_did);
            let variant_def = tcx.adt_def(struct_did).non_enum_variant();
            Ok((struct_did, variant_def, false))
        }
        Res::Def(DefKind::TyAlias { lazy }, alias_did) => {
            unsupported_err_unless!(!lazy, span, "lazy type alias");

            let alias_ty = tcx.type_of(alias_did).skip_binder();

            let struct_did = match alias_ty.kind() {
                TyKind::Adt(AdtDef(adt_def_data), _args) => adt_def_data.did,
                _ => {
                    return err_span(
                        span,
                        "Verus internal error: got unexpected alias type trying to resolve constructor",
                    );
                }
            };

            let variant_def = tcx.adt_def(struct_did).non_enum_variant();
            Ok((struct_did, variant_def, false))
        }
        Res::SelfCtor(impl_id) | Res::SelfTyAlias { alias_to: impl_id, .. } => {
            let self_ty = tcx.type_of(impl_id).skip_binder();
            let struct_did = match self_ty.kind() {
                TyKind::Adt(AdtDef(adt_def_data), _args) => adt_def_data.did,
                _ => {
                    return err_span(
                        span,
                        "Verus internal error: got unexpected Self type trying to resolve constructor",
                    );
                }
            };

            let variant_def = tcx.adt_def(struct_did).non_enum_variant();
            Ok((struct_did, variant_def, false))
        }
        _ => {
            println!("res: {:#?}", res);
            err_span(span, "Verus internal error: got unexpected Res trying to resolve constructor")
        }
    }
}

pub(crate) fn expr_tuple_datatype_ctor_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    res: &Res,
    args_slice: &[Expr<'tcx>],
    fun_span: Span,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let expr_typ = typ_of_node(bctx, expr.span, &expr.hir_id, false)?;

    let (adt_def_id, variant_def, _is_enum) = get_adt_res(tcx, *res, fun_span)?;
    let variant_name = str_ident(&variant_def.ident(tcx).as_str());
    let vir_path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, adt_def_id);

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
    let exprx = ExprX::Ctor(vir_path, variant_name, vir_fields, None);
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
        PatKind::Binding(BindingAnnotation(_, Mutability::Not), canonical, x, None) => {
            PatternX::Var { name: Arc::new(local_to_var(x, canonical.local_id)), mutable: false }
        }
        PatKind::Binding(BindingAnnotation(_, Mutability::Mut), canonical, x, None) => {
            PatternX::Var { name: Arc::new(local_to_var(x, canonical.local_id)), mutable: true }
        }
        PatKind::Path(qpath) => {
            let res = bctx.types.qpath_res(qpath, pat.hir_id);
            let (adt_def_id, variant_def, _is_enum) = get_adt_res(tcx, res, pat.span)?;
            let variant_name = str_ident(&variant_def.ident(tcx).as_str());
            let vir_path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, adt_def_id);
            PatternX::Constructor(vir_path, variant_name, Arc::new(vec![]))
        }
        PatKind::Tuple(pats, dot_dot_pos) => {
            let mut patterns: Vec<vir::ast::Pattern> = Vec::new();

            let typs = match &*pat_typ {
                TypX::Tuple(typs) => typs,
                _ => {
                    return err_span(pat.span, "Verus internal error: expected tuple type");
                }
            };
            let (n_wildcards, pos_to_insert_wildcards) =
                handle_dot_dot(pats.len(), typs.len(), &dot_dot_pos);

            for pat in pats.iter() {
                patterns.push(pattern_to_vir(bctx, pat)?);
            }
            patterns.splice(
                pos_to_insert_wildcards..pos_to_insert_wildcards,
                typs[pos_to_insert_wildcards..pos_to_insert_wildcards + n_wildcards]
                    .iter()
                    .map(|typ| bctx.spanned_typed_new(pat.span, &typ, PatternX::Wildcard(true))),
            );

            PatternX::Tuple(Arc::new(patterns))
        }
        PatKind::TupleStruct(qpath, pats, dot_dot_pos) => {
            let res = bctx.types.qpath_res(qpath, pat.hir_id);
            let (adt_def_id, variant_def, _is_enum) = get_adt_res(tcx, res, pat.span)?;
            let variant_name = str_ident(&variant_def.ident(tcx).as_str());
            let vir_path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, adt_def_id);

            let (n_wildcards, pos_to_insert_wildcards) =
                handle_dot_dot(pats.len(), variant_def.fields.len(), &dot_dot_pos);

            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for (i, pat) in pats.iter().enumerate() {
                let actual_idx = if i < pos_to_insert_wildcards { i } else { i + n_wildcards };

                let pattern = pattern_to_vir(bctx, pat)?;
                let binder = ident_binder(&positional_field_ident(actual_idx), &pattern);
                binders.push(binder);
            }

            if n_wildcards > 0 {
                // Have to get the type for each wildcard to create the vir::Pattern
                let substs = match bctx.types.node_type(pat.hir_id).kind() {
                    TyKind::Adt(_, substs) => substs,
                    _ => {
                        return err_span(pat.span, "Verus internal error: expected Adt type");
                    }
                };
                let mut wildcard_binders = vec![];
                for i in 0..n_wildcards {
                    let actual_idx = i + pos_to_insert_wildcards;
                    let field_def = &variant_def.fields[actual_idx.into()];
                    let typ = field_def.ty(bctx.ctxt.tcx, substs);
                    let vir_typ = mid_ty_to_vir(
                        bctx.ctxt.tcx,
                        &bctx.ctxt.verus_items,
                        bctx.fun_id,
                        pat.span,
                        &typ,
                        false,
                    )?;
                    let pattern =
                        bctx.spanned_typed_new(pat.span, &vir_typ, PatternX::Wildcard(true));
                    wildcard_binders
                        .push(ident_binder(&positional_field_ident(actual_idx), &pattern));
                }

                binders.splice(
                    pos_to_insert_wildcards..pos_to_insert_wildcards,
                    wildcard_binders.into_iter(),
                );
            }

            PatternX::Constructor(vir_path, variant_name, Arc::new(binders))
        }
        PatKind::Struct(qpath, pats, _) => {
            let res = bctx.types.qpath_res(qpath, pat.hir_id);
            let (adt_def_id, variant_def, _is_enum) = get_adt_res(tcx, res, pat.span)?;
            let variant_name = str_ident(&variant_def.ident(tcx).as_str());
            let vir_path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, adt_def_id);

            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for fpat in pats.iter() {
                let pattern = pattern_to_vir(bctx, &fpat.pat)?;
                let binder = ident_binder(&str_ident(&fpat.ident.as_str()), &pattern);
                binders.push(binder);
            }
            PatternX::Constructor(vir_path, variant_name, Arc::new(binders))
        }
        PatKind::Box(pat) => {
            return pattern_to_vir(bctx, pat);
        }
        PatKind::Or(pats) => {
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
        PatKind::Binding(_, _, _, Some(_)) => unsupported_err!(pat.span, "@ patterns", pat),
        PatKind::Ref(..) => unsupported_err!(pat.span, "ref patterns", pat),
        PatKind::Lit(..) => unsupported_err!(pat.span, "literal patterns", pat),
        PatKind::Range(..) => unsupported_err!(pat.span, "range patterns", pat),
        PatKind::Slice(..) => unsupported_err!(pat.span, "slice patterns", pat),
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
    let attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
    attrs_is_invariant_block(attrs)
}

fn malformed_inv_block_err<'tcx>(expr: &Expr<'tcx>) -> Result<vir::ast::Expr, VirErr> {
    err_span(
        expr.span,
        "malformed invariant block; use `open_atomic_invariant!` or `open_local_invariant!` macro instead",
    )
}

pub(crate) fn invariant_block_open<'a>(
    verus_items: &verus_items::VerusItems,
    open_stmt: &'a Stmt,
) -> Option<(HirId, HirId, &'a rustc_hir::Pat<'a>, &'a rustc_hir::Expr<'a>, InvAtomicity)> {
    match open_stmt.kind {
        StmtKind::Local(Local {
            pat:
                Pat {
                    kind:
                        PatKind::Tuple(
                            [
                                Pat {
                                    kind:
                                        PatKind::Binding(
                                            BindingAnnotation(_, Mutability::Not),
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
                                            BindingAnnotation(_, Mutability::Mut),
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
        _ => None,
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

    if body.stmts.len() != 3 || body.expr.is_some() {
        return malformed_inv_block_err(expr);
    }

    let open_stmt = &body.stmts[0];
    let mid_stmt = &body.stmts[1];
    let close_stmt = &body.stmts[body.stmts.len() - 1];

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

    let name = Arc::new(pat_to_var(inner_pat)?);
    let inner_ty = typ_of_node(bctx, inner_pat.span, &inner_hir, false)?;
    let vir_binder = Arc::new(BinderX { name, a: inner_ty });

    let e = ExprX::OpenInvariant(vir_arg, vir_binder, vir_body, atomicity);
    Ok(bctx.spanned_typed_new(expr.span, &typ_of_node(bctx, expr.span, &expr.hir_id, false)?, e))
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) struct ExprModifier {
    /// dereferencing a mutable reference
    pub(crate) deref_mut: bool,
    /// taking a mutable reference
    pub(crate) addr_of: bool,
}

impl ExprModifier {
    pub(crate) const REGULAR: Self = Self { deref_mut: false, addr_of: false };

    #[allow(dead_code)]
    pub(crate) const DEREF_MUT: Self = Self { deref_mut: true, addr_of: false };

    pub(crate) const ADDR_OF: Self = Self { deref_mut: false, addr_of: true };
}

pub(crate) fn is_expr_typ_mut_ref<'tcx>(
    ty: rustc_middle::ty::Ty<'tcx>,
    modifier: ExprModifier,
) -> Result<ExprModifier, VirErr> {
    match ty.kind() {
        TyKind::Ref(_, _tys, rustc_ast::Mutability::Not) => Ok(modifier),
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

    if adjustment_idx == 0 {
        return expr_to_vir_innermost(bctx, expr, current_modifier);
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

    let adjustment = &adjustments[adjustment_idx - 1];

    match &adjustment.kind {
        Adjust::NeverToAny => expr_to_vir_with_adjustments(
            bctx,
            expr,
            current_modifier,
            adjustments,
            adjustment_idx - 1,
        ),
        Adjust::Deref(None) => {
            // handle same way as the UnOp::Deref case
            let new_modifier = is_expr_typ_mut_ref(get_inner_ty(), current_modifier)?;
            expr_to_vir_with_adjustments(bctx, expr, new_modifier, adjustments, adjustment_idx - 1)
        }
        Adjust::Deref(Some(_)) => {
            // note: deref has signature (&self) -> &Self::Target
            // and deref_mut has signature (&mut self) -> &mut Self::Target
            // The adjustment, though, goes from self -> Self::Target
            // without the refs.
            if auto_deref_supported_for_ty(bctx.ctxt.tcx, &get_inner_ty()) {
                expr_to_vir_with_adjustments(
                    bctx,
                    expr,
                    current_modifier,
                    adjustments,
                    adjustment_idx - 1,
                )
            } else {
                unsupported_err!(
                    expr.span,
                    &format!(
                        "overloaded deref (`{:}` is implicity converted to `{:}`)",
                        get_inner_ty(),
                        adjustment.target
                    )
                )
            }
        }
        Adjust::Borrow(AutoBorrow::Ref(_region, AutoBorrowMutability::Not)) => {
            // Similar to ExprKind::AddrOf
            expr_to_vir_with_adjustments(
                bctx,
                expr,
                ExprModifier::REGULAR,
                adjustments,
                adjustment_idx - 1,
            )
        }
        Adjust::Borrow(AutoBorrow::Ref(_region, AutoBorrowMutability::Mut { .. })) => {
            if current_modifier.deref_mut {
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
            unsupported_err!(
                expr.span,
                "unsizing operation (e.g., implicit cast from array [T; N] to slice [T])"
            );
        }
        Adjust::Pointer(_cast) => {
            unsupported_err!(expr.span, "casting a pointer (here the cast is implicit)")
        }
        Adjust::DynStar => {
            unsupported_err!(expr.span, "dyn cast (here the cast is implicit)")
        }
    }
}

pub(crate) fn expr_to_vir_innermost<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    current_modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    if bctx.external_body {
        // we want just requires/ensures, not the whole body
        match &expr.kind {
            ExprKind::Block(..) | ExprKind::Call(..) => {}
            _ => {
                return Ok(bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Block(Arc::new(vec![]), None),
                ));
            }
        }
    }

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

    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
    let expr_vattrs =
        get_verifier_attrs(expr_attrs, Some(&mut *bctx.ctxt.diagnostics.borrow_mut()))?;
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
                "the attribute #[verifier(truncate)] is only allowed on casts (you may need parentheses around the cast)",
            );
        }
    }

    match &expr.kind {
        ExprKind::Block(body, _) => {
            if is_invariant_block(bctx, expr)? {
                invariant_block_to_vir(bctx, expr, modifier)
            } else if let Some(g_attr) = get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(expr.hir_id))
            {
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
                block_to_vir(bctx, body, &expr.span, &expr_typ()?, modifier)
            }
        }
        ExprKind::Call(fun, args_slice) => {
            let res = match &fun.kind {
                // a tuple-style datatype constructor
                ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: res @ Res::Def(DefKind::Ctor(_, _), _), .. },
                )) => Some(expr_tuple_datatype_ctor_to_vir(
                    bctx,
                    expr,
                    res,
                    *args_slice,
                    fun.span,
                    modifier,
                )),
                ExprKind::Path(qpath) => {
                    let res = bctx.types.qpath_res(&qpath, fun.hir_id);
                    match res {
                        // A datatype constructor
                        rustc_hir::def::Res::Def(DefKind::Ctor(_, _), _)
                        | rustc_hir::def::Res::SelfCtor(_) => {
                            Some(expr_tuple_datatype_ctor_to_vir(
                                bctx,
                                expr,
                                &res,
                                *args_slice,
                                fun.span,
                                modifier,
                            ))
                        }
                        // a statically resolved function
                        rustc_hir::def::Res::Def(_, def_id) => {
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
                        rustc_hir::def::Res::Local(_) => {
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

                    let is_spec_fn = match &*undecorate_typ(&vir_fun.typ) {
                        TypX::Lambda(..) => true,
                        _ => false,
                    };

                    let (target, vir_args, resolved_call) = if is_spec_fn {
                        (CallTarget::FnSpec(vir_fun), vir_args, ResolvedCall::Spec)
                    } else {
                        // non-static calls are translated into a static call to
                        // `exec_nonstatic_call` which is defined in the pervasive lib.
                        let span = bctx.ctxt.spans.to_air_span(expr.span.clone());
                        let tup = vir::ast_util::mk_tuple(&span, &Arc::new(vir_args));
                        let helper_fun =
                            vir::def::exec_nonstatic_call_fun(&bctx.ctxt.vstd_crate_name);
                        let ret_typ = expr_typ.clone();

                        // Anything that goes in `typ_args` needs to have the correct
                        // decoration, so call mid_ty_to_vir for these
                        // Compute `tup_typ` with the correct decoration:
                        let mut arg_typs = vec![];
                        for arg in args {
                            arg_typs.push(mid_ty_to_vir(
                                tcx,
                                &bctx.ctxt.verus_items,
                                bctx.fun_id,
                                arg.span,
                                &bctx.types.expr_ty_adjusted(arg),
                                false,
                            )?);
                        }
                        let tup_typ = Arc::new(TypX::Tuple(Arc::new(arg_typs)));

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

                        let typ_args = Arc::new(vec![tup_typ, ret_typ, fun_typ]);
                        (
                            CallTarget::Fun(
                                vir::ast::CallTargetKind::Static,
                                helper_fun,
                                typ_args,
                                Arc::new(vec![]),
                                AutospecUsage::Final,
                            ),
                            vec![vir_fun, tup],
                            ResolvedCall::NonStaticExec,
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
            mk_expr(ExprX::Tuple(Arc::new(args?)))
        }
        ExprKind::Array(exprs) => {
            if bctx.ctxt.no_vstd {
                return err_span(expr.span, "Array literals are not supported with --no-vstd");
            }
            let args: Result<Vec<vir::ast::Expr>, VirErr> =
                exprs.iter().map(|e| expr_to_vir(bctx, e, modifier)).collect();
            mk_expr(ExprX::ArrayLiteral(Arc::new(args?)))
        }
        ExprKind::Lit(lit) => match lit.node {
            LitKind::Bool(b) => {
                let c = vir::ast::Constant::Bool(b);
                mk_expr(ExprX::Const(c))
            }
            LitKind::Int(i, _) => {
                mk_lit_int(false, i, typ_of_node(bctx, expr.span, &expr.hir_id, false)?)
            }
            LitKind::Char(c) => {
                let c = vir::ast::Constant::Char(c);
                mk_expr(ExprX::Const(c))
            }
            LitKind::Str(..) => {
                return err_span(
                    expr.span,
                    "Unsupported string constant (use new_strlit(\"...\") instead)",
                );
            }
            _ => {
                return err_span(expr.span, "Unsupported constant type");
            }
        },
        ExprKind::Cast(source, _) => {
            let source_vir = &expr_to_vir(bctx, source, modifier)?;
            let source_ty = &source_vir.typ;
            let to_ty = expr_typ()?;
            match (&*undecorate_typ(source_ty), &*undecorate_typ(&to_ty)) {
                (TypX::Int(_), TypX::Int(_)) => {
                    Ok(mk_ty_clip(&to_ty, &source_vir, expr_vattrs.truncate))
                }
                (TypX::Char, TypX::Int(_)) => {
                    let source_unicode =
                        mk_expr(ExprX::Unary(UnaryOp::CharToInt, source_vir.clone()))?;
                    Ok(mk_ty_clip(&to_ty, &source_unicode, expr_vattrs.truncate))
                }
                _ => {
                    return err_span(
                        expr.span,
                        "Verus currently only supports casts from integer types and `char` to integer types",
                    );
                }
            }
        }
        ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, e) => {
            expr_to_vir_inner(bctx, e, ExprModifier::REGULAR)
        }
        ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e) => {
            if current_modifier.deref_mut {
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
                let not_op = match (tc.expr_ty_adjusted(arg)).kind() {
                    TyKind::Adt(_, _) | TyKind::Uint(_) | TyKind::Int(_) => UnaryOp::BitNot,
                    TyKind::Bool => UnaryOp::Not,
                    _ => panic!("Internal error on UnOp::Not translation"),
                };
                let varg = expr_to_vir(bctx, arg, modifier)?;
                mk_expr(ExprX::Unary(not_op, varg))
            }
            UnOp::Neg => {
                let zero_const = vir::ast_util::const_int_from_u128(0);
                let zero = mk_expr(ExprX::Const(zero_const))?;
                let varg =
                    if let ExprKind::Lit(Spanned { node: LitKind::Int(i, _), .. }) = &arg.kind {
                        mk_lit_int(true, *i, typ_of_node(bctx, expr.span, &expr.hir_id, false)?)?
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
            UnOp::Deref => {
                let inner = expr_to_vir_inner(
                    bctx,
                    arg,
                    is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(arg), modifier)?,
                )?;
                Ok(inner)
            }
        },
        ExprKind::Binary(op, lhs, rhs) => {
            let vlhs = expr_to_vir(bctx, lhs, modifier)?;
            let vrhs = expr_to_vir(bctx, rhs, modifier)?;
            match op.node {
                BinOpKind::Eq | BinOpKind::Ne => unsupported_err_unless!(
                    is_smt_equality(bctx, expr.span, &lhs.hir_id, &rhs.hir_id)?,
                    expr.span,
                    "==/!= for non smt equality types"
                ),
                BinOpKind::Add
                | BinOpKind::Sub
                | BinOpKind::Mul
                | BinOpKind::Le
                | BinOpKind::Ge
                | BinOpKind::Lt
                | BinOpKind::Gt => unsupported_err_unless!(
                    is_smt_arith(bctx, lhs.span, rhs.span, &lhs.hir_id, &rhs.hir_id)?,
                    expr.span,
                    "cmp or arithmetic for non smt arithmetic types",
                    expr
                ),
                _ => (),
            }
            let mode_for_ghostness = if bctx.in_ghost { Mode::Spec } else { Mode::Exec };
            let vop = binopkind_to_binaryop(op, tc, lhs, rhs, mode_for_ghostness);
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
                            // Non-Euclidean division, which will need more encoding
                            unsupported_err!(expr.span, "div/mod on signed finite-width integers")
                        }
                    }
                }
                _ => Ok(e),
            }
        }
        ExprKind::Path(qpath) => {
            let res = bctx.types.qpath_res(&qpath, expr.hir_id);
            match res {
                Res::Local(id) => match tcx.hir().get(id) {
                    Node::Pat(pat) => mk_expr(if modifier.addr_of {
                        ExprX::VarLoc(Arc::new(pat_to_var(pat)?))
                    } else {
                        ExprX::Var(Arc::new(pat_to_var(pat)?))
                    }),
                    node => unsupported_err!(expr.span, format!("Path {:?}", node)),
                },
                Res::SelfCtor(_) | Res::Def(DefKind::Ctor(_, _), _) => {
                    expr_tuple_datatype_ctor_to_vir(bctx, expr, &res, &[], expr.span, modifier)
                }
                Res::Def(DefKind::AssocConst, id) => {
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
                        unsupported_err!(expr.span, "associated constants");
                    }
                }
                Res::Def(DefKind::Const, id) => {
                    let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, id);
                    let fun = FunX { path };
                    let autospec_usage =
                        if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };
                    mk_expr(ExprX::ConstVar(Arc::new(fun), autospec_usage))
                }
                Res::Def(DefKind::Static(Mutability::Not), id) => {
                    let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, id);
                    let fun = FunX { path };
                    mk_expr(ExprX::StaticVar(Arc::new(fun)))
                }
                Res::Def(DefKind::Fn | DefKind::AssocFn, _) => {
                    unsupported_err!(expr.span, "using functions as values");
                }
                Res::Def(DefKind::ConstParam, id) => {
                    let gparam = if let Some(local_id) = id.as_local() {
                        let hir_id = tcx.hir().local_def_id_to_hir_id(local_id);
                        match tcx.hir().get(hir_id) {
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
                res => unsupported_err!(expr.span, format!("Path {:?}", res)),
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
            let (datatype, variant_name, field_name) = if let Some(adt_def) = lhs_ty.ty_adt_def() {
                unsupported_err_unless!(
                    adt_def.variants().len() == 1,
                    expr.span,
                    "field_of_adt_with_multiple_variants",
                    expr
                );
                let datatype_path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, adt_def.did());
                let hir_def = bctx.ctxt.tcx.adt_def(adt_def.did());
                let variant = hir_def.variants().iter().next().unwrap();
                let variant_name = str_ident(&variant.ident(tcx).as_str());
                let field_name = match variant.ctor_kind() {
                    Some(rustc_hir::def::CtorKind::Fn) => {
                        let field_idx = variant
                            .fields
                            .iter()
                            .position(|f| f.ident(tcx).as_str() == name.as_str())
                            .expect("positional field not found");
                        positional_field_ident(field_idx)
                    }
                    None => str_ident(&name.as_str()),
                    Some(rustc_hir::def::CtorKind::Const) => panic!("unexpected tuple constructor"),
                };
                (datatype_path, variant_name, field_name)
            } else {
                let lhs_typ = typ_of_node(bctx, lhs.span, &lhs.hir_id, false)?;
                let lhs_typ = undecorate_typ(&lhs_typ);
                if let TypX::Tuple(ts) = &*lhs_typ {
                    let field: usize =
                        str::parse(&name.as_str()).expect("integer index into tuple");
                    let field_opr = UnaryOpr::TupleField { tuple_arity: ts.len(), field };
                    let vir = mk_expr(ExprX::UnaryOpr(field_opr, vir_lhs))?;
                    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                    erasure_info.resolved_exprs.push((expr.span.data(), vir.clone()));
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
                        datatype,
                        variant: variant_name,
                        field: field_name,
                        get_variant: false,
                    }),
                    vir_lhs,
                ),
            );
            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
            erasure_info.resolved_exprs.push((expr.span.data(), vir.clone()));
            Ok(vir)
        }
        ExprKind::If(cond, lhs, rhs) => {
            let cond = cond.peel_drop_temps();
            match cond.kind {
                ExprKind::Let(Let { hir_id: _, pat, init: expr, ty: _, span: _ }) => {
                    // if let
                    let vir_expr = expr_to_vir(bctx, expr, modifier)?;
                    let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
                    /* lhs */
                    {
                        let pattern = pattern_to_vir(bctx, pat)?;
                        let guard = mk_expr(ExprX::Const(Constant::Bool(true)))?;
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
                        let guard = mk_expr(ExprX::Const(Constant::Bool(true)))?;
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
                    None => mk_expr(ExprX::Const(Constant::Bool(true)))?,
                    Some(Guard::If(guard)) => expr_to_vir(bctx, guard, modifier)?,
                    Some(Guard::IfLet(_)) => unsupported_err!(expr.span, "Guard IfLet"),
                };
                let body = expr_to_vir(bctx, &arm.body, modifier)?;
                let vir_arm = ArmX { pattern, guard, body };
                vir_arms.push(bctx.spanned_new(arm.span, vir_arm));
            }
            mk_expr(ExprX::Match(vir_expr, Arc::new(vir_arms)))
        }
        ExprKind::Loop(block, label, LoopSource::Loop, _span) => {
            let typ = typ_of_node(bctx, block.span, &block.hir_id, false)?;
            let mut body = block_to_vir(bctx, block, &expr.span, &typ, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut body)?;
            let label = label.map(|l| l.ident.to_string());
            mk_expr(ExprX::Loop { label, cond: None, body, invs: header.loop_invariants() })
        }
        ExprKind::Loop(
            Block {
                stmts: [], expr: Some(Expr { kind: ExprKind::If(cond, body, other), .. }), ..
            },
            label,
            LoopSource::While,
            _span,
        ) => {
            // rustc desugars a while loop of the form `while cond { body }`
            // to `loop { if cond { body } else { break; } }`
            // We want to "un-desugar" it to represent it as a while loop.
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
            let header = vir::headers::read_header(&mut body)?;
            if header.decrease.len() > 0 {
                return err_span(expr.span, "termination checking of loops is not supported");
            }
            let label = label.map(|l| l.ident.to_string());
            mk_expr(ExprX::Loop { label, cond, body, invs: header.loop_invariants() })
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
        ExprKind::Struct(qpath, fields, spread) => {
            let update = match spread {
                None => None,
                Some(update) => Some(expr_to_vir(bctx, update, modifier)?),
            };

            let res = bctx.types.qpath_res(qpath, expr.hir_id);
            let (adt_def_id, variant_def, _is_enum) = get_adt_res(tcx, res, expr.span)?;
            let variant_name = str_ident(&variant_def.ident(tcx).as_str());
            let path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, adt_def_id);

            let vir_fields = Arc::new(
                fields
                    .iter()
                    .map(|f| -> Result<_, VirErr> {
                        let vir = expr_to_vir(bctx, f.expr, modifier)?;
                        Ok(ident_binder(&str_ident(&f.ident.as_str()), &vir))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
            let resolved_call = ResolvedCall::Ctor(path.clone(), variant_name.clone());
            erasure_info.resolved_calls.push((expr.hir_id, expr.span.data(), resolved_call));
            mk_expr(ExprX::Ctor(path, variant_name, vir_fields, update))
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
        ExprKind::Closure(..) => closure_to_vir(bctx, expr, expr_typ()?, false, modifier),
        ExprKind::Index(tgt_expr, idx_expr, _span) => {
            // Determine if this is Index or IndexMut
            // Based on ./rustc_mir_build/src/thir/cx/expr.rs in rustc
            // this is apparently determined by the (adjusted) type of the receiver
            let tgt_ty = bctx.types.expr_ty_adjusted(tgt_expr);
            let is_index_mut = match tgt_ty.kind() {
                TyKind::Array(_, _) => false,
                TyKind::Ref(_, _, Mutability::Not) => false,
                TyKind::Ref(_, _, Mutability::Mut) => true,
                _ => {
                    return err_span(
                        expr.span,
                        "Verus internal error: index operator expected & or &mut",
                    );
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
                TypX::Decorate(_, t) => t,
                _ => t1,
            };
            let (fun, typ_args) = match &**t1 {
                TypX::Datatype(p, typ_args, _impl_paths)
                    if p == &Arc::new(vir::ast::PathX {
                        krate: Some(Arc::new("alloc".to_string())),
                        segments: Arc::new(vec![
                            Arc::new("vec".to_string()),
                            Arc::new("Vec".to_string()),
                        ]),
                    }) =>
                {
                    let fun = vir::ast::FunX {
                        path: Arc::new(vir::ast::PathX {
                            krate: Some(Arc::new("vstd".to_string())),
                            segments: Arc::new(vec![
                                Arc::new("std_specs".to_string()),
                                Arc::new("vec".to_string()),
                                Arc::new("vec_index".to_string()),
                            ]),
                        }),
                    };
                    (fun, typ_args.clone())
                }
                TypX::Primitive(vir::ast::Primitive::Array, typ_args) => {
                    let fun = vir::ast::FunX {
                        path: Arc::new(vir::ast::PathX {
                            krate: Some(Arc::new("vstd".to_string())),
                            segments: Arc::new(vec![
                                Arc::new("array".to_string()),
                                Arc::new("array_index_get".to_string()),
                            ]),
                        }),
                    };
                    (fun, typ_args.clone())
                }
                _ => {
                    return err_span(
                        expr.span,
                        "in exec code, Verus only supports the index operator for Vec and array types",
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
                Arc::new(fun),
                typ_args,
                // arbitrary impl_path
                Arc::new(vec![vir::def::prefix_lambda_type(0)]),
                AutospecUsage::Final,
            );
            let args = Arc::new(vec![tgt_vir.clone(), idx_vir.clone()]);
            mk_expr(ExprX::Call(call_target, args))
        }
        ExprKind::Loop(..) => unsupported_err!(expr.span, format!("complex loop expressions")),
        ExprKind::Break(..) => unsupported_err!(expr.span, format!("complex break expressions")),
        ExprKind::AssignOp(op, lhs, rhs) => {
            if matches!(op.node, BinOpKind::Div | BinOpKind::Rem) {
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
        ExprKind::Repeat(..) => unsupported_err!(expr.span, format!("repeat expressions")),
        ExprKind::Yield(..) => unsupported_err!(expr.span, format!("yield expressions")),
        ExprKind::InlineAsm(..) => unsupported_err!(expr.span, format!("inline-asm expressions")),
        ExprKind::Err(..) => unsupported_err!(expr.span, format!("Err expressions")),
        ExprKind::Become(..) => unsupported_err!(expr.span, format!("Become expressions")),
    }
}

fn binopkind_to_binaryop(
    op: &Spanned<BinOpKind>,
    tc: &rustc_middle::ty::TypeckResults,
    lhs: &Expr,
    rhs: &Expr,
    mode_for_ghostness: Mode,
) -> BinaryOp {
    let vop = match op.node {
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
        BinOpKind::Shr => BinaryOp::Bitwise(BitwiseOp::Shr, mode_for_ghostness),
        BinOpKind::Shl => BinaryOp::Bitwise(BitwiseOp::Shl, mode_for_ghostness),
    };
    vop
}

fn expr_assign_to_vir_innermost<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    tc: &rustc_middle::ty::TypeckResults,
    lhs: &Expr<'tcx>,
    mk_expr: impl Fn(ExprX) -> Result<vir::ast::Expr, vir::messages::Message>,
    rhs: &Expr<'tcx>,
    modifier: ExprModifier,
    op_kind: Option<&Spanned<BinOpKind>>,
) -> Result<vir::ast::Expr, vir::messages::Message> {
    fn init_not_mut(bctx: &BodyCtxt, lhs: &Expr) -> Result<bool, VirErr> {
        Ok(match lhs.kind {
            ExprKind::Path(QPath::Resolved(None, rustc_hir::Path { res: Res::Local(id), .. })) => {
                let not_mut = if let Node::Pat(pat) = bctx.ctxt.tcx.hir().get(*id) {
                    let (mutable, _) = pat_to_mut_var(pat)?;
                    let ty = bctx.types.node_type(*id);
                    !(mutable || ty.ref_mutability() == Some(Mutability::Mut))
                } else {
                    panic!("assignment to non-local");
                };
                if not_mut {
                    match bctx.ctxt.tcx.hir().get_parent(*id) {
                        Node::Param(_) => err_span(lhs.span, "cannot assign to non-mut parameter")?,
                        Node::Local(_) => (),
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
                    false,
                    true,
                )?
                .1;
                unsupported_err_unless!(!deref_ghost, lhs.span, "assignment through Ghost/Tracked");
                init_not_mut(bctx, lhs)?
            }
            ExprKind::Unary(UnOp::Deref, _) => false,
            _ => {
                unsupported_err!(lhs.span, format!("assign lhs {:?}", lhs))
            }
        })
    }
    let mode_for_ghostness = if bctx.in_ghost { Mode::Spec } else { Mode::Exec };
    let op = op_kind.map(|op| binopkind_to_binaryop(op, tc, lhs, rhs, mode_for_ghostness));
    let init_not_mut = init_not_mut(bctx, lhs)?;
    mk_expr(ExprX::Assign {
        init_not_mut,
        lhs: expr_to_vir(bctx, lhs, ExprModifier::ADDR_OF)?,
        rhs: expr_to_vir(bctx, rhs, modifier)?,
        op: op,
    })
}

pub(crate) fn let_stmt_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pattern: &rustc_hir::Pat<'tcx>,
    initializer: &Option<&Expr<'tcx>>,
    attrs: &[Attribute],
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    let mode = get_var_mode(bctx.mode, attrs);
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
    Ok(vec![bctx.spanned_new(pattern.span, StmtX::Decl { pattern: vir_pattern, mode, init })])
}

fn unwrap_parameter_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    stmt1: &Stmt<'tcx>,
    stmt2: &Stmt<'tcx>,
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    // match "let x;"
    let x = if let StmtKind::Local(Local {
        pat:
            pat @ Pat {
                kind:
                    PatKind::Binding(BindingAnnotation(ByRef::No, Mutability::Not), hir_id, x, None),
                ..
            },
        ty: None,
        init: None,
        ..
    }) = &stmt1.kind
    {
        Some((pat.hir_id, Arc::new(local_to_var(x, hir_id.local_id))))
    } else {
        None
    };
    // match #[verifier(proof_block)]
    let ghost = get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(stmt2.hir_id));
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
            let vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            Ok(vec![bctx.spanned_new(expr.span, StmtX::Expr(vir_expr))])
        }
        StmtKind::Local(Local { pat, init, .. }) => {
            let_stmt_to_vir(bctx, pat, init, bctx.ctxt.tcx.hir().attrs(stmt.hir_id))
        }
        StmtKind::Item(item_id) => {
            let attrs = bctx.ctxt.tcx.hir().attrs(item_id.hir_id());
            let vattrs = get_verifier_attrs(attrs, Some(&mut *bctx.ctxt.diagnostics.borrow_mut()))?;
            if vattrs.internal_reveal_fn {
                dbg!(&item_id.hir_id());
                unreachable!();
            } else {
                unsupported_err!(stmt.span, "internal item statements", stmt)
            }
        }
    }
}

pub(crate) fn stmts_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    stmts: &mut impl Iterator<Item = &'tcx Stmt<'tcx>>,
) -> Result<Option<Vec<vir::ast::Stmt>>, VirErr> {
    if let Some(stmt) = stmts.next() {
        let attrs =
            crate::attributes::parse_attrs_opt(bctx.ctxt.tcx.hir().attrs(stmt.hir_id), None);
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

pub(crate) fn closure_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    closure_expr: &Expr<'tcx>,
    closure_vir_typ: Typ,
    is_spec_fn: bool,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    if let ExprKind::Closure(Closure { fn_decl, body: body_id, .. }) = &closure_expr.kind {
        unsupported_err_unless!(!fn_decl.c_variadic, closure_expr.span, "c_variadic");
        unsupported_err_unless!(
            matches!(fn_decl.implicit_self, rustc_hir::ImplicitSelfKind::None),
            closure_expr.span,
            "implicit_self in closure"
        );
        let body = bctx.ctxt.tcx.hir().body(*body_id);

        let typs = closure_param_typs(bctx, closure_expr)?;
        assert!(typs.len() == body.params.len());
        let params: Vec<Binder<Typ>> = body
            .params
            .iter()
            .zip(typs.clone())
            .map(|(x, t)| {
                let attrs = bctx.ctxt.tcx.hir().attrs(x.hir_id);
                let mode = crate::attributes::get_mode(Mode::Exec, attrs);
                if mode != Mode::Exec {
                    return err_span(x.span, "closures only accept exec-mode parameters");
                }

                let (is_mut, name) = pat_to_mut_var(x.pat)?;
                if is_mut {
                    return err_span(x.span, "Verus does not support 'mut' params for closures");
                }
                Ok(Arc::new(BinderX { name: Arc::new(name), a: t }))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut body = expr_to_vir(bctx, &body.value, modifier)?;

        let header = vir::headers::read_header(&mut body)?;
        let vir::headers::Header { require, ensure, ensure_id_typ, .. } = header;

        let exprx = if is_spec_fn {
            if require.len() > 0 || ensure.len() > 0 {
                return err_span(
                    closure_expr.span,
                    "SpecFn should not have `requires` clause or `ensures` clause",
                );
            }
            ExprX::Closure(Arc::new(params), body)
        } else {
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
                None => Arc::new(
                    vir::def::CLOSURE_RETURN_VALUE_PREFIX.to_string()
                        + &body_id.hir_id.local_id.index().to_string(),
                ),
            };

            let ret = Arc::new(BinderX { name: id, a: ret_typ });

            ExprX::ExecClosure {
                params: Arc::new(params),
                body,
                requires: require,
                ensures: ensure,
                ret: ret,
                external_spec: None, // filled in by ast_simplify
            }
        };
        Ok(bctx.spanned_typed_new(closure_expr.span, &closure_vir_typ, exprx))
    } else {
        panic!("closure_to_vir expects ExprKind::Closure");
    }
}
