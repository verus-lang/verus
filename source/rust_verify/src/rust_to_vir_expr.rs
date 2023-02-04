use crate::attributes::{
    get_ghost_block_opt, get_trigger, get_var_mode, get_verifier_attrs, parse_attrs, Attr,
    GetVariantField, GhostBlockAttr,
};
use crate::context::{BodyCtxt, Context};
use crate::erase::{CompilableOperator, ResolvedCall};
use crate::rust_to_vir_base::{
    def_id_to_vir_path, def_to_path_ident, get_function_def, get_range, hack_get_def_name,
    is_smt_arith, is_smt_equality, is_type_std_rc_or_arc, local_to_var, mid_ty_simplify,
    mid_ty_to_vir, mid_ty_to_vir_ghost, mk_range, typ_of_node, typ_of_node_expect_mut_ref,
    typ_path_and_ident_to_vir_path,
};
use crate::util::{
    err_span_str, err_span_string, slice_vec_map_result, spanned_new, spanned_typed_new,
    to_air_span, unsupported_err_span, vec_map, vec_map_result,
};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use air::ast::{Binder, BinderX};
use air::ast_util::str_ident;
use rustc_ast::{Attribute, BorrowKind, LitKind, Mutability};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    BinOpKind, BindingAnnotation, Block, Destination, Expr, ExprKind, Guard, HirId, Local,
    LoopSource, Node, Pat, PatKind, QPath, Stmt, StmtKind, UnOp,
};

use crate::rust_intrinsics_to_vir::int_intrinsic_constant_to_vir;
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{PredicateKind, TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_span::symbol::Symbol;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    ArithOp, ArmX, AssertQueryMode, BinaryOp, BitwiseOp, CallTarget, ComputeMode, Constant, ExprX,
    FieldOpr, FunX, HeaderExpr, HeaderExprX, Ident, InequalityOp, IntRange, IntegerTypeBoundKind,
    InvAtomicity, Mode, ModeCoercion, MultiOp, PatternX, Quant, SpannedTyped, StmtX, Stmts, Typ,
    TypX, UnaryOp, UnaryOpr, VarAt, VirErr,
};
use vir::ast_util::types_equal;
use vir::ast_util::{const_int_from_string, ident_binder, path_as_rust_name};
use vir::def::positional_field_ident;

pub(crate) fn pat_to_var<'tcx>(pat: &Pat) -> String {
    let (_, name) = pat_to_mut_var(pat);
    name
}

pub(crate) fn pat_to_mut_var<'tcx>(pat: &Pat) -> (bool, String) {
    let Pat { hir_id: _, kind, span: _, default_binding_modes } = pat;
    unsupported_unless!(default_binding_modes, "default_binding_modes");
    match kind {
        PatKind::Binding(annotation, id, ident, pat) => {
            let mutable = match annotation {
                BindingAnnotation::Unannotated => false,
                BindingAnnotation::Mutable => true,
                _ => {
                    unsupported!(format!("binding annotation {:?}", annotation))
                }
            };
            match pat {
                None => {}
                _ => {
                    unsupported!(format!("pattern {:?}", kind))
                }
            }
            (mutable, local_to_var(ident, id.local_id))
        }
        _ => {
            unsupported!(format!("pattern {:?}", kind))
        }
    }
}

fn extract_array<'tcx>(expr: &'tcx Expr<'tcx>) -> Vec<&'tcx Expr<'tcx>> {
    match &expr.kind {
        ExprKind::Array(fields) => fields.iter().collect(),
        _ => vec![expr],
    }
}

fn extract_tuple<'tcx>(expr: &'tcx Expr<'tcx>) -> Vec<&'tcx Expr<'tcx>> {
    match &expr.kind {
        ExprKind::Tup(exprs) => exprs.iter().collect(),
        _ => vec![expr],
    }
}

fn get_ensures_arg<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    if matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
        expr_to_vir(bctx, expr, ExprModifier::REGULAR)
    } else {
        err_span_str(expr.span, "ensures needs a bool expression")
    }
}

fn closure_param_typs<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr<'tcx>) -> Vec<Typ> {
    let node_type = bctx.types.node_type(expr.hir_id);
    match node_type.kind() {
        TyKind::Closure(_def, substs) => {
            let sig = substs.as_closure().sig();
            let args: Vec<Typ> = sig
                .inputs()
                .skip_binder() // REVIEW: rustc docs refer to skip_binder as "dangerous"
                .iter()
                .map(|t| mid_ty_to_vir(bctx.ctxt.tcx, t, false /* allow_mut_ref */))
                .collect();
            assert!(args.len() == 1);
            match &*args[0] {
                TypX::Tuple(typs) => (**typs).clone(),
                _ => panic!("expected tuple type"),
            }
        }
        _ => panic!("closure_param_types expected Closure type"),
    }
}

fn closure_ret_typ<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr<'tcx>) -> Typ {
    let node_type = bctx.types.node_type(expr.hir_id);
    match node_type.kind() {
        TyKind::Closure(_def, substs) => {
            let sig = substs.as_closure().sig();
            let t = sig.output().skip_binder();
            mid_ty_to_vir(bctx.ctxt.tcx, t, false /* allow_mut_ref */)
        }
        _ => panic!("closure_param_types expected Closure type"),
    }
}

fn extract_ensures<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Result<HeaderExpr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let typs: Vec<Typ> = closure_param_typs(bctx, expr);
            let body = tcx.hir().body(*body_id);
            let xs: Vec<String> = body.params.iter().map(|param| pat_to_var(param.pat)).collect();
            let expr = &body.value;
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(bctx, e))?;
            if typs.len() == 1 && xs.len() == 1 {
                let id_typ = Some((Arc::new(xs[0].clone()), typs[0].clone()));
                Ok(Arc::new(HeaderExprX::Ensures(id_typ, Arc::new(args))))
            } else {
                err_span_str(expr.span, "expected 1 parameter in closure")
            }
        }
        _ => {
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(bctx, e))?;
            Ok(Arc::new(HeaderExprX::Ensures(None, Arc::new(args))))
        }
    }
}

fn extract_quant<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    quant: Quant,
    expr: &'tcx Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let body = tcx.hir().body(*body_id);
            let typs = closure_param_typs(bctx, expr);
            assert!(typs.len() == body.params.len());
            let binders: Vec<Binder<Typ>> = body
                .params
                .iter()
                .zip(typs)
                .map(|(x, t)| Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)), a: t }))
                .collect();
            let expr = &body.value;
            let mut vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut vir_expr)?;
            if header.require.len() + header.ensure.len() > 0 {
                return err_span_str(expr.span, "forall/ensures cannot have requires/ensures");
            }
            let typ = Arc::new(TypX::Bool);
            if !matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
                return err_span_str(expr.span, "forall/ensures needs a bool expression");
            }
            Ok(spanned_typed_new(span, &typ, ExprX::Quant(quant, Arc::new(binders), vir_expr)))
        }
        _ => err_span_str(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn extract_assert_forall_by<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    expr: &'tcx Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let body = tcx.hir().body(*body_id);
            let typs = closure_param_typs(bctx, expr);
            assert!(body.params.len() == typs.len());
            let binders: Vec<Binder<Typ>> = body
                .params
                .iter()
                .zip(typs)
                .map(|(x, t)| Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)), a: t }))
                .collect();
            let expr = &body.value;
            let mut vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut vir_expr)?;
            if header.require.len() > 1 {
                return err_span_str(expr.span, "assert_forall_by can have at most one requires");
            }
            if header.ensure.len() != 1 {
                return err_span_str(expr.span, "assert_forall_by must have exactly one ensures");
            }
            if header.ensure_id_typ.is_some() {
                return err_span_str(expr.span, "ensures clause must be a bool");
            }
            let typ = Arc::new(TypX::Tuple(Arc::new(vec![])));
            let vars = Arc::new(binders);
            let require = if header.require.len() == 1 {
                header.require[0].clone()
            } else {
                spanned_typed_new(span, &Arc::new(TypX::Bool), ExprX::Const(Constant::Bool(true)))
            };
            let ensure = header.ensure[0].clone();
            let forallx = ExprX::Forall { vars, require, ensure, proof: vir_expr };
            Ok(spanned_typed_new(span, &typ, forallx))
        }
        _ => err_span_str(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn extract_choose<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    expr: &'tcx Expr<'tcx>,
    tuple: bool,
    expr_typ: Typ,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let closure_body = tcx.hir().body(*body_id);
            let mut params: Vec<Binder<Typ>> = Vec::new();
            let mut vars: Vec<vir::ast::Expr> = Vec::new();
            let typs = closure_param_typs(bctx, expr);
            assert!(closure_body.params.len() == typs.len());
            for (x, typ) in closure_body.params.iter().zip(typs) {
                let name = Arc::new(pat_to_var(x.pat));
                let vir_expr = spanned_typed_new(x.span, &typ, ExprX::Var(name.clone()));
                let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                erasure_info.hir_vir_ids.push((x.pat.hir_id, vir_expr.span.id));
                vars.push(vir_expr);
                params.push(Arc::new(BinderX { name, a: typ }));
            }
            let typs = vec_map(&params, |p| p.a.clone());
            let cond_expr = &closure_body.value;
            let cond = expr_to_vir(bctx, cond_expr, ExprModifier::REGULAR)?;
            let body = if tuple {
                let typ = Arc::new(TypX::Tuple(Arc::new(typs)));
                if !vir::ast_util::types_equal(&typ, &expr_typ) {
                    return err_span_string(
                        expr.span,
                        format!(
                            "expected choose_tuple to have type {:?}, found type {:?}",
                            typ, expr_typ
                        ),
                    );
                }
                spanned_typed_new(span, &typ, ExprX::Tuple(Arc::new(vars)))
            } else {
                if params.len() != 1 {
                    return err_span_str(
                        expr.span,
                        "choose expects exactly one parameter (use choose_tuple for multiple parameters)",
                    );
                }
                vars[0].clone()
            };
            let params = Arc::new(params);
            Ok(spanned_typed_new(span, &body.clone().typ, ExprX::Choose { params, cond, body }))
        }
        _ => err_span_str(expr.span, "argument to choose must be a closure"),
    }
}

/// If `expr` is of the form `closure_to_spec_fn(e)` then return `e`.
/// Otherwise, return `expr`.
///
/// This is needed because the syntax macro can often create expressions that look like:
/// forall(closure_to_fn_spec(|x| { ... }))

fn skip_closure_coercion<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    match &expr.kind {
        ExprKind::Call(fun, args_slice) => match &fun.kind {
            ExprKind::Path(qpath) => {
                let def = bctx.types.qpath_res(&qpath, fun.hir_id);
                match def {
                    rustc_hir::def::Res::Def(_, def_id) => {
                        let f_name = bctx.ctxt.tcx.def_path_str(def_id);
                        if f_name == "builtin::closure_to_fn_spec" {
                            return &args_slice[0];
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        },
        _ => {}
    }

    expr
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

fn mk_ty_clip<'tcx>(
    typ: &Typ,
    expr: &vir::ast::Expr,
    recommends_assume_truncate: bool,
) -> vir::ast::Expr {
    mk_clip(&get_range(typ), expr, recommends_assume_truncate)
}

fn check_lit_int(
    ctxt: &Context,
    span: Span,
    in_negative_literal: bool,
    i: u128,
    typ: &Typ,
) -> Result<(), VirErr> {
    let i_bump = if in_negative_literal { 1 } else { 0 };
    if let TypX::Int(range) = **typ {
        match range {
            IntRange::Int | IntRange::Nat => Ok(()),
            IntRange::U(n) if n == 128 || (n < 128 && i < (1u128 << n)) => Ok(()),
            IntRange::I(n) if n - 1 < 128 && i < (1u128 << (n - 1)) + i_bump => Ok(()),
            IntRange::USize if i < (1u128 << ctxt.arch.word_bits.min_bits()) => Ok(()),
            IntRange::ISize if i < (1u128 << (ctxt.arch.word_bits.min_bits() - 1)) + i_bump => {
                Ok(())
            }
            _ => {
                return err_span_str(span, "integer literal out of range");
            }
        }
    } else {
        return err_span_str(span, "expected integer type");
    }
}

pub(crate) fn expr_to_vir_inner<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = expr.peel_drop_temps();
    let vir_expr = expr_to_vir_innermost(bctx, expr, modifier)?;
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
    for group in get_trigger(bctx.ctxt.tcx.hir().attrs(expr.hir_id))? {
        vir_expr = vir_expr.new_x(ExprX::Unary(UnaryOp::Trigger(group), vir_expr.clone()));
    }
    Ok(vir_expr)
}

fn record_fun(
    ctxt: &crate::context::Context,
    hir_id: HirId,
    span: Span,
    name: &vir::ast::Fun,
    is_spec: bool,
    is_spec_allow_proof_args: bool,
    is_compilable_operator: Option<CompilableOperator>,
) {
    let mut erasure_info = ctxt.erasure_info.borrow_mut();
    let resolved_call = if is_spec {
        ResolvedCall::Spec
    } else if is_spec_allow_proof_args {
        ResolvedCall::SpecAllowProofArgs
    } else if let Some(op) = is_compilable_operator {
        ResolvedCall::CompilableOperator(op)
    } else {
        ResolvedCall::Call(name.clone())
    };
    erasure_info.resolved_calls.push((hir_id, span.data(), resolved_call));
}

fn get_fn_path<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr<'tcx>) -> Result<vir::ast::Fun, VirErr> {
    match &expr.kind {
        ExprKind::Path(qpath) => {
            let id = bctx.types.qpath_res(qpath, expr.hir_id).def_id();
            if let Some(_) =
                bctx.ctxt.tcx.impl_of_method(id).and_then(|ii| bctx.ctxt.tcx.trait_id_of_impl(ii))
            {
                unsupported_err!(expr.span, format!("Fn {:?}", id))
            } else {
                Ok(Arc::new(FunX { path: def_id_to_vir_path(bctx.ctxt.tcx, id), trait_path: None }))
            }
        }
        _ => unsupported_err!(expr.span, format!("{:?}", expr)),
    }
}

const BUILTIN_INV_LOCAL_BEGIN: &str = "crate::pervasive::invariant::open_local_invariant_begin";
const BUILTIN_INV_ATOMIC_BEGIN: &str = "crate::pervasive::invariant::open_atomic_invariant_begin";
const BUILTIN_INV_END: &str = "crate::pervasive::invariant::open_invariant_end";

fn fn_call_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    f: DefId,
    node_substs: &[rustc_middle::ty::subst::GenericArg<'tcx>],
    fn_span: Span,
    args_slice: &'tcx [Expr<'tcx>],
    autoview_typ: Option<&Typ>,
    defined_locally: bool,
    outer_modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let mut args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();

    let tcx = bctx.ctxt.tcx;
    let path = if let Some(autoview_typ) = autoview_typ {
        if let TypX::Datatype(type_path, _) = &**autoview_typ {
            // If the function call was originally Foo::X with autoview type Bar,
            // then use the function Bar::X instead.
            typ_path_and_ident_to_vir_path(type_path, def_to_path_ident(tcx, f))
        } else {
            panic!("autoview_typ must be Datatype");
        }
    } else {
        def_id_to_vir_path(tcx, f)
    };

    let (is_get_variant, autospec) = {
        match tcx.hir().get_if_local(f) {
            Some(rustc_hir::Node::ImplItem(
                impl_item @ rustc_hir::ImplItem { kind: rustc_hir::ImplItemKind::Fn(..), .. },
            )) => {
                let fn_attrs = bctx.ctxt.tcx.hir().attrs(impl_item.hir_id());
                let fn_vattrs = get_verifier_attrs(fn_attrs)?;
                let is_get_variant = if let Some(variant_ident) = fn_vattrs.is_variant {
                    Some((variant_ident, None))
                } else if let Some((variant_ident, field_ident)) = fn_vattrs.get_variant {
                    Some((variant_ident, Some(field_ident)))
                } else {
                    None
                };
                let autospec = match (bctx.in_ghost, fn_vattrs.autospec) {
                    (true, Some(method_name)) => Some(method_name),
                    _ => None,
                };
                (is_get_variant, autospec)
            }
            _ => (None, None),
        }
    };
    let path = if let Some(method_name) = autospec {
        crate::rust_to_vir_func::autospec_fun(&path, method_name)
    } else {
        path
    };

    let f_name = tcx.def_path_str(f);
    let is_admit = f_name == "builtin::admit";
    let is_no_method_body = f_name == "builtin::no_method_body";
    let is_requires = f_name == "builtin::requires";
    let is_recommends = f_name == "builtin::recommends";
    let is_ensures = f_name == "builtin::ensures";
    let is_invariant = f_name == "builtin::invariant";
    let is_invariant_ensures = f_name == "builtin::invariant_ensures";
    let is_decreases = f_name == "builtin::decreases";
    let is_decreases_when = f_name == "builtin::decreases_when";
    let is_decreases_by = f_name == "builtin::decreases_by" || f_name == "builtin::recommends_by";
    let is_opens_invariants_none = f_name == "builtin::opens_invariants_none";
    let is_opens_invariants_any = f_name == "builtin::opens_invariants_any";
    let is_opens_invariants = f_name == "builtin::opens_invariants";
    let is_opens_invariants_except = f_name == "builtin::opens_invariants_except";
    let is_forall = f_name == "builtin::forall";
    let is_exists = f_name == "builtin::exists";
    let is_forall_arith = f_name == "builtin::forall_arith";
    let is_choose = f_name == "builtin::choose";
    let is_choose_tuple = f_name == "builtin::choose_tuple";
    let is_with_triggers = f_name == "builtin::with_triggers";
    let is_equal = f_name == "builtin::equal";
    let is_chained_value = f_name == "builtin::spec_chained_value";
    let is_chained_le = f_name == "builtin::spec_chained_le";
    let is_chained_lt = f_name == "builtin::spec_chained_lt";
    let is_chained_ge = f_name == "builtin::spec_chained_ge";
    let is_chained_gt = f_name == "builtin::spec_chained_gt";
    let is_chained_cmp = f_name == "builtin::spec_chained_cmp";
    let is_hide = f_name == "builtin::hide";
    let is_extra_dependency = f_name == "builtin::extra_dependency";
    let is_reveal = f_name == "builtin::reveal";
    let is_reveal_fuel = f_name == "builtin::reveal_with_fuel";
    let is_implies = f_name == "builtin::imply";
    let is_assume = f_name == "builtin::assume_";
    let is_assert = f_name == "builtin::assert_";
    let is_assert_by = f_name == "builtin::assert_by";
    let is_assert_by_compute = f_name == "builtin::assert_by_compute";
    let is_assert_by_compute_only = f_name == "builtin::assert_by_compute_only";
    let is_assert_nonlinear_by = f_name == "builtin::assert_nonlinear_by";
    let is_assert_bitvector_by = f_name == "builtin::assert_bitvector_by";
    let is_assert_forall_by = f_name == "builtin::assert_forall_by";
    let is_assert_bit_vector = f_name == "builtin::assert_bit_vector";
    let is_old = f_name == "builtin::old";
    let is_eq = f_name == "core::cmp::PartialEq::eq";
    let is_ne = f_name == "core::cmp::PartialEq::ne";
    let is_le = f_name == "core::cmp::PartialOrd::le";
    let is_ge = f_name == "core::cmp::PartialOrd::ge";
    let is_lt = f_name == "core::cmp::PartialOrd::lt";
    let is_gt = f_name == "core::cmp::PartialOrd::gt";
    let is_builtin_add = f_name == "builtin::add";
    let is_builtin_sub = f_name == "builtin::sub";
    let is_builtin_mul = f_name == "builtin::mul";
    let is_add = f_name == "std::ops::Add::add";
    let is_sub = f_name == "std::ops::Sub::sub";
    let is_mul = f_name == "std::ops::Mul::mul";
    let is_spec_eq = f_name == "builtin::spec_eq";
    let is_spec_le = f_name == "builtin::SpecOrd::spec_le";
    let is_spec_ge = f_name == "builtin::SpecOrd::spec_ge";
    let is_spec_lt = f_name == "builtin::SpecOrd::spec_lt";
    let is_spec_gt = f_name == "builtin::SpecOrd::spec_gt";
    let is_spec_neg = f_name == "builtin::SpecNeg::spec_neg";
    let is_spec_add = f_name == "builtin::SpecAdd::spec_add";
    let is_spec_sub = f_name == "builtin::SpecSub::spec_sub";
    let is_spec_mul = f_name == "builtin::SpecMul::spec_mul";
    let is_spec_euclidean_div = f_name == "builtin::SpecEuclideanDiv::spec_euclidean_div";
    let is_spec_euclidean_mod = f_name == "builtin::SpecEuclideanMod::spec_euclidean_mod";
    let is_spec_bitand = f_name == "builtin::SpecBitAnd::spec_bitand";
    let is_spec_bitor = f_name == "builtin::SpecBitOr::spec_bitor";
    let is_spec_bitxor = f_name == "builtin::SpecBitXor::spec_bitxor";
    let is_spec_shl = f_name == "builtin::SpecShl::spec_shl";
    let is_spec_shr = f_name == "builtin::SpecShr::spec_shr";
    let is_spec_literal_integer = f_name == "builtin::spec_literal_integer";
    let is_spec_literal_int = f_name == "builtin::spec_literal_int";
    let is_spec_literal_nat = f_name == "builtin::spec_literal_nat";
    let is_spec_cast_integer = f_name == "builtin::spec_cast_integer";
    let is_panic = f_name == "core::panicking::panic";
    let is_ghost_view = f_name == "builtin::Ghost::<A>::view";
    let is_ghost_borrow = f_name == "builtin::Ghost::<A>::borrow";
    let is_ghost_borrow_mut = f_name == "builtin::Ghost::<A>::borrow_mut";
    let is_ghost_new = f_name == "builtin::Ghost::<A>::new";
    let is_ghost_exec = f_name == "pervasive::modes::ghost_exec";
    let is_ghost_split_tuple = f_name.starts_with("builtin::ghost_split_tuple");
    let is_tracked_view = f_name == "builtin::Tracked::<A>::view";
    let is_tracked_borrow = f_name == "builtin::Tracked::<A>::borrow";
    let is_tracked_borrow_mut = f_name == "builtin::Tracked::<A>::borrow_mut";
    let is_tracked_exec = f_name == "pervasive::modes::tracked_exec";
    let is_tracked_exec_borrow = f_name == "pervasive::modes::tracked_exec_borrow";
    let is_tracked_get = f_name == "builtin::Tracked::<A>::get";
    let is_tracked_split_tuple = f_name.starts_with("builtin::tracked_split_tuple");
    let is_new_strlit = tcx.is_diagnostic_item(Symbol::intern("pervasive::string::new_strlit"), f);

    let is_signed_min = f_name == "builtin::signed_min";
    let is_signed_max = f_name == "builtin::signed_max";
    let is_unsigned_max = f_name == "builtin::unsigned_max";
    let is_arch_word_bits = f_name == "builtin::arch_word_bits";
    let is_height = f_name == "builtin::height";

    let is_reveal_strlit = tcx.is_diagnostic_item(Symbol::intern("builtin::reveal_strlit"), f);
    let is_strslice_len = tcx.is_diagnostic_item(Symbol::intern("builtin::strslice_len"), f);
    let is_strslice_get_char =
        tcx.is_diagnostic_item(Symbol::intern("builtin::strslice_get_char"), f);
    let is_strslice_is_ascii =
        tcx.is_diagnostic_item(Symbol::intern("builtin::strslice_is_ascii"), f);
    let is_closure_to_fn_spec =
        tcx.is_diagnostic_item(Symbol::intern("builtin::closure_to_fn_spec"), f);

    let is_spec = is_admit
        || is_no_method_body
        || is_requires
        || is_recommends
        || is_ensures
        || is_invariant
        || is_invariant_ensures
        || is_decreases
        || is_decreases_when
        || is_decreases_by
        || is_opens_invariants_none
        || is_opens_invariants_any
        || is_opens_invariants
        || is_opens_invariants_except;
    let is_quant = is_forall || is_exists || is_forall_arith;
    let is_directive =
        is_extra_dependency || is_hide || is_reveal || is_reveal_fuel || is_reveal_strlit;
    let is_cmp = is_eq || is_ne || is_le || is_ge || is_lt || is_gt;
    let is_arith_binary =
        is_builtin_add || is_builtin_sub || is_builtin_mul || is_add || is_sub || is_mul;
    let is_spec_cmp =
        is_equal || is_spec_eq || is_spec_le || is_spec_ge || is_spec_lt || is_spec_gt;
    let is_spec_arith_binary =
        is_spec_add || is_spec_sub || is_spec_mul || is_spec_euclidean_div || is_spec_euclidean_mod;
    let is_spec_bitwise_binary =
        is_spec_bitand || is_spec_bitor || is_spec_bitxor || is_spec_shl || is_spec_shr;
    let is_chained_ineq = is_chained_le || is_chained_lt || is_chained_ge || is_chained_gt;
    let is_spec_literal = is_spec_literal_int || is_spec_literal_nat || is_spec_literal_integer;
    let is_spec_op = is_spec_cast_integer
        || is_spec_cmp
        || is_spec_arith_binary
        || is_spec_bitwise_binary
        || is_spec_neg
        || is_chained_ineq
        || is_spec_literal
        || is_chained_cmp
        || is_chained_value
        || is_chained_ineq;
    let is_spec_ghost_tracked =
        is_ghost_view || is_ghost_borrow || is_ghost_borrow_mut || is_ghost_new || is_tracked_view;

    // These functions are all no-ops in the SMT encoding, so we don't emit any VIR
    let is_smartptr_new = f_name == "std::boxed::Box::<T>::new"
        || f_name == "std::rc::Rc::<T>::new"
        || f_name == "std::sync::Arc::<T>::new";

    if f_name == BUILTIN_INV_ATOMIC_BEGIN
        || f_name == BUILTIN_INV_LOCAL_BEGIN
        || f_name == BUILTIN_INV_END
    {
        // `open_invariant_begin` and `open_invariant_end` calls should only appear
        // through use of the `open_invariant!` macro, which creates an invariant block.
        // Thus, they should end up being processed by `invariant_block_to_vir` before
        // we get here. Thus, for any well-formed use of an invariant block, we should
        // not reach this point.
        return err_span_string(
            expr.span,
            format!(
                "{} should never be used except through open_atomic_invariant or open_local_invariant macro",
                f_name
            ),
        );
    }

    if bctx.external_body
        && !is_requires
        && !is_recommends
        && !is_ensures
        && !is_opens_invariants_none
        && !is_opens_invariants_any
        && !is_opens_invariants
        && !is_opens_invariants_except
        && !is_extra_dependency
    {
        return Ok(spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Bool),
            ExprX::Block(Arc::new(vec![]), None),
        ));
    }

    if is_panic {
        return err_span_string(
            expr.span,
            format!(
                "panic is not supported (if you used Rust's `assert!` macro, you may have meant to use Verus's `assert` function)"
            ),
        );
    }

    unsupported_err_unless!(
        bctx.ctxt
            .tcx
            .impl_of_method(f)
            .and_then(|method_def_id| bctx.ctxt.tcx.trait_id_of_impl(method_def_id))
            .is_none(),
        expr.span,
        "call of trait impl"
    );
    let name = Arc::new(FunX { path: path.clone(), trait_path: None });

    record_fun(
        &bctx.ctxt,
        expr.hir_id,
        fn_span,
        &name,
        is_spec
            || is_quant
            || is_directive
            || is_choose
            || is_choose_tuple
            || is_with_triggers
            || is_assume
            || is_assert
            || is_assert_by
            || is_assert_by_compute
            || is_assert_by_compute_only
            || is_assert_nonlinear_by
            || is_assert_bitvector_by
            || is_assert_forall_by
            || is_assert_bit_vector
            || is_old
            || is_spec_ghost_tracked
            || is_closure_to_fn_spec
            || is_arch_word_bits
            || is_height,
        is_spec_op
            || is_get_variant.is_some()
            || is_builtin_add
            || is_builtin_sub
            || is_builtin_mul
            || is_signed_max
            || is_signed_min
            || is_unsigned_max,
        match () {
            _ if is_implies => Some(CompilableOperator::Implies),
            _ if is_smartptr_new => Some(CompilableOperator::SmartPtrNew),
            _ if is_new_strlit => Some(CompilableOperator::NewStrLit),
            _ if is_tracked_get => Some(CompilableOperator::TrackedGet),
            _ if is_tracked_borrow => Some(CompilableOperator::TrackedBorrow),
            _ if is_tracked_borrow_mut => Some(CompilableOperator::TrackedBorrowMut),
            _ if is_ghost_split_tuple => Some(CompilableOperator::GhostSplitTuple),
            _ if is_tracked_split_tuple => Some(CompilableOperator::TrackedSplitTuple),
            _ => None,
        },
    );

    let len = args.len();
    let expr_typ = || typ_of_node(bctx, &expr.hir_id, false);
    let mk_expr = |x: ExprX| spanned_typed_new(expr.span, &expr_typ(), x);
    let mk_expr_span = |span: Span, x: ExprX| spanned_typed_new(span, &expr_typ(), x);

    if is_spec_literal_int || is_spec_literal_nat || is_spec_literal_integer {
        unsupported_err_unless!(len == 1, expr.span, "expected spec_literal_*", &args);
        let arg = &args[0];
        let is_num = |s: &String| s.chars().count() > 0 && s.chars().all(|c| c.is_digit(10));
        match &args[0] {
            Expr { kind: ExprKind::Lit(Spanned { node: LitKind::Str(s, _), .. }), .. }
                if is_num(&s.to_string()) =>
            {
                // TODO: negative literals for is_spec_literal_int and is_spec_literal_integer
                if is_spec_literal_integer {
                    // TODO: big integers for int, nat
                    let i: u128 = match s.to_string().parse() {
                        Ok(i) => i,
                        Err(err) => {
                            return err_span_string(
                                arg.span,
                                format!("integer out of range {}", err),
                            );
                        }
                    };
                    let in_negative_literal = false;
                    check_lit_int(&bctx.ctxt, expr.span, in_negative_literal, i, &expr_typ())?
                }
                return Ok(mk_expr(ExprX::Const(const_int_from_string(s.to_string()))));
            }
            _ => {
                return err_span_str(arg.span, "spec_literal_* requires a string literal");
            }
        }
    }
    if is_no_method_body {
        return Ok(mk_expr(ExprX::Header(Arc::new(HeaderExprX::NoMethodBody))));
    }
    if is_requires || is_recommends {
        unsupported_err_unless!(len == 1, expr.span, "expected requires/recommends", &args);
        let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "requires/recommends needs a bool expression");
            }
        }
        let vir_args = vec_map_result(&args, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
        let header = if is_requires {
            Arc::new(HeaderExprX::Requires(Arc::new(vir_args)))
        } else {
            Arc::new(HeaderExprX::Recommends(Arc::new(vir_args)))
        };
        return Ok(mk_expr(ExprX::Header(header)));
    }
    if is_opens_invariants || is_opens_invariants_except {
        return err_span_str(
            expr.span,
            "'is_opens_invariants' and 'is_opens_invariants_except' are not yet implemented",
        );
    }
    if is_opens_invariants_none {
        let header = Arc::new(HeaderExprX::InvariantOpens(Arc::new(Vec::new())));
        return Ok(mk_expr(ExprX::Header(header)));
    }
    if is_opens_invariants_any {
        let header = Arc::new(HeaderExprX::InvariantOpensExcept(Arc::new(Vec::new())));
        return Ok(mk_expr(ExprX::Header(header)));
    }
    if is_ensures {
        unsupported_err_unless!(len == 1, expr.span, "expected ensures", &args);
        let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
        let header = extract_ensures(&bctx, args[0])?;
        let expr = mk_expr_span(args[0].span, ExprX::Header(header));
        // extract_ensures does most of the necessary work, so we can return at this point
        return Ok(expr);
    }
    if is_invariant || is_invariant_ensures {
        unsupported_err_unless!(len == 1, expr.span, "expected invariant", &args);
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "invariant needs a bool expression");
            }
        }
    }
    if is_decreases {
        unsupported_err_unless!(len == 1, expr.span, "expected decreases", &args);
        args = extract_tuple(args[0]);
    }
    if is_forall || is_exists || is_forall_arith {
        unsupported_err_unless!(len == 1, expr.span, "expected forall/exists", &args);
        let quant = if is_forall || is_forall_arith {
            air::ast::Quant::Forall
        } else {
            air::ast::Quant::Exists
        };
        let quant = Quant { quant, boxed_params: !is_forall_arith };
        return extract_quant(bctx, expr.span, quant, args[0]);
    }
    if is_closure_to_fn_spec {
        unsupported_err_unless!(len == 1, expr.span, "expected closure_to_spec_fn", &args);
        if let ExprKind::Closure(..) = &args[0].kind {
            return closure_to_vir(bctx, &args[0], expr_typ(), true, ExprModifier::REGULAR);
        } else {
            return err_span_str(
                args[0].span,
                "the argument to `closure_to_spec_fn` must be a closure",
            );
        }
    }

    if is_choose {
        unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
        return extract_choose(bctx, expr.span, args[0], false, expr_typ());
    }
    if is_choose_tuple {
        unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
        return extract_choose(bctx, expr.span, args[0], true, expr_typ());
    }
    if is_with_triggers {
        unsupported_err_unless!(len == 2, expr.span, "expected with_triggers", &args);
        let modifier = ExprModifier::REGULAR;
        let triggers_tuples = expr_to_vir(bctx, args[0], modifier)?;
        let body = expr_to_vir(bctx, args[1], modifier)?;
        let mut trigs: Vec<vir::ast::Exprs> = Vec::new();
        if let ExprX::Tuple(triggers) = &triggers_tuples.x {
            for trigger_tuple in triggers.iter() {
                if let ExprX::Tuple(terms) = &trigger_tuple.x {
                    trigs.push(terms.clone());
                } else {
                    return err_span_str(expr.span, "expected tuple arguments to with_triggers");
                }
            }
        } else {
            return err_span_str(expr.span, "expected tuple arguments to with_triggers");
        }
        let triggers = Arc::new(trigs);
        return Ok(mk_expr(ExprX::WithTriggers { triggers, body }));
    }
    if is_old {
        if let ExprKind::Path(QPath::Resolved(None, rustc_hir::Path { res: Res::Local(id), .. })) =
            &args[0].kind
        {
            if let Node::Binding(pat) = tcx.hir().get(*id) {
                let typ = typ_of_node_expect_mut_ref(bctx, &expr.hir_id, args[0].span)?;
                return Ok(spanned_typed_new(
                    expr.span,
                    &typ,
                    ExprX::VarAt(Arc::new(pat_to_var(pat)), VarAt::Pre),
                ));
            }
        }
        return err_span_str(
            expr.span,
            "only a variable binding is allowed as the argument to old",
        );
    }

    if is_ghost_exec || is_tracked_exec {
        unsupported_err_unless!(len == 1, expr.span, "expected Ghost/Tracked", &args);
        let arg = &args[0];
        if get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(expr.hir_id))
            == Some(GhostBlockAttr::Wrapper)
        {
            let vir_arg = expr_to_vir(bctx, arg, ExprModifier::REGULAR)?;
            let alloc_wrapper = Some(name);
            match (is_tracked_exec, get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(arg.hir_id))) {
                (false, Some(GhostBlockAttr::GhostWrapped)) => {
                    return Ok(mk_expr(ExprX::Ghost {
                        alloc_wrapper,
                        tracked: false,
                        expr: vir_arg,
                    }));
                }
                (true, Some(GhostBlockAttr::TrackedWrapped)) => {
                    return Ok(mk_expr(ExprX::Ghost {
                        alloc_wrapper,
                        tracked: true,
                        expr: vir_arg,
                    }));
                }
                (_, attr) => {
                    return err_span_string(
                        expr.span,
                        format!("unexpected ghost block attribute {:?}", attr),
                    );
                }
            }
        }
    }

    if is_decreases_by {
        unsupported_err_unless!(len == 1, expr.span, "expected function", &args);
        let x = get_fn_path(bctx, &args[0])?;
        let header = Arc::new(HeaderExprX::DecreasesBy(x));
        return Ok(mk_expr(ExprX::Header(header)));
    }
    if is_extra_dependency || is_hide || is_reveal {
        unsupported_err_unless!(len == 1, expr.span, "expected hide/reveal", &args);
        let x = get_fn_path(bctx, &args[0])?;
        if is_hide {
            let header = Arc::new(HeaderExprX::Hide(x));
            return Ok(mk_expr(ExprX::Header(header)));
        } else if is_extra_dependency {
            let header = Arc::new(HeaderExprX::ExtraDependency(x));
            return Ok(mk_expr(ExprX::Header(header)));
        } else {
            return Ok(mk_expr(ExprX::Fuel(x, 1)));
        }
    }
    if is_reveal_fuel {
        unsupported_err_unless!(len == 2, expr.span, "expected reveal_fuel", &args);
        let x = get_fn_path(bctx, &args[0])?;
        match &expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?.x {
            ExprX::Const(Constant::Int(i)) => {
                let n = vir::ast_util::const_int_to_u32(&to_air_span(expr.span), i)?;
                return Ok(mk_expr(ExprX::Fuel(x, n)));
            }
            _ => panic!("internal error: is_reveal_fuel"),
        }
    }
    if is_assert_by {
        unsupported_err_unless!(len == 2, expr.span, "expected assert_by", &args);
        let vars = Arc::new(vec![]);
        let require =
            spanned_typed_new(expr.span, &Arc::new(TypX::Bool), ExprX::Const(Constant::Bool(true)));
        let ensure = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        let proof = expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?;
        return Ok(mk_expr(ExprX::Forall { vars, require, ensure, proof }));
    }
    if is_assert_by_compute {
        unsupported_err_unless!(len == 1, expr.span, "expected assert_by_compute", &args);
        let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        return Ok(mk_expr(ExprX::AssertCompute(exp, ComputeMode::Z3)));
    }
    if is_assert_by_compute_only {
        unsupported_err_unless!(len == 1, expr.span, "expected assert_by_compute_only", &args);
        let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        return Ok(mk_expr(ExprX::AssertCompute(exp, ComputeMode::ComputeOnly)));
    }
    if is_assert_nonlinear_by || is_assert_bitvector_by {
        unsupported_err_unless!(
            len == 1,
            expr.span,
            "expected assert_nonlinear_by/assert_bitvector_by with one argument",
            &args
        );
        let mut vir_expr = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        let header = vir::headers::read_header(&mut vir_expr)?;
        let requires = if header.require.len() >= 1 {
            header.require
        } else {
            Arc::new(vec![spanned_typed_new(
                expr.span,
                &Arc::new(TypX::Bool),
                ExprX::Const(Constant::Bool(true)),
            )])
        };
        if header.ensure.len() == 0 {
            return err_span_str(
                expr.span,
                "assert_nonlinear_by/assert_bitvector_by must have at least one ensures",
            );
        }
        let ensures = header.ensure;
        let proof = vir_expr;

        let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
        let expr_vattrs = get_verifier_attrs(expr_attrs)?;
        if expr_vattrs.spinoff_prover {
            return err_span_str(
                expr.span,
                "#[verifier(spinoff_prover)] is implied for assert by nonlinear_arith and assert by bit_vector",
            );
        }
        return Ok(mk_expr(ExprX::AssertQuery {
            requires,
            ensures,
            proof,
            mode: if is_assert_nonlinear_by {
                AssertQueryMode::NonLinear
            } else {
                AssertQueryMode::BitVector
            },
        }));
    }
    if is_assert_forall_by {
        unsupported_err_unless!(len == 1, expr.span, "expected assert_forall_by", &args);
        return extract_assert_forall_by(bctx, expr.span, args[0]);
    }

    // internally translate this into `assert_bitvector_by`. REVIEW: consider deprecating this at all
    if is_assert_bit_vector {
        let vir_expr = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        let requires = Arc::new(vec![spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Bool),
            ExprX::Const(Constant::Bool(true)),
        )]);
        let ensures = Arc::new(vec![vir_expr]);
        let proof = spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Tuple(Arc::new(vec![]))),
            ExprX::Block(Arc::new(vec![]), None),
        );
        return Ok(mk_expr(ExprX::AssertQuery {
            requires,
            ensures,
            proof,
            mode: AssertQueryMode::BitVector,
        }));
    }

    if is_signed_min || is_signed_max || is_unsigned_max {
        assert!(args.len() == 1);
        let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;

        let kind = if is_signed_min {
            IntegerTypeBoundKind::SignedMin
        } else if is_signed_max {
            IntegerTypeBoundKind::SignedMax
        } else {
            IntegerTypeBoundKind::UnsignedMax
        };

        return Ok(mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg)));
    }
    if is_arch_word_bits {
        assert!(args.len() == 0);
        let arg = spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Int(IntRange::Int)),
            ExprX::Const(vir::ast_util::const_int_from_u128(0)),
        );

        let kind = IntegerTypeBoundKind::ArchWordBits;

        return Ok(mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg)));
    }

    if is_height {
        assert!(args.len() == 1);
        let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        return Ok(mk_expr(ExprX::UnaryOpr(UnaryOpr::Height, arg)));
    }

    if is_smartptr_new {
        unsupported_err_unless!(len == 1, expr.span, "expected 1 argument", &args);
        let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;

        return Ok(arg);
    }

    let inputs: Box<dyn Iterator<Item = Option<_>>> = if let Some(f_local) = f.as_local() {
        let f_hir_id = bctx.ctxt.tcx.hir().local_def_id_to_hir_id(f_local);
        let inputs = get_function_def(bctx.ctxt.tcx, f_hir_id).0.decl.inputs;
        Box::new(inputs.iter().map(Some).into_iter())
    } else {
        Box::new(std::iter::repeat(None))
    };

    if is_new_strlit {
        let s = if let ExprKind::Lit(lit0) = &args[0].kind {
            if let rustc_ast::LitKind::Str(s, _) = lit0.node {
                s
            } else {
                panic!("unexpected arguments to new_strlit")
            }
        } else {
            panic!("unexpected arguments to new_strlit")
        };

        let c = vir::ast::Constant::StrSlice(Arc::new(s.to_string()));
        return Ok(mk_expr(ExprX::Const(c)));
    }

    if is_reveal_strlit {
        if let Some(s) = if let ExprKind::Lit(lit0) = &args[0].kind {
            if let rustc_ast::LitKind::Str(s, _) = lit0.node { Some(s) } else { None }
        } else {
            None
        } {
            return Ok(mk_expr(ExprX::RevealString(Arc::new(s.to_string()))));
        } else {
            return err_span_string(args[0].span, "string literal expected".to_string());
        }
    }

    if is_strslice_get_char {
        return match &expr.kind {
            ExprKind::Call(_, args) if args.len() == 2 => {
                let arg0 = args.first().unwrap();
                let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR).expect(
                    "invalid parameter for builtin::strslice_get_char at arg0, arg0 must be self",
                );
                let arg1 = &args[1];
                let arg1 = expr_to_vir(bctx, arg1, ExprModifier::REGULAR)
                    .expect("invalid parameter for builtin::strslice_get_char at arg1, arg1 must be an integer");
                Ok(mk_expr(ExprX::Binary(BinaryOp::StrGetChar, arg0, arg1)))
            }
            _ => panic!(
                "Expected a call for builtin::strslice_get_char with two argument but did not receive it"
            ),
        };
    }

    if is_strslice_len {
        return match &expr.kind {
            ExprKind::Call(_, args) => {
                assert!(args.len() == 1);
                let arg0 = args.first().unwrap();
                let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR)
                    .expect("internal compiler error");
                Ok(mk_expr(ExprX::Unary(UnaryOp::StrLen, arg0)))
            }
            _ => panic!(
                "Expected a call for builtin::strslice_len with one argument but did not receive it"
            ),
        };
    }

    if is_strslice_is_ascii {
        return match &expr.kind {
            ExprKind::Call(_, args) => {
                assert!(args.len() == 1);
                let arg0 = args.first().unwrap();
                let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR)
                    .expect("internal compiler error");
                Ok(mk_expr(ExprX::Unary(UnaryOp::StrIsAscii, arg0)))
            }
            _ => panic!(
                "Expected a call for builtin::strslice_is_ascii with one argument but did not receive it"
            ),
        };
    }

    let mut vir_args = args
        .iter()
        .zip(inputs)
        .map(|(arg, param)| {
            let is_mut_ref_param = match param {
                Some(rustc_hir::Ty {
                    kind:
                        rustc_hir::TyKind::Rptr(
                            _,
                            rustc_hir::MutTy { mutbl: rustc_hir::Mutability::Mut, .. },
                        ),
                    ..
                }) => true,
                _ => false,
            };
            if is_mut_ref_param {
                let arg_x = match &arg.kind {
                    ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e) => e,
                    _ => arg,
                };
                let deref_mut = match bctx.types.node_type(arg_x.hir_id).ref_mutability() {
                    Some(Mutability::Mut) => true,
                    _ => false,
                };
                let expr = expr_to_vir(bctx, arg_x, ExprModifier { addr_of: true, deref_mut })?;
                Ok(spanned_typed_new(arg.span, &expr.typ.clone(), ExprX::Loc(expr)))
            } else if is_decreases || is_invariant || is_invariant_ensures {
                let bctx = &BodyCtxt { in_ghost: true, ..bctx.clone() };
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, ExprModifier::REGULAR)?)
            } else if is_ghost_borrow_mut || is_tracked_borrow_mut {
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, outer_modifier)?)
            } else {
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, ExprModifier::REGULAR)?)
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let self_path = if let Some(autoview_typ) = autoview_typ {
        // replace f(arg0, arg1, ..., argn) with f(arg0.view(), arg1, ..., argn)
        let typ_args = if let TypX::Datatype(_, args) = &**autoview_typ {
            args.clone()
        } else {
            panic!("autoview_typ must be Datatype")
        };

        let receiver = args.first().expect("receiver in method call");
        let self_path = match &(*typ_of_node(bctx, &receiver.hir_id, true)) {
            TypX::Datatype(path, _) => path.clone(),
            _ => panic!("unexpected receiver type"),
        };
        let view_path = typ_path_and_ident_to_vir_path(&self_path, Arc::new("view".to_string()));

        let fun = Arc::new(FunX { path: view_path, trait_path: None });
        let target = CallTarget::Static(fun, typ_args);
        let viewx = ExprX::Call(target, Arc::new(vec![vir_args[0].clone()]));
        vir_args[0] = spanned_typed_new(expr.span, autoview_typ, viewx);
        self_path
    } else {
        let mut self_path = path.clone();
        let self_path_mut = Arc::make_mut(&mut self_path);
        Arc::make_mut(&mut self_path_mut.segments).pop();
        self_path
    };

    match is_get_variant {
        Some((variant_name, None)) => {
            return Ok(mk_expr(ExprX::UnaryOpr(
                UnaryOpr::IsVariant { datatype: self_path, variant: str_ident(&variant_name) },
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            )));
        }
        Some((variant_name, Some(variant_field))) => {
            let variant_name_ident = str_ident(&variant_name);
            return Ok(mk_expr(ExprX::UnaryOpr(
                UnaryOpr::Field(FieldOpr {
                    datatype: self_path.clone(),
                    variant: variant_name_ident.clone(),
                    field: match variant_field {
                        GetVariantField::Named(n) => str_ident(&n),
                        GetVariantField::Unnamed(i) => positional_field_ident(i),
                    },
                }),
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            )));
        }
        None => {}
    }

    let is_smt_unary = if is_spec_neg {
        match *typ_of_node(bctx, &args[0].hir_id, false) {
            TypX::Int(_) => true,
            _ => false,
        }
    } else {
        false
    };

    let is_smt_binary = if is_equal {
        true
    } else if is_spec_eq {
        let t1 = typ_of_node(bctx, &args[0].hir_id, true);
        let t2 = typ_of_node(bctx, &args[1].hir_id, true);
        if types_equal(&t1, &t2) || is_smt_arith(bctx, &args[0].hir_id, &args[1].hir_id) {
            true
        } else {
            return err_span_str(expr.span, "types must be compatible to use == or !=");
        }
    } else if is_eq || is_ne {
        is_smt_equality(bctx, expr.span, &args[0].hir_id, &args[1].hir_id)
    } else if is_cmp
        || is_arith_binary
        || is_implies
        || is_spec_cmp
        || is_spec_arith_binary
        || is_spec_bitwise_binary
    {
        is_smt_arith(bctx, &args[0].hir_id, &args[1].hir_id)
    } else {
        false
    };

    if is_invariant {
        let header = Arc::new(HeaderExprX::Invariant(Arc::new(vir_args)));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_invariant_ensures {
        let header = Arc::new(HeaderExprX::InvariantEnsures(Arc::new(vir_args)));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_decreases {
        let header = Arc::new(HeaderExprX::Decreases(Arc::new(vir_args)));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_decreases_when {
        unsupported_err_unless!(len == 1, expr.span, "expected decreases_when", &args);
        let header = Arc::new(HeaderExprX::DecreasesWhen(vir_args[0].clone()));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_admit {
        unsupported_err_unless!(len == 0, expr.span, "expected admit", args);
        let f = spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Bool),
            ExprX::Const(Constant::Bool(false)),
        );
        Ok(mk_expr(ExprX::AssertAssume { is_assume: true, expr: f }))
    } else if is_assume {
        unsupported_err_unless!(len == 1, expr.span, "expected assume", args);
        Ok(mk_expr(ExprX::AssertAssume { is_assume: true, expr: vir_args[0].clone() }))
    } else if is_assert {
        unsupported_err_unless!(len == 1, expr.span, "expected assert", args);
        Ok(mk_expr(ExprX::AssertAssume { is_assume: false, expr: vir_args[0].clone() }))
    } else if is_spec_cast_integer {
        unsupported_err_unless!(len == 1, expr.span, "spec_cast_integer", args);
        let source_vir = vir_args[0].clone();
        let source_ty = &source_vir.typ;
        let to_ty = expr_typ();
        match (&**source_ty, &*to_ty) {
            (TypX::Int(IntRange::U(_)), TypX::Int(IntRange::Nat)) => Ok(source_vir),
            (TypX::Int(IntRange::USize), TypX::Int(IntRange::Nat)) => Ok(source_vir),
            (TypX::Int(IntRange::Nat), TypX::Int(IntRange::Nat)) => Ok(source_vir),
            (TypX::Int(IntRange::Int), TypX::Int(IntRange::Nat)) => {
                return Ok(mk_ty_clip(&to_ty, &source_vir, true));
            }
            (TypX::Int(_), TypX::Int(_)) => {
                let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                return Ok(mk_ty_clip(&to_ty, &source_vir, expr_vattrs.truncate));
            }
            (TypX::Char, TypX::Int(_)) => {
                let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                let source_unicode = mk_expr(ExprX::Unary(UnaryOp::CharToInt, source_vir.clone()));
                return Ok(mk_ty_clip(&to_ty, &source_unicode, expr_vattrs.truncate));
            }
            _ => {
                return err_span_str(
                    expr.span,
                    "Verus currently only supports casts from integer types and `char` to integer types",
                );
            }
        }
    } else if is_smt_unary {
        unsupported_err_unless!(len == 1, expr.span, "expected unary op", args);
        let varg = vir_args[0].clone();
        if is_spec_neg {
            let zero_const = vir::ast_util::const_int_from_u128(0);
            let zero = mk_expr(ExprX::Const(zero_const));
            Ok(mk_expr(ExprX::Binary(BinaryOp::Arith(ArithOp::Sub, None), zero, varg)))
        } else {
            panic!("internal error")
        }
    } else if is_smt_binary {
        unsupported_err_unless!(len == 2, expr.span, "expected binary op", args);
        let lhs = vir_args[0].clone();
        let rhs = vir_args[1].clone();
        let vop = if is_equal || is_spec_eq {
            BinaryOp::Eq(Mode::Spec)
        } else if is_eq {
            BinaryOp::Eq(Mode::Exec)
        } else if is_ne {
            BinaryOp::Ne
        } else if is_le || is_spec_le {
            BinaryOp::Inequality(InequalityOp::Le)
        } else if is_ge || is_spec_ge {
            BinaryOp::Inequality(InequalityOp::Ge)
        } else if is_lt || is_spec_lt {
            BinaryOp::Inequality(InequalityOp::Lt)
        } else if is_gt || is_spec_gt {
            BinaryOp::Inequality(InequalityOp::Gt)
        } else if is_add || is_builtin_add {
            BinaryOp::Arith(ArithOp::Add, Some(bctx.ctxt.infer_mode()))
        } else if is_sub || is_builtin_sub {
            BinaryOp::Arith(ArithOp::Sub, Some(bctx.ctxt.infer_mode()))
        } else if is_mul || is_builtin_mul {
            BinaryOp::Arith(ArithOp::Mul, Some(bctx.ctxt.infer_mode()))
        } else if is_spec_add {
            BinaryOp::Arith(ArithOp::Add, None)
        } else if is_spec_sub {
            BinaryOp::Arith(ArithOp::Sub, None)
        } else if is_spec_mul {
            BinaryOp::Arith(ArithOp::Mul, None)
        } else if is_spec_euclidean_div {
            BinaryOp::Arith(ArithOp::EuclideanDiv, None)
        } else if is_spec_euclidean_mod {
            BinaryOp::Arith(ArithOp::EuclideanMod, None)
        } else if is_spec_bitand {
            BinaryOp::Bitwise(BitwiseOp::BitAnd)
        } else if is_spec_bitor {
            BinaryOp::Bitwise(BitwiseOp::BitOr)
        } else if is_spec_bitxor {
            if matches!(*vir_args[0].typ, TypX::Bool) {
                BinaryOp::Xor
            } else {
                BinaryOp::Bitwise(BitwiseOp::BitXor)
            }
        } else if is_spec_shl {
            BinaryOp::Bitwise(BitwiseOp::Shl)
        } else if is_spec_shr {
            BinaryOp::Bitwise(BitwiseOp::Shr)
        } else if is_implies {
            BinaryOp::Implies
        } else {
            panic!("internal error")
        };
        let e = mk_expr(ExprX::Binary(vop, lhs, rhs));
        if is_arith_binary || is_spec_arith_binary {
            Ok(mk_ty_clip(&expr_typ(), &e, true))
        } else {
            Ok(e)
        }
    } else if is_chained_value {
        unsupported_err_unless!(len == 1, expr.span, "spec_chained_value", &args);
        unsupported_err_unless!(
            matches!(*vir_args[0].typ, TypX::Int(_)),
            expr.span,
            "chained inequalities for non-integer types",
            &args
        );
        let exprx =
            ExprX::Multi(MultiOp::Chained(Arc::new(vec![])), Arc::new(vec![vir_args[0].clone()]));
        Ok(spanned_typed_new(expr.span, &Arc::new(TypX::Bool), exprx))
    } else if is_chained_ineq {
        unsupported_err_unless!(len == 2, expr.span, "chained inequality", &args);
        unsupported_err_unless!(
            matches!(&vir_args[0].x, ExprX::Multi(MultiOp::Chained(_), _)),
            expr.span,
            "chained inequalities for non-integer types",
            &args
        );
        unsupported_err_unless!(
            matches!(*vir_args[1].typ, TypX::Int(_)),
            expr.span,
            "chained inequalities for non-integer types",
            &args
        );
        let op = if is_chained_le {
            InequalityOp::Le
        } else if is_chained_lt {
            InequalityOp::Lt
        } else if is_chained_ge {
            InequalityOp::Ge
        } else if is_chained_gt {
            InequalityOp::Gt
        } else {
            panic!("is_chained_ineq")
        };
        if let ExprX::Multi(MultiOp::Chained(ops), es) = &vir_args[0].x {
            let mut ops = (**ops).clone();
            let mut es = (**es).clone();
            ops.push(op);
            es.push(vir_args[1].clone());
            let exprx = ExprX::Multi(MultiOp::Chained(Arc::new(ops)), Arc::new(es));
            Ok(spanned_typed_new(expr.span, &Arc::new(TypX::Bool), exprx))
        } else {
            panic!("is_chained_ineq")
        }
    } else if is_chained_cmp {
        unsupported_err_unless!(len == 1, expr.span, "spec_chained_cmp", args);
        Ok(vir_args[0].clone())
    } else if is_ghost_view || is_ghost_borrow || is_tracked_view || is_ghost_new {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Spec,
            from_mode: Mode::Spec,
            to_mode: Mode::Spec,
            kind: ModeCoercion::Other,
        };
        Ok(mk_expr(ExprX::Unary(op, vir_args[0].clone())))
    } else if is_ghost_exec {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Exec,
            from_mode: Mode::Spec,
            to_mode: Mode::Exec,
            kind: ModeCoercion::Other,
        };
        Ok(mk_expr(ExprX::Unary(op, vir_args[0].clone())))
    } else if is_tracked_exec || is_tracked_exec_borrow {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Exec,
            from_mode: Mode::Proof,
            to_mode: Mode::Exec,
            kind: ModeCoercion::Other,
        };
        Ok(mk_expr(ExprX::Unary(op, vir_args[0].clone())))
    } else if is_tracked_get || is_tracked_borrow {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::Other,
        };
        Ok(mk_expr(ExprX::Unary(op, vir_args[0].clone())))
    } else if is_ghost_split_tuple || is_tracked_split_tuple {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Exec,
            from_mode: Mode::Exec,
            to_mode: Mode::Exec,
            kind: ModeCoercion::Other,
        };
        Ok(mk_expr(ExprX::Unary(op, vir_args[0].clone())))
    } else if is_ghost_borrow_mut {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Spec,
            kind: ModeCoercion::BorrowMut,
        };
        let typ = typ_of_node(bctx, &expr.hir_id, true);
        Ok(spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_args[0].clone())))
    } else if is_tracked_borrow_mut {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::BorrowMut,
        };
        let typ = typ_of_node(bctx, &expr.hir_id, true);
        Ok(spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_args[0].clone())))
    } else {
        if !defined_locally {
            unsupported_err!(
                expr.span,
                format!("method call to method not defined in this crate"),
                expr
            );
        }

        // filter out the Fn type parameters
        let mut fn_params: Vec<Ident> = Vec::new();
        for (x, _) in tcx.predicates_of(f).predicates {
            if let PredicateKind::Trait(t) = x.kind().skip_binder() {
                let name = path_as_rust_name(&def_id_to_vir_path(tcx, t.trait_ref.def_id));
                if name == "core::ops::function::Fn" {
                    for s in t.trait_ref.substs {
                        if let GenericArgKind::Type(ty) = s.unpack() {
                            if let TypX::TypParam(x) = &*mid_ty_to_vir(tcx, ty, false) {
                                fn_params.push(x.clone());
                            }
                        }
                    }
                }
            }
        }
        // type arguments
        let mut typ_args: Vec<Typ> = Vec::new();
        for typ_arg in node_substs {
            match typ_arg.unpack() {
                GenericArgKind::Type(ty) => {
                    typ_args.push(mid_ty_to_vir(tcx, ty, false));
                }
                GenericArgKind::Lifetime(_) => {}
                GenericArgKind::Const(cnst) => {
                    typ_args.push(crate::rust_to_vir_base::mid_ty_const_to_vir(tcx, cnst));
                }
            }
        }
        let target = CallTarget::Static(name, Arc::new(typ_args));
        Ok(spanned_typed_new(expr.span, &expr_typ(), ExprX::Call(target, Arc::new(vir_args))))
    }
}

fn datatype_of_path(mut path: vir::ast::Path, pop_count: u32) -> vir::ast::Path {
    // TODO is there a safer way to do this?
    let segments = Arc::get_mut(&mut Arc::get_mut(&mut path).unwrap().segments).unwrap();
    for _ in 0..pop_count {
        segments.pop(); // remove variant or constructor
    }
    path
}

pub(crate) fn datatype_variant_of_res_pop_count<'tcx>(
    tcx: TyCtxt<'tcx>,
    res: &Res,
    pop_count: u32,
) -> (vir::ast::Path, Ident) {
    let variant = tcx.expect_variant_res(*res);
    let vir_path = datatype_of_path(def_id_to_vir_path(tcx, res.def_id()), pop_count);
    let variant_name = str_ident(&variant.ident.as_str());
    (vir_path, variant_name)
}

pub(crate) fn datatype_constructor_variant_of_res<'tcx>(
    tcx: TyCtxt<'tcx>,
    res: &Res,
    pop_variant: bool,
) -> (vir::ast::Path, Ident) {
    let pop_count = if pop_variant { 1 } else { 0 };
    datatype_variant_of_res_pop_count(tcx, res, pop_count)
}

pub(crate) fn datatype_variant_of_res<'tcx>(
    tcx: TyCtxt<'tcx>,
    res: &Res,
    pop_constructor: bool,
) -> (vir::ast::Path, Ident) {
    let pop_count = if pop_constructor { 2 } else { 1 };
    datatype_variant_of_res_pop_count(tcx, res, pop_count)
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
    let expr_typ = typ_of_node(bctx, &expr.hir_id, false);
    let ctor_of = if let Res::Def(DefKind::Ctor(ctor_of, ctor_kind), _def_id) = res {
        unsupported_unless!(
            ctor_of == &rustc_hir::def::CtorOf::Variant
                || ctor_of == &rustc_hir::def::CtorOf::Struct,
            "non_variant_ctor_in_call_expr",
            expr
        );
        unsupported_unless!(
            ctor_kind == &rustc_hir::def::CtorKind::Fn
                || ctor_kind == &rustc_hir::def::CtorKind::Const,
            "non_fn_ctor_in_call_expr",
            expr
        );
        ctor_of
    } else {
        panic!("unexpected constructor in expr_tuple_datatype_ctor_to_vir")
    };
    let (vir_path, variant_name) =
        datatype_variant_of_res(tcx, res, ctor_of == &rustc_hir::def::CtorOf::Variant);
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
    Ok(spanned_typed_new(expr.span, &expr_typ, exprx))
}

pub(crate) fn pattern_to_vir_inner<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pat: &Pat<'tcx>,
) -> Result<vir::ast::Pattern, VirErr> {
    let tcx = bctx.ctxt.tcx;
    unsupported_err_unless!(pat.default_binding_modes, pat.span, "complex pattern");
    let pattern = match &pat.kind {
        PatKind::Wild => PatternX::Wildcard,
        PatKind::Binding(BindingAnnotation::Unannotated, canonical, x, None) => {
            PatternX::Var { name: Arc::new(local_to_var(x, canonical.local_id)), mutable: false }
        }
        PatKind::Binding(BindingAnnotation::Mutable, canonical, x, None) => {
            PatternX::Var { name: Arc::new(local_to_var(x, canonical.local_id)), mutable: true }
        }
        PatKind::Path(QPath::Resolved(
            None,
            rustc_hir::Path {
                res:
                    res @ Res::Def(
                        DefKind::Ctor(
                            rustc_hir::def::CtorOf::Variant,
                            rustc_hir::def::CtorKind::Const,
                        ),
                        _,
                    ),
                ..
            },
        )) => {
            let (vir_path, variant_name) = datatype_variant_of_res(tcx, res, true);
            PatternX::Constructor(vir_path, variant_name, Arc::new(vec![]))
        }
        PatKind::Tuple(pats, None) => {
            let mut patterns: Vec<vir::ast::Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(pattern_to_vir(bctx, pat)?);
            }
            PatternX::Tuple(Arc::new(patterns))
        }
        PatKind::TupleStruct(
            QPath::Resolved(
                None,
                rustc_hir::Path {
                    res:
                        res @ Res::Def(
                            DefKind::Ctor(
                                ctor_of @ (rustc_hir::def::CtorOf::Variant
                                | rustc_hir::def::CtorOf::Struct),
                                rustc_hir::def::CtorKind::Fn,
                            ),
                            _,
                        ),
                    ..
                },
            ),
            pats,
            None,
        ) => {
            let (vir_path, variant_name) =
                datatype_variant_of_res(tcx, res, *ctor_of == rustc_hir::def::CtorOf::Variant);
            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for (i, pat) in pats.iter().enumerate() {
                let pattern = pattern_to_vir(bctx, pat)?;
                let binder = ident_binder(&positional_field_ident(i), &pattern);
                binders.push(binder);
            }
            PatternX::Constructor(vir_path, variant_name, Arc::new(binders))
        }
        PatKind::Struct(
            QPath::Resolved(None, rustc_hir::Path { res: res @ Res::Def(DefKind::Variant, _), .. }),
            pats,
            _,
        ) => {
            let (vir_path, variant_name) = datatype_variant_of_res(tcx, res, false);
            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for fpat in pats.iter() {
                let pattern = pattern_to_vir(bctx, &fpat.pat)?;
                let binder = ident_binder(&str_ident(&fpat.ident.as_str()), &pattern);
                binders.push(binder);
            }
            PatternX::Constructor(vir_path, variant_name, Arc::new(binders))
        }
        PatKind::Struct(
            QPath::Resolved(None, rustc_hir::Path { res: res @ Res::Def(DefKind::Struct, _), .. }),
            pats,
            _,
        ) => {
            let vir_path = def_id_to_vir_path(tcx, res.def_id());
            let variant_name = vir_path.segments.last().expect("empty vir_path").clone();
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
                let pat_typ = typ_of_node(bctx, &pat.hir_id, false);
                pat_or = PatternX::Or(p, spanned_typed_new(pat.span, &pat_typ, pat_or));
            }
            pat_or
        }
        _ => return unsupported_err!(pat.span, "complex pattern", pat),
    };
    let pat_typ = typ_of_node(bctx, &pat.hir_id, false);
    let pattern = spanned_typed_new(pat.span, &pat_typ, pattern);
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
    let vir_stmts: Stmts = Arc::new(
        slice_vec_map_result(block.stmts, |stmt| stmt_to_vir(bctx, stmt))?
            .into_iter()
            .flatten()
            .collect(),
    );
    if block.stmts.len() != 0 {
        modifier = ExprModifier { deref_mut: false, ..modifier };
    }
    let vir_expr = block.expr.map(|expr| expr_to_vir(bctx, &expr, modifier)).transpose()?;

    let x = ExprX::Block(vir_stmts, vir_expr);
    Ok(spanned_typed_new(span.clone(), ty, x))
}

/// Check for the #[verifier(invariant_block)] attribute
pub fn attrs_is_invariant_block(attrs: &[Attribute]) -> Result<bool, VirErr> {
    let attrs_vec = parse_attrs(attrs)?;
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
    err_span_str(
        expr.span,
        "malformed invariant block; use `open_atomic_invariant!` or `open_local_invariant!` macro instead",
    )
}

pub(crate) fn invariant_block_open<'a>(
    tcx: TyCtxt,
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
                                            BindingAnnotation::Unannotated,
                                            guard_hir,
                                            _,
                                            None,
                                        ),
                                    default_binding_modes: true,
                                    ..
                                },
                                inner_pat @ Pat {
                                    kind:
                                        PatKind::Binding(BindingAnnotation::Mutable, inner_hir, _, None),
                                    default_binding_modes: true,
                                    ..
                                },
                            ],
                            None,
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
        }) => {
            let f_name = path_as_rust_name(&def_id_to_vir_path(tcx, *fun_id));
            if f_name != BUILTIN_INV_ATOMIC_BEGIN && f_name != BUILTIN_INV_LOCAL_BEGIN {
                return None;
            }
            let atomicity = if f_name == BUILTIN_INV_ATOMIC_BEGIN {
                InvAtomicity::Atomic
            } else {
                InvAtomicity::NonAtomic
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
        if let Some(block_open) = invariant_block_open(bctx.ctxt.tcx, open_stmt) {
            block_open
        } else {
            return malformed_inv_block_err(expr);
        }
    };

    if let Some((hir_id1, hir_id2, fun_id)) = invariant_block_close(close_stmt) {
        let f_name = path_as_rust_name(&def_id_to_vir_path(bctx.ctxt.tcx, fun_id));
        if f_name != BUILTIN_INV_END {
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
            let ty = typ_of_node(bctx, &e.hir_id, false);
            // NOTE: we use body.span here instead of e.span
            // body.span leads to better error messages
            // (e.g., the "Cannot show invariant holds at end of block" error)
            // (e.span or mid_stmt.span would expose macro internals)
            spanned_typed_new(body.span, &ty, ExprX::Block(vir_stmts, vir_expr))
        }
        _ => {
            return malformed_inv_block_err(expr);
        }
    };

    let vir_arg = expr_to_vir(bctx, &inv_arg, modifier)?;

    let name = Arc::new(pat_to_var(inner_pat));
    let inner_ty = typ_of_node(bctx, &inner_hir, false);
    let vir_binder = Arc::new(BinderX { name, a: inner_ty });

    let e = ExprX::OpenInvariant(vir_arg, vir_binder, vir_body, atomicity);
    Ok(spanned_typed_new(expr.span, &typ_of_node(bctx, &expr.hir_id, false), e))
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) struct ExprModifier {
    /// dereferencing a mutable reference
    deref_mut: bool,
    /// taking a mutable reference
    addr_of: bool,
}

impl ExprModifier {
    pub(crate) const REGULAR: Self = Self { deref_mut: false, addr_of: false };

    #[allow(dead_code)]
    pub(crate) const DEREF_MUT: Self = Self { deref_mut: true, addr_of: false };

    pub(crate) const ADDR_OF: Self = Self { deref_mut: false, addr_of: true };
}

fn is_expr_typ_mut_ref<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<ExprModifier, VirErr> {
    match bctx.types.node_type(expr.hir_id).kind() {
        TyKind::Ref(_, _tys, rustc_ast::Mutability::Not) => Ok(modifier),
        TyKind::Ref(_, _tys, rustc_ast::Mutability::Mut) => {
            Ok(ExprModifier { deref_mut: true, ..modifier })
        }
        _ => Ok(modifier),
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
                return Ok(spanned_typed_new(
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
            typ_of_node_expect_mut_ref(bctx, &expr.hir_id, expr.span)
                .expect("unexpected non-mut-ref type here")
        } else {
            typ_of_node(bctx, &expr.hir_id, false)
        }
    };
    let mk_expr = move |x: ExprX| spanned_typed_new(expr.span, &expr_typ(), x);

    let modifier = ExprModifier { deref_mut: false, ..current_modifier };

    let mk_lit_int = |in_negative_literal: bool, i: u128, typ: Typ| {
        check_lit_int(&bctx.ctxt, expr.span, in_negative_literal, i, &typ)?;
        let c = vir::ast_util::const_int_from_u128(i);
        Ok(mk_expr(ExprX::Const(c)))
    };

    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
    let expr_vattrs = get_verifier_attrs(expr_attrs)?;
    if expr_vattrs.truncate {
        if !match &expr.kind {
            ExprKind::Cast(_, _) => true,
            ExprKind::Call(target, _) => match &target.kind {
                ExprKind::Path(qpath) => {
                    let def = bctx.types.qpath_res(&qpath, expr.hir_id);
                    match def {
                        rustc_hir::def::Res::Def(_, def_id) => {
                            let f_name = tcx.def_path_str(def_id);
                            f_name == "builtin::spec_cast_integer"
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        } {
            return err_span_str(
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
                let block = block_to_vir(bctx, body, &expr.span, &expr_typ(), current_modifier);
                let tracked = match g_attr {
                    GhostBlockAttr::Proof => false,
                    GhostBlockAttr::Tracked => true,
                    GhostBlockAttr::GhostWrapped | GhostBlockAttr::TrackedWrapped => {
                        return block;
                    }
                    GhostBlockAttr::Wrapper => {
                        return err_span_str(expr.span, "unexpected ghost block wrapper");
                    }
                };
                Ok(mk_expr(ExprX::Ghost { alloc_wrapper: None, tracked, expr: block? }))
            } else {
                block_to_vir(bctx, body, &expr.span, &expr_typ(), modifier)
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
                    let def = bctx.types.qpath_res(&qpath, fun.hir_id);
                    match def {
                        // a statically resolved function
                        rustc_hir::def::Res::Def(_, def_id) => Some(fn_call_to_vir(
                            bctx,
                            expr,
                            def_id,
                            bctx.types.node_substs(fun.hir_id),
                            fun.span,
                            args_slice,
                            None,
                            true,
                            modifier,
                        )),
                        rustc_hir::def::Res::Local(_) => {
                            None // dynamically computed function, see below
                        }
                        _ => {
                            unsupported!(format!(
                                "function call {:?} {:?} {:?}",
                                def, expr, expr.span
                            ))
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
                        return Ok(mk_expr(ExprX::Block(Arc::new(vec![]), None)));
                    }
                    let vir_fun = expr_to_vir(bctx, fun, modifier)?;
                    let args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();
                    let vir_args = vec_map_result(&args, |arg| expr_to_vir(bctx, arg, modifier))?;
                    let expr_typ = typ_of_node(bctx, &expr.hir_id, false);

                    let is_spec_fn = match &*vir_fun.typ {
                        TypX::Lambda(..) => true,
                        _ => false,
                    };

                    let (target, vir_args, resolved_call) = if is_spec_fn {
                        (CallTarget::FnSpec(vir_fun), vir_args, ResolvedCall::Spec)
                    } else {
                        // non-static calls are translated into a static call to
                        // `exec_nonstatic_call` which is defined in the pervasive lib.
                        let span = to_air_span(expr.span.clone());
                        let tup = vir::ast_util::mk_tuple(&span, &Arc::new(vir_args));
                        let fun = vir::def::exec_nonstatic_call_fun();
                        let ret_typ = expr_typ.clone();
                        let typ_args =
                            Arc::new(vec![tup.typ.clone(), ret_typ, vir_fun.typ.clone()]);
                        (
                            CallTarget::Static(fun, typ_args),
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

                    Ok(spanned_typed_new(
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
            Ok(mk_expr(ExprX::Tuple(Arc::new(args?))))
        }
        ExprKind::Lit(lit) => match lit.node {
            LitKind::Bool(b) => {
                let c = vir::ast::Constant::Bool(b);
                Ok(mk_expr(ExprX::Const(c)))
            }
            LitKind::Int(i, _) => mk_lit_int(false, i, typ_of_node(bctx, &expr.hir_id, false)),
            LitKind::Char(c) => {
                let c = vir::ast::Constant::Char(c);
                Ok(mk_expr(ExprX::Const(c)))
            }
            _ => {
                panic!("unexpected constant: {:?}", lit)
            }
        },
        ExprKind::Cast(source, _) => {
            let source_vir = &expr_to_vir(bctx, source, modifier)?;
            let source_ty = &source_vir.typ;
            let to_ty = expr_typ();
            match (&**source_ty, &*to_ty) {
                (TypX::Int(_), TypX::Int(_)) => {
                    Ok(mk_ty_clip(&to_ty, &source_vir, expr_vattrs.truncate))
                }
                (TypX::Char, TypX::Int(_)) => {
                    let source_unicode =
                        mk_expr(ExprX::Unary(UnaryOp::CharToInt, source_vir.clone()));
                    Ok(mk_ty_clip(&to_ty, &source_unicode, expr_vattrs.truncate))
                }
                _ => {
                    return err_span_str(
                        expr.span,
                        "Verus currently only supports casts from integer types and `char` to integer types",
                    );
                }
            }
        }
        ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, e) => {
            expr_to_vir_inner(bctx, e, ExprModifier::REGULAR)
        }
        ExprKind::Box(e) => expr_to_vir_inner(bctx, e, ExprModifier::REGULAR),
        ExprKind::Unary(op, arg) => match op {
            UnOp::Not => {
                let not_op = match (tc.node_type(expr.hir_id)).kind() {
                    TyKind::Adt(_, _) | TyKind::Uint(_) | TyKind::Int(_) => UnaryOp::BitNot,
                    TyKind::Bool => UnaryOp::Not,
                    _ => panic!("Internal error on UnOp::Not translation"),
                };
                let varg = expr_to_vir(bctx, arg, modifier)?;
                Ok(mk_expr(ExprX::Unary(not_op, varg)))
            }
            UnOp::Neg => {
                let zero_const = vir::ast_util::const_int_from_u128(0);
                let zero = mk_expr(ExprX::Const(zero_const));
                let varg =
                    if let ExprKind::Lit(Spanned { node: LitKind::Int(i, _), .. }) = &arg.kind {
                        mk_lit_int(true, *i, typ_of_node(bctx, &expr.hir_id, false))?
                    } else {
                        expr_to_vir(bctx, arg, modifier)?
                    };
                Ok(mk_expr(ExprX::Binary(
                    BinaryOp::Arith(ArithOp::Sub, Some(bctx.ctxt.infer_mode())),
                    zero,
                    varg,
                )))
            }
            UnOp::Deref => {
                let inner =
                    expr_to_vir_inner(bctx, arg, is_expr_typ_mut_ref(bctx, arg, modifier)?)?;
                Ok(inner)
            }
        },
        ExprKind::Binary(op, lhs, rhs) => {
            let vlhs = expr_to_vir(bctx, lhs, modifier)?;
            let vrhs = expr_to_vir(bctx, rhs, modifier)?;
            match op.node {
                BinOpKind::Eq | BinOpKind::Ne => unsupported_err_unless!(
                    is_smt_equality(bctx, expr.span, &lhs.hir_id, &rhs.hir_id),
                    expr.span,
                    "==/!= for non smt equality types"
                ),
                BinOpKind::Add
                | BinOpKind::Sub
                | BinOpKind::Mul
                | BinOpKind::Le
                | BinOpKind::Ge
                | BinOpKind::Lt
                | BinOpKind::Gt => unsupported_unless!(
                    is_smt_arith(bctx, &lhs.hir_id, &rhs.hir_id),
                    "cmp or arithmetic for non smt arithmetic types",
                    expr
                ),
                _ => (),
            }
            let vop = match op.node {
                BinOpKind::And => BinaryOp::And,
                BinOpKind::Or => BinaryOp::Or,
                BinOpKind::Eq => BinaryOp::Eq(Mode::Exec),
                BinOpKind::Ne => BinaryOp::Ne,
                BinOpKind::Le => BinaryOp::Inequality(InequalityOp::Le),
                BinOpKind::Ge => BinaryOp::Inequality(InequalityOp::Ge),
                BinOpKind::Lt => BinaryOp::Inequality(InequalityOp::Lt),
                BinOpKind::Gt => BinaryOp::Inequality(InequalityOp::Gt),
                BinOpKind::Add => BinaryOp::Arith(ArithOp::Add, Some(bctx.ctxt.infer_mode())),
                BinOpKind::Sub => BinaryOp::Arith(ArithOp::Sub, Some(bctx.ctxt.infer_mode())),
                BinOpKind::Mul => BinaryOp::Arith(ArithOp::Mul, Some(bctx.ctxt.infer_mode())),
                BinOpKind::Div => {
                    BinaryOp::Arith(ArithOp::EuclideanDiv, Some(bctx.ctxt.infer_mode()))
                }
                BinOpKind::Rem => {
                    BinaryOp::Arith(ArithOp::EuclideanMod, Some(bctx.ctxt.infer_mode()))
                }
                BinOpKind::BitXor => {
                    match ((tc.node_type(lhs.hir_id)).kind(), (tc.node_type(rhs.hir_id)).kind()) {
                        (TyKind::Bool, TyKind::Bool) => BinaryOp::Xor,
                        (TyKind::Int(_), TyKind::Int(_)) => BinaryOp::Bitwise(BitwiseOp::BitXor),
                        (TyKind::Uint(_), TyKind::Uint(_)) => BinaryOp::Bitwise(BitwiseOp::BitXor),
                        _ => panic!("bitwise XOR for this type not supported"),
                    }
                }
                BinOpKind::BitAnd => {
                    match ((tc.node_type(lhs.hir_id)).kind(), (tc.node_type(rhs.hir_id)).kind()) {
                        (TyKind::Bool, TyKind::Bool) => {
                            panic!(
                                "bitwise AND for bools (i.e., the not-short-circuited version) not supported"
                            );
                        }
                        (TyKind::Int(_), TyKind::Int(_)) => BinaryOp::Bitwise(BitwiseOp::BitAnd),
                        (TyKind::Uint(_), TyKind::Uint(_)) => BinaryOp::Bitwise(BitwiseOp::BitAnd),
                        t => panic!("bitwise AND for this type not supported {:#?}", t),
                    }
                }
                BinOpKind::BitOr => {
                    match ((tc.node_type(lhs.hir_id)).kind(), (tc.node_type(rhs.hir_id)).kind()) {
                        (TyKind::Bool, TyKind::Bool) => {
                            panic!(
                                "bitwise OR for bools (i.e., the not-short-circuited version) not supported"
                            );
                        }
                        (TyKind::Int(_), TyKind::Int(_)) => BinaryOp::Bitwise(BitwiseOp::BitOr),
                        (TyKind::Uint(_), TyKind::Uint(_)) => BinaryOp::Bitwise(BitwiseOp::BitOr),
                        _ => panic!("bitwise OR for this type not supported"),
                    }
                }
                BinOpKind::Shr => BinaryOp::Bitwise(BitwiseOp::Shr),
                BinOpKind::Shl => BinaryOp::Bitwise(BitwiseOp::Shl),
            };
            let e = mk_expr(ExprX::Binary(vop, vlhs, vrhs));
            match op.node {
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul => {
                    Ok(mk_ty_clip(&expr_typ(), &e, true))
                }
                BinOpKind::Div | BinOpKind::Rem => {
                    match mk_range(tc.node_type(expr.hir_id)) {
                        IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::USize => {
                            // Euclidean division
                            Ok(mk_ty_clip(&expr_typ(), &e, true))
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
        ExprKind::AssignOp(Spanned { node: BinOpKind::Shr, .. }, lhs, rhs) => {
            let vlhs = expr_to_vir(bctx, lhs, modifier)?;
            let vrhs = expr_to_vir(bctx, rhs, modifier)?;
            if matches!(*vlhs.typ, TypX::Bool) {
                let e = mk_expr(ExprX::Binary(BinaryOp::Implies, vlhs, vrhs));
                Ok(e)
            } else {
                unsupported_err!(expr.span, "assignment operators")
            }
        }
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(id) => match tcx.hir().get(id) {
                Node::Binding(pat) => Ok(mk_expr(if modifier.addr_of {
                    ExprX::VarLoc(Arc::new(pat_to_var(pat)))
                } else {
                    ExprX::Var(Arc::new(pat_to_var(pat)))
                })),
                node => unsupported_err!(expr.span, format!("Path {:?}", node)),
            },
            Res::Def(def_kind, id) => {
                match def_kind {
                    DefKind::Const => {
                        let path = def_id_to_vir_path(tcx, id);
                        let fun = FunX { path, trait_path: None };
                        Ok(mk_expr(ExprX::ConstVar(Arc::new(fun))))
                    }
                    DefKind::Fn => {
                        let name = hack_get_def_name(tcx, id); // TODO: proper handling of paths
                        Ok(mk_expr(ExprX::Var(Arc::new(name))))
                    }
                    DefKind::Ctor(_, _ctor_kind) => expr_tuple_datatype_ctor_to_vir(
                        bctx,
                        expr,
                        &path.res,
                        &[],
                        expr.span,
                        modifier,
                    ),
                    DefKind::ConstParam => {
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
                        match *expr_typ() {
                            TypX::Int(_) => {}
                            _ => {
                                unsupported_err!(expr.span, format!("non-int ConstParam {:?}", id))
                            }
                        }
                        if let Some(name) = gparam {
                            let typ = Arc::new(TypX::TypParam(Arc::new(name.ident().to_string())));
                            let opr = vir::ast::NullaryOpr::ConstGeneric(typ);
                            Ok(mk_expr(ExprX::NullaryOpr(opr)))
                        } else {
                            unsupported_err!(expr.span, format!("ConstParam {:?}", id))
                        }
                    }
                    _ => {
                        unsupported_err!(expr.span, format!("Path {:?} kind {:?}", id, def_kind))
                    }
                }
            }
            res => unsupported_err!(expr.span, format!("Path {:?}", res)),
        },
        ExprKind::Path(qpath @ QPath::TypeRelative(_ty, _path_seg)) => {
            let def = bctx.types.qpath_res(&qpath, expr.hir_id);
            match def {
                rustc_hir::def::Res::Def(_, def_id) => {
                    let f_name = bctx.ctxt.tcx.def_path_str(def_id);
                    if let Some(vir_expr) =
                        int_intrinsic_constant_to_vir(expr.span, &expr_typ(), &f_name)
                    {
                        let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                        erasure_info.resolved_calls.push((
                            expr.hir_id,
                            expr.span.data(),
                            ResolvedCall::CompilableOperator(CompilableOperator::IntIntrinsic),
                        ));
                        return Ok(vir_expr);
                    }
                }
                _ => {}
            }
            unsupported_err!(expr.span, format!("expression"), expr)
        }
        ExprKind::Assign(lhs, rhs, _) => {
            fn init_not_mut<'tcx>(bctx: &BodyCtxt<'tcx>, lhs: &Expr) -> Result<bool, VirErr> {
                Ok(match lhs.kind {
                    ExprKind::Path(QPath::Resolved(
                        None,
                        rustc_hir::Path { res: Res::Local(id), .. },
                    )) => {
                        let not_mut = if let Node::Binding(pat) = bctx.ctxt.tcx.hir().get(*id) {
                            let (mutable, _) = pat_to_mut_var(pat);
                            let ty = bctx.types.node_type(*id);
                            !(mutable || ty.ref_mutability() == Some(Mutability::Mut))
                        } else {
                            panic!("assignment to non-local");
                        };
                        if not_mut {
                            match bctx.ctxt.tcx.hir().get(bctx.ctxt.tcx.hir().get_parent_node(*id))
                            {
                                Node::Param(_) => {
                                    err_span_str(lhs.span, "cannot assign to non-mut parameter")?
                                }
                                Node::Local(_) => (),
                                other => unsupported_err!(lhs.span, "assignee node", other),
                            }
                        }
                        not_mut
                    }
                    ExprKind::Field(lhs, _) => {
                        let deref_ghost = mid_ty_to_vir_ghost(
                            bctx.ctxt.tcx,
                            bctx.types.node_type(lhs.hir_id),
                            true,
                        )
                        .1;
                        unsupported_err_unless!(
                            !deref_ghost,
                            lhs.span,
                            "assignment through Ghost/Tracked"
                        );
                        init_not_mut(bctx, lhs)?
                    }
                    ExprKind::Unary(UnOp::Deref, _) => false,
                    _ => {
                        unsupported_err!(lhs.span, format!("assign lhs {:?}", lhs))
                    }
                })
            }
            let init_not_mut = init_not_mut(bctx, lhs)?;
            Ok(mk_expr(ExprX::Assign {
                init_not_mut,
                lhs: expr_to_vir(bctx, lhs, ExprModifier::ADDR_OF)?,
                rhs: expr_to_vir(bctx, rhs, modifier)?,
            }))
        }
        ExprKind::Field(lhs, name) => {
            let lhs_modifier = is_expr_typ_mut_ref(bctx, lhs, modifier)?;
            let vir_lhs = expr_to_vir(bctx, lhs, lhs_modifier)?;
            let lhs_ty = tc.node_type(lhs.hir_id);
            let lhs_ty = mid_ty_simplify(tcx, lhs_ty, true);
            let (datatype, variant_name, field_name) = if let Some(adt_def) = lhs_ty.ty_adt_def() {
                unsupported_err_unless!(
                    adt_def.variants.len() == 1,
                    expr.span,
                    "field_of_adt_with_multiple_variants",
                    expr
                );
                let datatype_path = def_id_to_vir_path(tcx, adt_def.did);
                let hir_def = bctx.ctxt.tcx.adt_def(adt_def.did);
                let variant = hir_def.variants.iter().next().unwrap();
                let variant_name = str_ident(&variant.ident.as_str());
                let field_name = match variant.ctor_kind {
                    rustc_hir::def::CtorKind::Fn => {
                        let field_idx = variant
                            .fields
                            .iter()
                            .position(|f| f.ident.as_str() == name.as_str())
                            .expect("positional field not found");
                        positional_field_ident(field_idx)
                    }
                    rustc_hir::def::CtorKind::Fictive => str_ident(&name.as_str()),
                    rustc_hir::def::CtorKind::Const => panic!("unexpected tuple constructor"),
                };
                (datatype_path, variant_name, field_name)
            } else {
                let lhs_typ = typ_of_node(bctx, &lhs.hir_id, false);
                if let TypX::Tuple(ts) = &*lhs_typ {
                    let field: usize =
                        str::parse(&name.as_str()).expect("integer index into tuple");
                    let field_opr = UnaryOpr::TupleField { tuple_arity: ts.len(), field };
                    let vir = mk_expr(ExprX::UnaryOpr(field_opr, vir_lhs));
                    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                    erasure_info.resolved_exprs.push((expr.span.data(), vir.clone()));
                    return Ok(vir);
                }
                unsupported_err!(expr.span, "field_of_non_adt", expr)
            };
            let field_type = expr_typ().clone();
            let vir = spanned_typed_new(
                expr.span,
                &field_type,
                ExprX::UnaryOpr(
                    UnaryOpr::Field(FieldOpr {
                        datatype,
                        variant: variant_name,
                        field: field_name,
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
                ExprKind::Let(pat, expr, _let_span) => {
                    // if let
                    let vir_expr = expr_to_vir(bctx, expr, modifier)?;
                    let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
                    /* lhs */
                    {
                        let pattern = pattern_to_vir(bctx, pat)?;
                        let guard = mk_expr(ExprX::Const(Constant::Bool(true)));
                        let body = expr_to_vir(bctx, &lhs, modifier)?;
                        let vir_arm = ArmX { pattern, guard, body };
                        vir_arms.push(spanned_new(lhs.span, vir_arm));
                    }
                    /* rhs */
                    {
                        let pat_typ = typ_of_node(bctx, &pat.hir_id, false);
                        let pattern = spanned_typed_new(cond.span, &pat_typ, PatternX::Wildcard);
                        {
                            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                            erasure_info.hir_vir_ids.push((cond.hir_id, pattern.span.id));
                        }
                        let guard = mk_expr(ExprX::Const(Constant::Bool(true)));
                        let body = if let Some(rhs) = rhs {
                            expr_to_vir(bctx, &rhs, modifier)?
                        } else {
                            mk_expr(ExprX::Block(Arc::new(Vec::new()), None))
                        };
                        let vir_arm = ArmX { pattern, guard, body };
                        vir_arms.push(spanned_new(lhs.span, vir_arm));
                    }
                    Ok(mk_expr(ExprX::Match(vir_expr, Arc::new(vir_arms))))
                }
                _ => {
                    let vir_cond = expr_to_vir(bctx, cond, modifier)?;
                    let vir_lhs = expr_to_vir(bctx, lhs, modifier)?;
                    let vir_rhs = rhs.map(|e| expr_to_vir(bctx, e, modifier)).transpose()?;
                    Ok(mk_expr(ExprX::If(vir_cond, vir_lhs, vir_rhs)))
                }
            }
        }
        ExprKind::Match(expr, arms, _match_source) => {
            let vir_expr = expr_to_vir(bctx, expr, modifier)?;
            let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
            for arm in arms.iter() {
                let pattern = pattern_to_vir(bctx, &arm.pat)?;
                let guard = match &arm.guard {
                    None => mk_expr(ExprX::Const(Constant::Bool(true))),
                    Some(Guard::If(guard)) => expr_to_vir(bctx, guard, modifier)?,
                    Some(Guard::IfLet(_, _)) => unsupported_err!(expr.span, "Guard IfLet"),
                };
                let body = expr_to_vir(bctx, &arm.body, modifier)?;
                let vir_arm = ArmX { pattern, guard, body };
                vir_arms.push(spanned_new(arm.span, vir_arm));
            }
            Ok(mk_expr(ExprX::Match(vir_expr, Arc::new(vir_arms))))
        }
        ExprKind::Loop(block, label, LoopSource::Loop, _span) => {
            let typ = typ_of_node(bctx, &block.hir_id, false);
            let mut body = block_to_vir(bctx, block, &expr.span, &typ, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut body)?;
            let label = label.map(|l| l.ident.to_string());
            Ok(mk_expr(ExprX::Loop { label, cond: None, body, invs: header.loop_invariants() }))
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
                unsupported!("loop else", expr);
            }
            assert!(modifier == ExprModifier::REGULAR);
            let cond = Some(expr_to_vir(bctx, cond, ExprModifier::REGULAR)?);
            let mut body = expr_to_vir(bctx, body, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut body)?;
            if header.decrease.len() > 0 {
                return err_span_str(expr.span, "termination checking of loops is not supported");
            }
            let label = label.map(|l| l.ident.to_string());
            Ok(mk_expr(ExprX::Loop { label, cond, body, invs: header.loop_invariants() }))
        }
        ExprKind::Ret(expr) => {
            let expr = match expr {
                None => None,
                Some(expr) => Some(expr_to_vir(bctx, expr, modifier)?),
            };
            Ok(mk_expr(ExprX::Return(expr)))
        }
        ExprKind::Break(dest, None) => {
            let label = dest.label.map(|l| l.ident.to_string());
            Ok(mk_expr(ExprX::BreakOrContinue { label, is_break: true }))
        }
        ExprKind::Continue(dest) => {
            let label = dest.label.map(|l| l.ident.to_string());
            Ok(mk_expr(ExprX::BreakOrContinue { label, is_break: false }))
        }
        ExprKind::Struct(qpath, fields, spread) => {
            let update = match spread {
                None => None,
                Some(update) => Some(expr_to_vir(bctx, update, modifier)?),
            };
            let (path, variant_name) = match qpath {
                QPath::Resolved(slf, path) => {
                    unsupported_unless!(
                        matches!(path.res, Res::Def(DefKind::Struct | DefKind::Variant, _)),
                        "non_struct_ctor",
                        path.res
                    );
                    unsupported_unless!(slf.is_none(), "self_in_struct_qpath");
                    let pop_variant = matches!(path.res, Res::Def(DefKind::Variant, _));
                    datatype_constructor_variant_of_res(tcx, &path.res, pop_variant)
                }
                _ => panic!("unexpected qpath {:?}", qpath),
            };
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
            Ok(mk_expr(ExprX::Ctor(path, variant_name, vir_fields, update)))
        }
        ExprKind::MethodCall(_name_and_generics, _call_span_0, all_args, fn_span) => {
            let fn_def_id = bctx
                .types
                .type_dependent_def_id(expr.hir_id)
                .expect("def id of the method definition");

            let defined_locally = match tcx.hir().get_if_local(fn_def_id) {
                Some(rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
                    kind: rustc_hir::ImplItemKind::Fn(..),
                    ..
                })) => true,
                Some(rustc_hir::Node::TraitItem(rustc_hir::TraitItem {
                    kind: rustc_hir::TraitItemKind::Fn(..),
                    ..
                })) => true,
                None => {
                    // Special case `clone` for standard Rc and Arc types
                    // (Could also handle it for other types where cloning is the identity
                    // operation in the SMT encoding.)
                    let f_name = tcx.def_path_str(fn_def_id);
                    if f_name == "std::clone::Clone::clone" {
                        assert!(all_args.len() == 1);
                        let arg_typ = bctx.types.node_type(all_args[0].hir_id);
                        if is_type_std_rc_or_arc(bctx.ctxt.tcx, &arg_typ) {
                            let arg = expr_to_vir(bctx, &all_args[0], ExprModifier::REGULAR)?;
                            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                            erasure_info.resolved_calls.push((
                                expr.hir_id,
                                fn_span.data(),
                                ResolvedCall::CompilableOperator(CompilableOperator::SmartPtrClone),
                            ));
                            return Ok(arg);
                        }
                    }

                    let is_closure_req = f_name == "builtin::FnWithSpecification::requires";
                    let is_closure_ens = f_name == "builtin::FnWithSpecification::ensures";

                    if is_closure_req || is_closure_ens {
                        {
                            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                            erasure_info.resolved_calls.push((
                                expr.hir_id,
                                fn_span.data(),
                                ResolvedCall::Spec,
                            ));
                        }
                        let bsf = if is_closure_req {
                            assert!(all_args.len() == 2);
                            vir::ast::BuiltinSpecFun::ClosureReq
                        } else {
                            assert!(all_args.len() == 3);
                            vir::ast::BuiltinSpecFun::ClosureEns
                        };
                        let vir_args = all_args
                            .iter()
                            .map(|arg| expr_to_vir(bctx, &arg, ExprModifier::REGULAR))
                            .collect::<Result<Vec<_>, _>>()?;

                        let mut typ_args: Vec<Typ> = Vec::new();
                        for typ_arg in bctx.types.node_substs(expr.hir_id) {
                            match typ_arg.unpack() {
                                GenericArgKind::Type(ty) => {
                                    typ_args.push(mid_ty_to_vir(tcx, ty, false));
                                }
                                GenericArgKind::Lifetime(_) => {}
                                _ => unsupported_err!(
                                    expr.span,
                                    format!("const type arguments"),
                                    expr
                                ),
                            }
                        }

                        let target = CallTarget::BuiltinSpecFun(bsf, Arc::new(typ_args));

                        return Ok(mk_expr(ExprX::Call(target, Arc::new(vir_args))));
                    }

                    false
                }
                _ => panic!("unexpected hir for method impl item"),
            };
            let autoview_typ = bctx.ctxt.autoviewed_call_typs.get(&expr.hir_id);
            fn_call_to_vir(
                bctx,
                expr,
                fn_def_id,
                bctx.types.node_substs(expr.hir_id),
                *fn_span,
                all_args,
                autoview_typ,
                defined_locally,
                modifier,
            )
        }
        ExprKind::Closure(..) => closure_to_vir(bctx, expr, expr_typ(), false, modifier),
        ExprKind::Index(tgt_expr, idx_expr) => {
            let tgt_vir = expr_to_vir(bctx, tgt_expr, modifier)?;
            if let TypX::Datatype(path, _dt_typs) = &*tgt_vir.typ {
                let tgt_index_path = {
                    let mut tp = path.clone();
                    Arc::make_mut(&mut Arc::make_mut(&mut tp).segments).push(str_ident("index"));
                    tp
                };
                let trait_def_id = bctx
                    .ctxt
                    .tcx
                    .lang_items()
                    .index_trait()
                    .expect("Index trait lang item should be defined");
                let trait_path = def_id_to_vir_path(bctx.ctxt.tcx, trait_def_id);
                let idx_vir = expr_to_vir(bctx, idx_expr, modifier)?;
                let target = CallTarget::Static(
                    Arc::new(FunX { path: tgt_index_path, trait_path: Some(trait_path) }),
                    Arc::new(vec![]),
                );
                Ok(mk_expr(ExprX::Call(target, Arc::new(vec![tgt_vir, idx_vir]))))
            } else {
                unsupported_err!(expr.span, format!("Index on non-datatype"), expr)
            }
        }
        _ => {
            unsupported_err!(expr.span, format!("expression"), expr)
        }
    }
}

pub(crate) fn let_stmt_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pattern: &rustc_hir::Pat<'tcx>,
    initializer: &Option<&Expr<'tcx>>,
    attrs: &[Attribute],
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    let vir_pattern = pattern_to_vir(bctx, pattern)?;
    let mode = get_var_mode(bctx.mode, attrs);
    let init = initializer.map(|e| expr_to_vir(bctx, e, ExprModifier::REGULAR)).transpose()?;
    Ok(vec![spanned_new(pattern.span, StmtX::Decl { pattern: vir_pattern, mode, init })])
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
            Ok(vec![spanned_new(expr.span, StmtX::Expr(vir_expr))])
        }
        StmtKind::Local(Local { pat, init, .. }) => {
            let_stmt_to_vir(bctx, pat, init, bctx.ctxt.tcx.hir().attrs(stmt.hir_id))
        }
        _ => {
            unsupported_err!(stmt.span, "statement", stmt)
        }
    }
}

fn closure_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    closure_expr: &Expr<'tcx>,
    closure_vir_typ: Typ,
    is_spec_fn: bool,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    if let ExprKind::Closure(_, fn_decl, body_id, _, _) = &closure_expr.kind {
        unsupported_unless!(!fn_decl.c_variadic, "c_variadic");
        unsupported_unless!(
            matches!(fn_decl.implicit_self, rustc_hir::ImplicitSelfKind::None),
            "implicit_self"
        );
        let body = bctx.ctxt.tcx.hir().body(*body_id);

        let typs = closure_param_typs(bctx, closure_expr);
        assert!(typs.len() == body.params.len());
        let params: Vec<Binder<Typ>> = body
            .params
            .iter()
            .zip(typs.clone())
            .map(|(x, t)| {
                let attrs = bctx.ctxt.tcx.hir().attrs(x.hir_id);
                let mode = crate::attributes::get_mode(Mode::Exec, attrs);
                if mode != Mode::Exec {
                    return err_span_str(x.span, "closures only accept exec-mode parameters");
                }

                let (is_mut, name) = pat_to_mut_var(x.pat);
                if is_mut {
                    return err_span_str(
                        x.span,
                        "Verus does not support 'mut' params for closures",
                    );
                }
                Ok(Arc::new(BinderX { name: Arc::new(name), a: t }))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut body = expr_to_vir(bctx, &body.value, modifier)?;

        let header = vir::headers::read_header(&mut body)?;
        let vir::headers::Header { require, ensure, ensure_id_typ, .. } = header;

        let exprx = if is_spec_fn {
            if require.len() > 0 || ensure.len() > 0 {
                return err_span_str(
                    closure_expr.span,
                    "SpecFn should not have `requires` clause or `ensures` clause",
                );
            }
            ExprX::Closure(Arc::new(params), body)
        } else {
            let ret_typ = closure_ret_typ(bctx, closure_expr);

            let id = match ensure_id_typ {
                Some((id, ensures_typ)) => {
                    if !types_equal(&ensures_typ, &ret_typ) {
                        return err_span_str(
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
        Ok(spanned_typed_new(closure_expr.span, &closure_vir_typ, exprx))
    } else {
        panic!("closure_to_vir expects ExprKind::Closure");
    }
}
