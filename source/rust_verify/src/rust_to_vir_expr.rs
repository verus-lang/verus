use crate::erase::ResolvedCall;
use crate::rust_to_vir_base::{
    def_id_to_vir_path, get_range, get_trigger, get_var_mode, hack_check_def_name,
    hack_get_def_name, ident_to_var, is_smt_arith, is_smt_equality, mid_ty_to_vir,
    mid_ty_to_vir_opt, mk_range, ty_to_vir, typ_of_node, BodyCtxt,
};
use crate::util::{
    err_span_str, slice_vec_map_result, spanned_new, spanned_typed_new, unsupported_err_span,
    vec_map_result,
};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use air::ast::{Binder, BinderX, Quant};
use rustc_ast::{Attribute, BorrowKind, LitKind, Mutability};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    Arm, BinOpKind, BindingAnnotation, Block, Destination, Expr, ExprKind, Local, LoopSource,
    MatchSource, Node, Pat, PatKind, QPath, Stmt, StmtKind, UnOp,
};
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    BinaryOp, Constant, ExprX, HeaderExpr, HeaderExprX, IntRange, ParamX, SpannedTyped, StmtX,
    Stmts, Typ, TypX, UnaryOp, UnaryOpr, VirErr,
};
use vir::ast_util::ident_binder;
use vir::def::{variant_field_ident, variant_ident, variant_positional_field_ident};

pub(crate) fn pat_to_var<'tcx>(pat: &Pat) -> String {
    let Pat { hir_id: _, kind, span: _, default_binding_modes } = pat;
    unsupported_unless!(default_binding_modes, "default_binding_modes");
    match kind {
        PatKind::Binding(annotation, _id, ident, pat) => {
            match annotation {
                BindingAnnotation::Unannotated => {}
                BindingAnnotation::Mutable => {}
                _ => {
                    unsupported!(format!("binding annotation {:?}", annotation))
                }
            }
            match pat {
                None => {}
                _ => {
                    unsupported!(format!("pattern {:?}", kind))
                }
            }
            ident_to_var(ident)
        }
        _ => {
            unsupported!(format!("pattern {:?}", kind))
        }
    }
}

fn expr_to_function<'hir>(expr: &Expr<'hir>) -> DefId {
    let v = match &expr.kind {
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            rustc_hir::def::Res::Def(_, def_id) => Some(def_id),
            _ => None,
        },
        _ => None,
    };
    match v {
        Some(def_id) => def_id,
        None => unsupported!(format!("complex function call {:?} {:?}", expr, expr.span)),
    }
}

fn extract_array<'tcx>(expr: &'tcx Expr<'tcx>) -> Vec<&'tcx Expr<'tcx>> {
    match &expr.kind {
        ExprKind::Array(fields) => fields.iter().collect(),
        _ => vec![expr],
    }
}

fn get_ensures_arg<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    if matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
        expr_to_vir(bctx, expr)
    } else {
        err_span_str(expr.span, "ensures needs a bool expression")
    }
}

fn extract_ensures<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Result<HeaderExpr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, fn_decl, body_id, _, _) => {
            let typs: Vec<Typ> = fn_decl.inputs.iter().map(|t| ty_to_vir(tcx, t)).collect();
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
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, fn_decl, body_id, _, _) => {
            let body = tcx.hir().body(*body_id);
            let binders: Vec<Binder<Typ>> = body
                .params
                .iter()
                .zip(fn_decl.inputs)
                .map(|(x, t)| {
                    Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)), a: ty_to_vir(tcx, t) })
                })
                .collect();
            let expr = &body.value;
            if !matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
                return err_span_str(expr.span, "forall/ensures needs a bool expression");
            }
            let vir_expr = expr_to_vir(bctx, expr)?;
            let typ = Arc::new(TypX::Bool);
            Ok(spanned_typed_new(span, &typ, ExprX::Quant(quant, Arc::new(binders), vir_expr)))
        }
        _ => err_span_str(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn mk_clip<'tcx>(range: &IntRange, expr: &vir::ast::Expr) -> vir::ast::Expr {
    match range {
        IntRange::Int => expr.clone(),
        range => SpannedTyped::new(
            &expr.span,
            &Arc::new(TypX::Int(*range)),
            ExprX::Unary(UnaryOp::Clip(*range), expr.clone()),
        ),
    }
}

fn mk_ty_clip<'tcx>(typ: &Typ, expr: &vir::ast::Expr) -> vir::ast::Expr {
    mk_clip(&get_range(typ), expr)
}

pub(crate) fn expr_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let mut vir_expr = expr_to_vir_inner(bctx, expr)?;
    for group in get_trigger(bctx.ctxt.tcx.hir().attrs(expr.hir_id))? {
        vir_expr = vir_expr.new_x(ExprX::Unary(UnaryOp::Trigger(group), vir_expr.clone()));
    }
    Ok(vir_expr)
}

fn record_fun(
    ctxt: &crate::context::Context,
    span: Span,
    id: DefId,
    is_spec: bool,
    is_compilable_operator: bool,
) {
    let mut erasure_info = ctxt.erasure_info.borrow_mut();
    let resolved_call = if is_spec {
        ResolvedCall::Spec
    } else if is_compilable_operator {
        ResolvedCall::CompilableOperator
    } else {
        ResolvedCall::Call(def_id_to_vir_path(ctxt.tcx, id))
    };
    erasure_info.resolved_calls.push((span.data(), resolved_call));
}

fn get_fn_path<'tcx>(tcx: TyCtxt<'tcx>, expr: &Expr<'tcx>) -> Result<vir::ast::Path, VirErr> {
    match &expr.kind {
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Def(DefKind::Fn, id) => Ok(def_id_to_vir_path(tcx, id)),
            res => unsupported_err!(expr.span, format!("Path {:?}", res)),
        },
        _ => unsupported_err!(expr.span, format!("{:?}", expr)),
    }
}

fn fn_call_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    fun: &'tcx Expr<'tcx>,
    args_slice: &'tcx [Expr<'tcx>],
) -> Result<vir::ast::Expr, VirErr> {
    let mut args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();
    let f = expr_to_function(fun);

    let tcx = bctx.ctxt.tcx;
    let expr_typ = typ_of_node(bctx, &expr.hir_id);
    let mk_expr = |x: ExprX| spanned_typed_new(expr.span, &expr_typ, x);
    let mk_expr_span = |span: Span, x: ExprX| spanned_typed_new(span, &expr_typ, x);

    let is_admit = hack_check_def_name(tcx, f, "builtin", "admit");
    let is_requires = hack_check_def_name(tcx, f, "builtin", "requires");
    let is_ensures = hack_check_def_name(tcx, f, "builtin", "ensures");
    let is_invariant = hack_check_def_name(tcx, f, "builtin", "invariant");
    let is_decreases = hack_check_def_name(tcx, f, "builtin", "decreases");
    let is_forall = hack_check_def_name(tcx, f, "builtin", "forall");
    let is_exists = hack_check_def_name(tcx, f, "builtin", "exists");
    let is_hide = hack_check_def_name(tcx, f, "builtin", "hide");
    let is_reveal = hack_check_def_name(tcx, f, "builtin", "reveal");
    let is_reveal_fuel = hack_check_def_name(tcx, f, "builtin", "reveal_with_fuel");
    let is_implies = hack_check_def_name(tcx, f, "builtin", "imply");
    let is_eq = hack_check_def_name(tcx, f, "core", "cmp::PartialEq::eq");
    let is_ne = hack_check_def_name(tcx, f, "core", "cmp::PartialEq::ne");
    let is_le = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::le");
    let is_ge = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::ge");
    let is_lt = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::lt");
    let is_gt = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::gt");
    let is_add = hack_check_def_name(tcx, f, "core", "ops::arith::Add::add");
    let is_sub = hack_check_def_name(tcx, f, "core", "ops::arith::Sub::sub");
    let is_mul = hack_check_def_name(tcx, f, "core", "ops::arith::Mul::mul");
    let is_spec = is_admit || is_requires || is_ensures || is_invariant || is_decreases;
    let is_quant = is_forall || is_exists;
    let is_directive = is_hide || is_reveal || is_reveal_fuel;
    let is_cmp = is_eq || is_ne || is_le || is_ge || is_lt || is_gt;
    let is_arith_binary = is_add || is_sub || is_mul;
    record_fun(&bctx.ctxt, fun.span, f, is_spec || is_quant || is_directive, is_implies);

    let len = args.len();
    if is_requires {
        unsupported_err_unless!(len == 1, expr.span, "expected requires", &args);
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "requires needs a bool expression");
            }
        }
    }
    if is_ensures {
        unsupported_err_unless!(len == 1, expr.span, "expected ensures", &args);
        let header = extract_ensures(bctx, args[0])?;
        let expr = mk_expr_span(args[0].span, ExprX::Header(header));
        // extract_ensures does most of the necessary work, so we can return at this point
        return Ok(expr);
    }
    if is_invariant {
        unsupported_err_unless!(len == 1, expr.span, "expected invariant", &args);
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "invariant needs a bool expression");
            }
        }
    }
    if is_forall || is_exists {
        unsupported_err_unless!(len == 1, expr.span, "expected forall/exists", &args);
        let quant = if is_forall { Quant::Forall } else { Quant::Exists };
        return extract_quant(bctx, expr.span, quant, args[0]);
    }

    if is_hide || is_reveal {
        unsupported_err_unless!(len == 1, expr.span, "expected hide/reveal", &args);
        let x = get_fn_path(tcx, &args[0])?;
        if is_hide {
            let header = Arc::new(HeaderExprX::Hide(x));
            return Ok(mk_expr(ExprX::Header(header)));
        } else {
            return Ok(mk_expr(ExprX::Fuel(x, 1)));
        }
    }
    if is_reveal_fuel {
        unsupported_err_unless!(len == 2, expr.span, "expected reveal_fuel", &args);
        let x = get_fn_path(tcx, &args[0])?;
        match &expr_to_vir(bctx, &args[1])?.x {
            ExprX::Const(Constant::Nat(s)) => {
                let n = s.parse::<u32>().expect(&format!("internal error: parse {}", s));
                return Ok(mk_expr(ExprX::Fuel(x, n)));
            }
            _ => panic!("internal error: is_reveal_fuel"),
        }
    }

    let mut vir_args = vec_map_result(&args, |arg| expr_to_vir(bctx, arg))?;

    let is_smt_binary = if is_eq || is_ne {
        is_smt_equality(bctx, expr.span, &args[0].hir_id, &args[1].hir_id)
    } else if is_cmp || is_arith_binary || is_implies {
        is_smt_arith(bctx, &args[0].hir_id, &args[1].hir_id)
    } else {
        false
    };

    if is_requires {
        let header = Arc::new(HeaderExprX::Requires(Arc::new(vir_args)));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_invariant {
        let header = Arc::new(HeaderExprX::Invariant(Arc::new(vir_args)));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_decreases {
        unsupported_err_unless!(len == 1, expr.span, "expected decreases", &args);
        let typ = typ_of_node(bctx, &args[0].hir_id);
        let header = Arc::new(HeaderExprX::Decreases(vir_args[0].clone(), typ));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_admit {
        unsupported_err_unless!(len == 0, expr.span, "expected admit", args);
        Ok(mk_expr(ExprX::Admit))
    } else if is_smt_binary {
        unsupported_err_unless!(len == 2, expr.span, "expected binary op", args);
        let lhs = vir_args[0].clone();
        let rhs = vir_args[1].clone();
        let vop = if is_eq {
            BinaryOp::Eq
        } else if is_ne {
            BinaryOp::Ne
        } else if is_le {
            BinaryOp::Le
        } else if is_ge {
            BinaryOp::Ge
        } else if is_lt {
            BinaryOp::Lt
        } else if is_gt {
            BinaryOp::Gt
        } else if is_add {
            BinaryOp::Add
        } else if is_sub {
            BinaryOp::Sub
        } else if is_mul {
            BinaryOp::Mul
        } else if is_implies {
            BinaryOp::Implies
        } else {
            panic!("internal error")
        };
        let e = mk_expr(ExprX::Binary(vop, lhs, rhs));
        if is_arith_binary { Ok(mk_ty_clip(&expr_typ, &e)) } else { Ok(e) }
    } else {
        let fun_ty = bctx.types.node_type(fun.hir_id);
        let (param_typs, ret_typ) = match fun_ty.kind() {
            TyKind::FnDef(def_id, _substs) => match tcx.fn_sig(*def_id).no_bound_vars() {
                None => unsupported_err!(expr.span, format!("found bound vars in function"), expr),
                Some(f) => {
                    let params: Vec<Typ> =
                        f.inputs().iter().map(|t| mid_ty_to_vir(tcx, *t)).collect();
                    let ret = mid_ty_to_vir_opt(tcx, f.output());
                    (params, ret)
                }
            },
            _ => {
                unsupported_err!(expr.span, format!("call to non-FnDef function"), expr)
            }
        };
        // box arguments where necessary
        assert_eq!(vir_args.len(), param_typs.len());
        for i in 0..vir_args.len() {
            let arg = &vir_args[i].clone();
            match (&*param_typs[i], &*arg.typ) {
                (TypX::TypParam(_), TypX::TypParam(_)) => {} // already boxed
                (TypX::TypParam(_), _) => {
                    let arg_typ = Arc::new(TypX::Boxed(arg.typ.clone()));
                    let arg_x = ExprX::UnaryOpr(UnaryOpr::Box(arg.typ.clone()), arg.clone());
                    vir_args[i] = SpannedTyped::new(&arg.span, &arg_typ, arg_x);
                }
                _ => {}
            }
        }
        // type arguments
        let mut typ_args: Vec<Typ> = Vec::new();
        for typ_arg in bctx.types.node_substs(fun.hir_id) {
            match typ_arg.unpack() {
                GenericArgKind::Type(ty) => {
                    typ_args.push(mid_ty_to_vir(tcx, ty));
                }
                _ => unsupported_err!(expr.span, format!("lifetime/const type arguments"), expr),
            }
        }
        // return type
        let possibly_boxed_ret_typ = match &ret_typ {
            None => Arc::new(TypX::Unit),
            Some(ret_typ) => match (&**ret_typ, &*expr_typ) {
                (TypX::TypParam(_), TypX::TypParam(_)) => expr_typ.clone(), // already boxed
                (TypX::TypParam(_), _) => Arc::new(TypX::Boxed(expr_typ.clone())),
                _ => expr_typ.clone(),
            },
        };
        // make call
        let mut call = spanned_typed_new(
            expr.span,
            &possibly_boxed_ret_typ,
            ExprX::Call(def_id_to_vir_path(tcx, f), Arc::new(typ_args), Arc::new(vir_args)),
        );
        // unbox result if necessary
        if let Some(ret_typ) = ret_typ {
            match (&*ret_typ, &*expr_typ) {
                (TypX::TypParam(_), TypX::TypParam(_)) => {} // already boxed
                (TypX::TypParam(_), _) => {
                    let call_x = ExprX::UnaryOpr(UnaryOpr::Unbox(expr_typ.clone()), call);
                    call = mk_expr(call_x);
                }
                _ => {}
            }
        }
        Ok(call)
    }
}

pub(crate) fn expr_tuple_datatype_ctor_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    res: &Res,
    args_slice: &[Expr<'tcx>],
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let expr_typ = typ_of_node(bctx, &expr.hir_id);
    let variant = tcx.expect_variant_res(*res);
    if let Res::Def(DefKind::Ctor(ctor_of, ctor_kind), _def_id) = res {
        unsupported_unless!(
            ctor_of == &rustc_hir::def::CtorOf::Variant,
            "non_variant_ctor_in_call_expr",
            expr
        );
        unsupported_unless!(
            ctor_kind == &rustc_hir::def::CtorKind::Fn
                || ctor_kind == &rustc_hir::def::CtorKind::Const,
            "non_fn_ctor_in_call_expr",
            expr
        );
    }
    let vir_path = {
        // TODO is there a safer way to do this?
        let mut vir_path = def_id_to_vir_path(tcx, res.def_id());
        Arc::get_mut(&mut vir_path).unwrap().pop(); // remove constructor
        Arc::get_mut(&mut vir_path).unwrap().pop(); // remove variant
        vir_path
    };
    let name = vir_path.last().expect("invalid path in datatype ctor");
    let variant_name = variant_ident(name.as_str(), &variant.ident.as_str());
    let vir_fields = Arc::new(
        args_slice
            .iter()
            .enumerate()
            .map(|(i, e)| -> Result<_, VirErr> {
                // TODO: deduplicate with Struct?
                let fielddef = &variant.fields[i];
                let field_typ = mid_ty_to_vir(tcx, tcx.type_of(fielddef.did));
                let f_expr_typ = typ_of_node(bctx, &e.hir_id);
                let mut vir = expr_to_vir(bctx, e)?;
                match (&*field_typ, &*f_expr_typ) {
                    (TypX::TypParam(_), TypX::TypParam(_)) => {} // already boxed
                    (TypX::TypParam(_), _) => {
                        vir = SpannedTyped::new(
                            &vir.span,
                            &Arc::new(TypX::Boxed(f_expr_typ.clone())),
                            ExprX::UnaryOpr(UnaryOpr::Box(f_expr_typ), vir.clone()),
                        );
                    }
                    _ => {}
                }
                Ok(ident_binder(&variant_positional_field_ident(&variant_name, i), &vir))
            })
            .collect::<Result<Vec<_>, _>>()?,
    );
    Ok(spanned_typed_new(expr.span, &expr_typ, ExprX::Ctor(vir_path, variant_name, vir_fields)))
}

pub(crate) fn expr_to_vir_inner<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let tc = bctx.types;
    let expr_typ = typ_of_node(bctx, &expr.hir_id);
    let mk_expr = |x: ExprX| spanned_typed_new(expr.span, &expr_typ, x);

    match &expr.kind {
        ExprKind::Block(body, _) => {
            let vir_stmts: Stmts = Arc::new(
                slice_vec_map_result(body.stmts, |stmt| stmt_to_vir(bctx, stmt))?
                    .into_iter()
                    .flatten()
                    .collect(),
            );
            let vir_expr = body.expr.map(|expr| expr_to_vir(bctx, &expr)).transpose()?;
            Ok(mk_expr(ExprX::Block(vir_stmts, vir_expr)))
        }
        ExprKind::Call(fun, args_slice) => {
            match fun.kind {
                // a tuple-style datatype constructor
                ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: res @ Res::Def(DefKind::Ctor(_, _), _), .. },
                )) => expr_tuple_datatype_ctor_to_vir(bctx, expr, res, *args_slice),
                // a function
                ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: Res::Def(DefKind::Fn, _), .. },
                )) => fn_call_to_vir(bctx, expr, fun, args_slice),
                _ => unsupported!("fun_kind_not_ctor_or_fn", expr.span),
            }
        }
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Bool(b) => {
                let c = vir::ast::Constant::Bool(b);
                Ok(mk_expr(ExprX::Const(c)))
            }
            rustc_ast::LitKind::Int(i, _) => {
                let typ = typ_of_node(bctx, &expr.hir_id);
                let c = vir::ast::Constant::Nat(Arc::new(i.to_string()));
                if let TypX::Int(range) = *typ {
                    match range {
                        IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::USize => {
                            Ok(mk_expr(ExprX::Const(c)))
                        }
                        IntRange::I(_) | IntRange::ISize => {
                            Ok(mk_clip(&range, &mk_expr(ExprX::Const(c))))
                        }
                    }
                } else {
                    panic!("unexpected constant: {:?} {:?}", lit, typ)
                }
            }
            _ => {
                panic!("unexpected constant: {:?}", lit)
            }
        },
        ExprKind::Cast(source, _) => Ok(mk_ty_clip(&expr_typ, &expr_to_vir(bctx, source)?)),
        ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, e) => expr_to_vir_inner(bctx, e),
        ExprKind::Unary(op, arg) => match op {
            UnOp::Not => {
                let varg = expr_to_vir(bctx, arg)?;
                Ok(mk_expr(ExprX::Unary(UnaryOp::Not, varg)))
            }
            UnOp::Deref => match bctx.types.node_type(arg.hir_id).kind() {
                TyKind::Ref(_, _tys, rustc_ast::Mutability::Not) => expr_to_vir_inner(bctx, arg),
                _ => unsupported_err!(expr.span, "dereferencing this type is unsupported", expr),
            },
            _ => {
                unsupported_err!(expr.span, "unary expression", expr)
            }
        },
        ExprKind::Binary(op, lhs, rhs) => {
            let vlhs = expr_to_vir(bctx, lhs)?;
            let vrhs = expr_to_vir(bctx, rhs)?;
            match op.node {
                BinOpKind::Eq | BinOpKind::Ne => unsupported_err_unless!(
                    is_smt_equality(bctx, expr.span, &lhs.hir_id, &rhs.hir_id),
                    expr.span,
                    "==/!= for non smt equality types",
                    expr
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
                BinOpKind::Eq => BinaryOp::Eq,
                BinOpKind::Ne => BinaryOp::Ne,
                BinOpKind::Le => BinaryOp::Le,
                BinOpKind::Ge => BinaryOp::Ge,
                BinOpKind::Lt => BinaryOp::Lt,
                BinOpKind::Gt => BinaryOp::Gt,
                BinOpKind::Add => BinaryOp::Add,
                BinOpKind::Sub => BinaryOp::Sub,
                BinOpKind::Mul => BinaryOp::Mul,
                BinOpKind::Div => BinaryOp::EuclideanDiv,
                BinOpKind::Rem => BinaryOp::EuclideanMod,
                _ => unsupported_err!(expr.span, format!("binary operator {:?}", op)),
            };
            let e = mk_expr(ExprX::Binary(vop, vlhs, vrhs));
            match op.node {
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul => Ok(mk_ty_clip(&expr_typ, &e)),
                BinOpKind::Div | BinOpKind::Rem => {
                    // TODO: disallow divide-by-zero in executable code?
                    match mk_range(tc.node_type(expr.hir_id)) {
                        IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::USize => {
                            // Euclidean division
                            Ok(e)
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
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(id) => match tcx.hir().get(id) {
                Node::Binding(pat) => Ok(mk_expr(ExprX::Var(Arc::new(pat_to_var(pat))))),
                node => unsupported_err!(expr.span, format!("Path {:?}", node)),
            },
            Res::Def(def_kind, id) => {
                match def_kind {
                    DefKind::Fn => {
                        let name = hack_get_def_name(tcx, id); // TODO: proper handling of paths
                        Ok(mk_expr(ExprX::Var(Arc::new(name))))
                    }
                    DefKind::Ctor(_, _ctor_kind) => {
                        expr_tuple_datatype_ctor_to_vir(bctx, expr, &path.res, &[])
                    }
                    _ => {
                        unsupported_err!(expr.span, format!("Path {:?} kind {:?}", id, def_kind))
                    }
                }
            }
            res => unsupported_err!(expr.span, format!("Path {:?}", res)),
        },
        ExprKind::Assign(lhs, rhs, _) => {
            Ok(mk_expr(ExprX::Assign(expr_to_vir(bctx, lhs)?, expr_to_vir(bctx, rhs)?)))
        }
        ExprKind::Field(lhs, name) => {
            let vir_lhs = expr_to_vir(bctx, lhs)?;
            let lhs_ty = tc.node_type(lhs.hir_id);
            let (datatype, field_name, unbox) = if let Some(adt_def) = lhs_ty.ty_adt_def() {
                unsupported_err_unless!(
                    adt_def.variants.len() == 1,
                    expr.span,
                    "field_of_adt_with_multiple_variants",
                    expr
                );
                let datatype_path = def_id_to_vir_path(tcx, adt_def.did);
                let datatype_name = datatype_path.last().unwrap();
                let variant = adt_def.variants.iter().next().unwrap();
                let variant_name = variant_ident(datatype_name.as_str(), &variant.ident.as_str());
                // TODO: deduplicate with Ctor?
                // TODO: is there a compiler function to do this instead?
                let fielddef = variant.fields.iter().find(|x| &x.ident == name).expect(
                    format!("cannot find field {:?} in struct {:?}", name, datatype_path).as_str(),
                );
                let field_typ = mid_ty_to_vir(tcx, tcx.type_of(fielddef.did));
                let unbox = match (&*expr_typ, &*field_typ) {
                    (TypX::TypParam(_), TypX::TypParam(_)) => None,
                    (_, TypX::TypParam(_)) => Some(expr_typ.clone()),
                    _ => None,
                };
                (datatype_path, variant_field_ident(&variant_name, &name.as_str()), unbox)
            } else {
                unsupported_err!(expr.span, "field_of_non_adt", expr)
            };
            let field_type = match &unbox {
                None => expr_typ.clone(),
                Some(_) => Arc::new(TypX::Boxed(expr_typ.clone())),
            };
            let mut vir = spanned_typed_new(
                expr.span,
                &field_type,
                ExprX::Field { lhs: vir_lhs, datatype, field_name },
            );
            if let Some(target_typ) = unbox {
                vir = SpannedTyped::new(
                    &vir.span,
                    &expr_typ,
                    ExprX::UnaryOpr(UnaryOpr::Unbox(target_typ), vir.clone()),
                );
            }
            Ok(vir)
        }
        ExprKind::If(cond, lhs, rhs) => {
            let vir_cond = expr_to_vir(bctx, cond)?;
            let vir_lhs = expr_to_vir(bctx, lhs)?;
            let vir_rhs = rhs.map(|e| expr_to_vir(bctx, e)).transpose()?;
            Ok(mk_expr(ExprX::If(vir_cond, vir_lhs, vir_rhs)))
        }
        ExprKind::Loop(
            Block {
                stmts: [],
                expr:
                    Some(Expr {
                        kind:
                            ExprKind::Match(
                                cond,
                                [Arm {
                                    pat:
                                        Pat {
                                            kind:
                                                PatKind::Lit(Expr {
                                                    kind:
                                                        ExprKind::Lit(rustc_span::source_map::Spanned {
                                                            node: LitKind::Bool(true),
                                                            ..
                                                        }),
                                                    ..
                                                }),
                                            ..
                                        },
                                    guard: None,
                                    body,
                                    ..
                                }, Arm {
                                    pat: Pat { kind: PatKind::Wild, .. },
                                    guard: None,
                                    body:
                                        Expr {
                                            kind:
                                                ExprKind::Break(Destination { label: None, .. }, None),
                                            ..
                                        },
                                    ..
                                }],
                                MatchSource::WhileDesugar,
                            ),
                        ..
                    }),
                ..
            },
            None,
            LoopSource::While,
            _span,
        ) => {
            let cond = match cond {
                Expr { kind: ExprKind::DropTemps(cond), .. } => cond,
                _ => cond,
            };
            let cond = expr_to_vir(bctx, cond)?;
            let mut body = expr_to_vir(bctx, body)?;
            let header = vir::headers::read_header(&mut body)?;
            let invs = header.invariant;
            Ok(mk_expr(ExprX::While { cond, body, invs }))
        }
        ExprKind::Struct(qpath, fields, spread) => {
            unsupported_unless!(spread.is_none(), "spread_in_struct_ctor");
            let (path, variant, variant_name) = match qpath {
                QPath::Resolved(slf, path) => {
                    unsupported_unless!(
                        matches!(path.res, Res::Def(DefKind::Struct | DefKind::Variant, _)),
                        "non_struct_ctor",
                        path.res
                    );
                    unsupported_unless!(slf.is_none(), "self_in_struct_qpath");
                    let variant = tcx.expect_variant_res(path.res);
                    let mut vir_path = def_id_to_vir_path(tcx, path.res.def_id());
                    if let Res::Def(DefKind::Variant, _) = path.res {
                        Arc::get_mut(&mut vir_path)
                            .unwrap()
                            .pop()
                            .expect(format!("variant name in Struct ctor for {:?}", path).as_str());
                    }
                    let name = vir_path
                        .last()
                        .expect(format!("adt name in Struct ctor for {:?}", path).as_str());
                    let variant_name = variant_ident(&name, &variant.ident.as_str());
                    (vir_path, variant, variant_name)
                }
                _ => panic!("unexpected qpath {:?}", qpath),
            };
            let vir_fields = Arc::new(
                fields
                    .iter()
                    .map(|f| -> Result<_, VirErr> {
                        // TODO: is there a compiler function to do this instead?
                        let fielddef = variant.fields.iter().find(|x| x.ident == f.ident).expect(
                            format!("cannot find field {:?} in struct {:?}", f.ident, path)
                                .as_str(),
                        );
                        let field_typ = mid_ty_to_vir(tcx, tcx.type_of(fielddef.did));
                        let f_expr_typ = typ_of_node(bctx, &f.expr.hir_id);
                        let mut vir = expr_to_vir(bctx, f.expr)?;
                        // TODO: deduplicate with Call?
                        match (&*field_typ, &*f_expr_typ) {
                            (TypX::TypParam(_), TypX::TypParam(_)) => {} // already boxed
                            (TypX::TypParam(_), _) => {
                                vir = SpannedTyped::new(
                                    &vir.span,
                                    &Arc::new(TypX::Boxed(f_expr_typ.clone())),
                                    ExprX::UnaryOpr(UnaryOpr::Box(f_expr_typ.clone()), vir.clone()),
                                );
                            }
                            _ => {}
                        }
                        Ok(ident_binder(
                            &variant_field_ident(&variant_name, &f.ident.as_str()),
                            &vir,
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            Ok(mk_expr(ExprX::Ctor(path, variant_name, vir_fields)))
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
    let Pat { hir_id, kind, span: _, default_binding_modes } = pattern;
    unsupported_err_unless!(default_binding_modes, pattern.span, "default_binding_modes");
    match pattern.kind {
        PatKind::Binding(annotation, _id, ident, pat) => {
            let mutable = match annotation {
                BindingAnnotation::Unannotated => false,
                BindingAnnotation::Mutable => true,
                _ => {
                    unsupported_err!(pattern.span, format!("binding annotation {:?}", annotation))
                }
            };
            match pat {
                None => {}
                _ => {
                    unsupported_err!(pattern.span, format!("pattern {:?}", kind))
                }
            }
            // TODO: need unique identifiers!
            let name = Arc::new(ident_to_var(&ident));
            let typ = typ_of_node(bctx, hir_id);
            let mode = get_var_mode(bctx.mode, attrs);
            Ok(vec![spanned_new(
                pattern.span,
                StmtX::Decl {
                    param: spanned_new(pattern.span, ParamX { name: name.clone(), typ, mode }),
                    mutable,
                    init: initializer.map(|e| expr_to_vir(bctx, e)).transpose()?,
                },
            )])
        }
        _ => {
            unsupported_err!(pattern.span, "let_pattern", pattern)
        }
    }
}

pub(crate) fn stmt_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    stmt: &Stmt<'tcx>,
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    match &stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
            let vir_expr = expr_to_vir(bctx, expr)?;
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
