use crate::rust_to_vir_base::{
    def_id_to_vir_path, get_trigger, get_var_mode, hack_check_def_name, hack_get_def_name,
    ident_to_var, is_smt_arith, is_smt_equality, mid_ty_to_vir, mid_ty_to_vir_opt, mk_range,
    ty_to_vir, typ_of_node, Ctxt,
};
use crate::util::{
    err_span_str, slice_vec_map_result, spanned_new, unsupported_err_span, vec_map, vec_map_result,
};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use air::ast::{Binder, BinderX, Quant};
use rustc_ast::{Attribute, LitKind};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    Arm, BinOpKind, BindingAnnotation, Block, Destination, Expr, ExprKind, Local, LoopSource,
    MatchSource, Node, Pat, PatKind, QPath, Stmt, StmtKind, UnOp,
};
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::TyKind;
use rustc_span::def_id::DefId;
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{
    BinaryOp, Constant, ExprX, HeaderExpr, HeaderExprX, IntRange, ParamX, StmtX, Stmts, Typ, TypX,
    UnaryOp, UnaryOpr, VirErr,
};
use vir::ast_util::ident_binder;
use vir::def::{variant_field_ident, variant_ident, variant_positional_field_ident, Spanned};

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

fn get_ensures_arg<'tcx>(ctxt: &Ctxt<'tcx>, expr: &Expr<'tcx>) -> Result<vir::ast::Expr, VirErr> {
    if matches!(ctxt.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
        expr_to_vir(ctxt, expr)
    } else {
        err_span_str(expr.span, "ensures needs a bool expression")
    }
}

fn extract_ensures<'tcx>(ctxt: &Ctxt<'tcx>, expr: &'tcx Expr<'tcx>) -> Result<HeaderExpr, VirErr> {
    let tcx = ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, fn_decl, body_id, _, _) => {
            let typs: Vec<Typ> = fn_decl.inputs.iter().map(|t| ty_to_vir(tcx, t)).collect();
            let body = tcx.hir().body(*body_id);
            let xs: Vec<String> = body.params.iter().map(|param| pat_to_var(param.pat)).collect();
            let expr = &body.value;
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(ctxt, e))?;
            if typs.len() == 1 && xs.len() == 1 {
                let id_typ = Some((Rc::new(xs[0].clone()), typs[0].clone()));
                Ok(Rc::new(HeaderExprX::Ensures(id_typ, Rc::new(args))))
            } else {
                err_span_str(expr.span, "expected 1 parameter in closure")
            }
        }
        _ => {
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(ctxt, e))?;
            Ok(Rc::new(HeaderExprX::Ensures(None, Rc::new(args))))
        }
    }
}

fn extract_quant<'tcx>(
    ctxt: &Ctxt<'tcx>,
    span: Span,
    quant: Quant,
    expr: &'tcx Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, fn_decl, body_id, _, _) => {
            let body = tcx.hir().body(*body_id);
            let binders: Vec<Binder<Typ>> = body
                .params
                .iter()
                .zip(fn_decl.inputs)
                .map(|(x, t)| {
                    Rc::new(BinderX { name: Rc::new(pat_to_var(x.pat)), a: ty_to_vir(tcx, t) })
                })
                .collect();
            let expr = &body.value;
            if !matches!(ctxt.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
                return err_span_str(expr.span, "forall/ensures needs a bool expression");
            }
            let vir_expr = expr_to_vir(ctxt, expr)?;
            Ok(spanned_new(span, ExprX::Quant(quant, Rc::new(binders), vir_expr)))
        }
        _ => err_span_str(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn mk_clip<'tcx>(range: &IntRange, expr: &vir::ast::Expr) -> vir::ast::Expr {
    match range {
        IntRange::Int => expr.clone(),
        range => Spanned::new(expr.span.clone(), ExprX::Unary(UnaryOp::Clip(*range), expr.clone())),
    }
}

fn mk_ty_clip<'tcx>(ty: rustc_middle::ty::Ty<'tcx>, expr: &vir::ast::Expr) -> vir::ast::Expr {
    mk_clip(&mk_range(ty), expr)
}

pub(crate) fn expr_to_vir<'tcx>(
    ctxt: &Ctxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let mut vir_expr = expr_to_vir_inner(ctxt, expr)?;
    for group in get_trigger(expr.span, ctxt.tcx.hir().attrs(expr.hir_id))? {
        vir_expr = spanned_new(expr.span, ExprX::Unary(UnaryOp::Trigger(group), vir_expr));
    }
    Ok(vir_expr)
}

fn fn_call_to_vir<'tcx>(
    ctxt: &Ctxt<'tcx>,
    expr: &Expr<'tcx>,
    fun: &'tcx Expr<'tcx>,
    args_slice: &'tcx [Expr<'tcx>],
) -> Result<vir::ast::Expr, VirErr> {
    let mut args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();
    let f = expr_to_function(fun);
    let is_admit = hack_check_def_name(ctxt.tcx, f, "builtin", "admit");
    let is_requires = hack_check_def_name(ctxt.tcx, f, "builtin", "requires");
    let is_ensures = hack_check_def_name(ctxt.tcx, f, "builtin", "ensures");
    let is_invariant = hack_check_def_name(ctxt.tcx, f, "builtin", "invariant");
    let is_decreases = hack_check_def_name(ctxt.tcx, f, "builtin", "decreases");
    let is_forall = hack_check_def_name(ctxt.tcx, f, "builtin", "forall");
    let is_exists = hack_check_def_name(ctxt.tcx, f, "builtin", "exists");
    let is_hide = hack_check_def_name(ctxt.tcx, f, "builtin", "hide");
    let is_reveal = hack_check_def_name(ctxt.tcx, f, "builtin", "reveal");
    let is_reveal_fuel = hack_check_def_name(ctxt.tcx, f, "builtin", "reveal_with_fuel");
    let is_implies = hack_check_def_name(ctxt.tcx, f, "builtin", "imply");
    let is_eq = hack_check_def_name(ctxt.tcx, f, "core", "cmp::PartialEq::eq");
    let is_ne = hack_check_def_name(ctxt.tcx, f, "core", "cmp::PartialEq::ne");
    let is_le = hack_check_def_name(ctxt.tcx, f, "core", "cmp::PartialOrd::le");
    let is_ge = hack_check_def_name(ctxt.tcx, f, "core", "cmp::PartialOrd::ge");
    let is_lt = hack_check_def_name(ctxt.tcx, f, "core", "cmp::PartialOrd::lt");
    let is_gt = hack_check_def_name(ctxt.tcx, f, "core", "cmp::PartialOrd::gt");
    let is_add = hack_check_def_name(ctxt.tcx, f, "core", "ops::arith::Add::add");
    let is_sub = hack_check_def_name(ctxt.tcx, f, "core", "ops::arith::Sub::sub");
    let is_mul = hack_check_def_name(ctxt.tcx, f, "core", "ops::arith::Mul::mul");
    let is_cmp = is_eq || is_ne || is_le || is_ge || is_lt || is_gt;
    let is_arith_binary = is_add || is_sub || is_mul;

    let len = args.len();
    if is_requires {
        unsupported_err_unless!(len == 1, expr.span, "expected requires", &args);
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(ctxt.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "requires needs a bool expression");
            }
        }
    }
    if is_ensures {
        unsupported_err_unless!(len == 1, expr.span, "expected ensures", &args);
        let header = extract_ensures(ctxt, args[0])?;
        let expr = spanned_new(args[0].span, ExprX::Header(header));
        return Ok(expr);
    }
    if is_invariant {
        unsupported_err_unless!(len == 1, expr.span, "expected invariant", &args);
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(ctxt.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "invariant needs a bool expression");
            }
        }
    }
    if is_forall || is_exists {
        unsupported_err_unless!(len == 1, expr.span, "expected forall/exists", &args);
        let quant = if is_forall { Quant::Forall } else { Quant::Exists };
        return extract_quant(ctxt, expr.span, quant, args[0]);
    }

    let mut vir_args = vec_map_result(&args, |arg| expr_to_vir(ctxt, arg))?;

    let is_smt_binary = if is_eq || is_ne {
        is_smt_equality(ctxt, expr.span, &args[0].hir_id, &args[1].hir_id)
    } else if is_cmp || is_arith_binary || is_implies {
        is_smt_arith(ctxt, &args[0].hir_id, &args[1].hir_id)
    } else {
        false
    };

    if is_requires {
        let header = Rc::new(HeaderExprX::Requires(Rc::new(vir_args)));
        Ok(spanned_new(expr.span, ExprX::Header(header)))
    } else if is_invariant {
        let header = Rc::new(HeaderExprX::Invariant(Rc::new(vir_args)));
        Ok(spanned_new(expr.span, ExprX::Header(header)))
    } else if is_decreases {
        unsupported_err_unless!(len == 1, expr.span, "expected decreases", &args);
        let typ = typ_of_node(ctxt, &args[0].hir_id);
        let header = Rc::new(HeaderExprX::Decreases(vir_args[0].clone(), typ));
        Ok(spanned_new(expr.span, ExprX::Header(header)))
    } else if is_admit {
        unsupported_err_unless!(len == 0, expr.span, "expected admit", args);
        Ok(spanned_new(expr.span, ExprX::Admit))
    } else if is_hide || is_reveal {
        unsupported_err_unless!(len == 1, expr.span, "expected hide/reveal", args);
        let arg = vir_args[0].clone();
        if let ExprX::Var(x) = &arg.x {
            if is_hide {
                let header = Rc::new(HeaderExprX::Hide(x.clone()));
                Ok(spanned_new(expr.span, ExprX::Header(header)))
            } else {
                Ok(spanned_new(expr.span, ExprX::Fuel(x.clone(), 1)))
            }
        } else {
            err_span_str(expr.span, "hide/reveal: expected identifier")
        }
    } else if is_reveal_fuel {
        unsupported_err_unless!(len == 2, expr.span, "expected reveal_fuel", args);
        match (&vir_args[0].x, &vir_args[1].x) {
            (ExprX::Var(x), ExprX::Const(Constant::Nat(s))) => {
                let n = s.parse::<u32>().expect(&format!("internal error: parse {}", s));
                Ok(spanned_new(expr.span, ExprX::Fuel(x.clone(), n)))
            }
            (ExprX::Var(_), _) => panic!("internal error: is_reveal_fuel"),
            _ => err_span_str(expr.span, "hide/reveal: expected identifier"),
        }
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
        let e = spanned_new(expr.span, ExprX::Binary(vop, lhs, rhs));
        let ty = ctxt.types.node_type(expr.hir_id);
        if is_arith_binary { Ok(mk_ty_clip(ty, &e)) } else { Ok(e) }
    } else {
        let fun_ty = ctxt.types.node_type(fun.hir_id);
        let (param_typs, ret_typ) = match fun_ty.kind() {
            TyKind::FnDef(def_id, _substs) => match ctxt.tcx.fn_sig(*def_id).no_bound_vars() {
                None => unsupported_err!(expr.span, format!("found bound vars in function"), expr),
                Some(f) => {
                    let params: Vec<Typ> =
                        f.inputs().iter().map(|t| mid_ty_to_vir(ctxt.tcx, *t)).collect();
                    let ret = mid_ty_to_vir_opt(ctxt.tcx, f.output());
                    (params, ret)
                }
            },
            _ => unsupported_err!(expr.span, format!("call to non-FnDef function"), expr),
        };
        // box arguments where necessary
        let arg_typs = vec_map(&args, |arg| typ_of_node(ctxt, &arg.hir_id));
        assert_eq!(vir_args.len(), param_typs.len());
        assert_eq!(vir_args.len(), arg_typs.len());
        for i in 0..vir_args.len() {
            match (&*param_typs[i], &*arg_typs[i]) {
                (TypX::TypParam(_), TypX::TypParam(_)) => {} // already boxed
                (TypX::TypParam(_), _) => {
                    let arg = &vir_args[i];
                    let arg_x = ExprX::UnaryOpr(UnaryOpr::Box(arg_typs[i].clone()), arg.clone());
                    vir_args[i] = Spanned::new(arg.span.clone(), arg_x);
                }
                _ => {}
            }
        }
        // type arguments
        let mut typ_args: Vec<Typ> = Vec::new();
        for typ_arg in ctxt.types.node_substs(fun.hir_id) {
            match typ_arg.unpack() {
                GenericArgKind::Type(ty) => {
                    typ_args.push(mid_ty_to_vir(ctxt.tcx, ty));
                }
                _ => unsupported_err!(expr.span, format!("lifetime/const type arguments"), expr),
            }
        }
        // make call
        let name = hack_get_def_name(ctxt.tcx, f); // TODO: proper handling of paths
        let mut call = spanned_new(
            expr.span,
            ExprX::Call(Rc::new(name), Rc::new(typ_args), Rc::new(vir_args)),
        );
        // unbox result if necessary
        if let Some(ret_typ) = ret_typ {
            let expr_typ = typ_of_node(ctxt, &expr.hir_id);
            match (&*ret_typ, &*expr_typ) {
                (TypX::TypParam(_), TypX::TypParam(_)) => {} // already boxed
                (TypX::TypParam(_), _) => {
                    let call_x = ExprX::UnaryOpr(UnaryOpr::Unbox(expr_typ.clone()), call);
                    call = spanned_new(expr.span, call_x);
                }
                _ => {}
            }
        }
        Ok(call)
    }
}

pub(crate) fn expr_to_vir_inner<'tcx>(
    ctxt: &Ctxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = ctxt.tcx;
    let tc = ctxt.types;
    match &expr.kind {
        ExprKind::Block(body, _) => {
            let vir_stmts: Stmts = Rc::new(
                slice_vec_map_result(body.stmts, |stmt| stmt_to_vir(ctxt, stmt))?
                    .into_iter()
                    .flatten()
                    .collect(),
            );
            let vir_expr = body.expr.map(|expr| expr_to_vir(ctxt, &expr)).transpose()?;
            Ok(spanned_new(expr.span, ExprX::Block(vir_stmts, vir_expr)))
        }
        ExprKind::Call(fun, args_slice) => {
            match fun.kind {
                // a tuple-style datatype constructor
                ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: Res::Def(ctor @ DefKind::Ctor(_, _), def_id), .. },
                )) => {
                    if let DefKind::Ctor(ctor_of, ctor_kind) = ctor {
                        unsupported_unless!(
                            ctor_of == &rustc_hir::def::CtorOf::Variant,
                            "non_variant_ctor_in_call_expr",
                            fun
                        );
                        unsupported_unless!(
                            ctor_kind == &rustc_hir::def::CtorKind::Fn,
                            "non_fn_ctor_in_call_expr",
                            fun
                        );
                        let (vir_path, variant) = {
                            let mut vir_path = def_id_to_vir_path(tcx, *def_id);
                            Rc::get_mut(&mut vir_path).unwrap().pop(); // remove constructor
                            let variant = Rc::get_mut(&mut vir_path)
                                .unwrap()
                                .pop()
                                .expect("invalid path in datatype ctor");
                            (vir_path, variant)
                        };
                        let name = vir_path.last().expect("invalid path in datatype ctor");
                        let variant_name = variant_ident(name.as_str(), variant.as_str());
                        let vir_fields = Rc::new(
                            args_slice
                                .iter()
                                .enumerate()
                                .map(|(i, e)| -> Result<_, VirErr> {
                                    Ok(ident_binder(
                                        &variant_positional_field_ident(&variant_name, i),
                                        &expr_to_vir(ctxt, e)?,
                                    ))
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        );
                        Ok(spanned_new(expr.span, ExprX::Ctor(vir_path, variant_name, vir_fields)))
                    } else {
                        unreachable!()
                    }
                }
                // a function
                ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: Res::Def(DefKind::Fn, _), .. },
                )) => fn_call_to_vir(ctxt, expr, fun, args_slice),
                _ => unsupported!("fun_kind_not_ctor_or_fn"),
            }
        }
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Bool(b) => {
                let c = vir::ast::Constant::Bool(b);
                Ok(spanned_new(expr.span, ExprX::Const(c)))
            }
            rustc_ast::LitKind::Int(i, _) => {
                let typ = typ_of_node(ctxt, &expr.hir_id);
                let c = vir::ast::Constant::Nat(Rc::new(i.to_string()));
                if let TypX::Int(range) = *typ {
                    match range {
                        IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::USize => {
                            Ok(spanned_new(expr.span, ExprX::Const(c)))
                        }
                        IntRange::I(_) | IntRange::ISize => {
                            Ok(mk_clip(&range, &spanned_new(expr.span, ExprX::Const(c))))
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
        ExprKind::Cast(source, _) => {
            Ok(mk_ty_clip(tc.node_type(expr.hir_id), &expr_to_vir(ctxt, source)?))
        }
        ExprKind::Unary(op, arg) => {
            let varg = expr_to_vir(ctxt, arg)?;
            let vop = match op {
                UnOp::Not => UnaryOp::Not,
                _ => {
                    unsupported_err!(expr.span, "unary expression", expr)
                }
            };
            Ok(spanned_new(expr.span, ExprX::Unary(vop, varg)))
        }
        ExprKind::Binary(op, lhs, rhs) => {
            let vlhs = expr_to_vir(ctxt, lhs)?;
            let vrhs = expr_to_vir(ctxt, rhs)?;
            match op.node {
                BinOpKind::Eq | BinOpKind::Ne => unsupported_unless!(
                    is_smt_equality(ctxt, expr.span, &lhs.hir_id, &rhs.hir_id),
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
                    is_smt_arith(ctxt, &lhs.hir_id, &rhs.hir_id),
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
                _ => unsupported_err!(expr.span, format!("binary operator {:?}", op)),
            };
            let e = spanned_new(expr.span, ExprX::Binary(vop, vlhs, vrhs));
            match op.node {
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul => {
                    Ok(mk_ty_clip(tc.node_type(expr.hir_id), &e))
                }
                _ => Ok(e),
            }
        }
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(id) => match tcx.hir().get(id) {
                Node::Binding(pat) => {
                    Ok(spanned_new(expr.span, ExprX::Var(Rc::new(pat_to_var(pat)))))
                }
                node => unsupported_err!(expr.span, format!("Path {:?}", node)),
            },
            Res::Def(_, id) => {
                let name = hack_get_def_name(tcx, id); // TODO: proper handling of paths
                Ok(spanned_new(expr.span, ExprX::Var(Rc::new(name))))
            }
            res => unsupported_err!(expr.span, format!("Path {:?}", res)),
        },
        ExprKind::Assign(lhs, rhs, _) => Ok(spanned_new(
            expr.span,
            ExprX::Assign(expr_to_vir(ctxt, lhs)?, expr_to_vir(ctxt, rhs)?),
        )),
        ExprKind::Field(lhs, name) => {
            let vir_lhs = expr_to_vir(ctxt, lhs)?;
            let lhs_ty = tc.node_type(lhs.hir_id);
            let (datatype_name, field_name) = if let Some(adt_def) = lhs_ty.ty_adt_def() {
                unsupported_err_unless!(
                    adt_def.variants.len() == 1,
                    expr.span,
                    "field_of_adt_with_multiple_variants",
                    expr
                );
                let datatype_name = hack_get_def_name(tcx, adt_def.did);
                let variant_name = variant_ident(datatype_name.as_str(), datatype_name.as_str());
                (Rc::new(datatype_name), variant_field_ident(&variant_name, &name.as_str()))
            } else {
                unsupported_err!(expr.span, "field_of_non_adt", expr)
            };
            Ok(spanned_new(expr.span, ExprX::Field { lhs: vir_lhs, datatype_name, field_name }))
        }
        ExprKind::If(cond, lhs, rhs) => {
            let vir_cond = expr_to_vir(ctxt, cond)?;
            let vir_lhs = expr_to_vir(ctxt, lhs)?;
            let vir_rhs = rhs.map(|e| expr_to_vir(ctxt, e)).transpose()?;
            Ok(spanned_new(expr.span, ExprX::If(vir_cond, vir_lhs, vir_rhs)))
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
            let cond = expr_to_vir(ctxt, cond)?;
            let mut body = expr_to_vir(ctxt, body)?;
            let header = vir::headers::read_header(&mut body)?;
            let invs = header.invariant;
            Ok(spanned_new(expr.span, ExprX::While { cond, body, invs }))
        }
        ExprKind::Struct(qpath, fields, spread) => {
            unsupported_unless!(spread.is_none(), "spread_in_struct_ctor");
            let (path, variant_name) = match qpath {
                QPath::Resolved(slf, path) => {
                    unsupported_unless!(
                        matches!(path.res, Res::Def(DefKind::Struct, _)),
                        "non_struct_ctor"
                    );
                    unsupported_unless!(slf.is_none(), "self_in_struct_qpath");
                    let vir_path = def_id_to_vir_path(ctxt.tcx, path.res.def_id());
                    let name = hack_get_def_name(ctxt.tcx, path.res.def_id());
                    let variant_name = variant_ident(&name, &name);
                    (vir_path, variant_name)
                }
                _ => panic!("unexpected qpath {:?}", qpath),
            };
            let vir_fields = Rc::new(
                fields
                    .iter()
                    .map(|f| -> Result<_, VirErr> {
                        Ok(ident_binder(
                            &variant_field_ident(&variant_name, &f.ident.as_str()),
                            &expr_to_vir(ctxt, f.expr)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            Ok(spanned_new(expr.span, ExprX::Ctor(path, variant_name, vir_fields)))
        }
        _ => {
            unsupported_err!(expr.span, format!("expression"), expr)
        }
    }
}

pub(crate) fn let_stmt_to_vir<'tcx>(
    ctxt: &Ctxt<'tcx>,
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
            let name = Rc::new(ident_to_var(&ident));
            let typ = typ_of_node(ctxt, hir_id);
            let mode = get_var_mode(ctxt.mode, attrs);
            Ok(vec![spanned_new(
                pattern.span,
                StmtX::Decl {
                    param: spanned_new(pattern.span, ParamX { name: name.clone(), typ, mode }),
                    mutable,
                    init: initializer.map(|e| expr_to_vir(ctxt, e)).transpose()?,
                },
            )])
        }
        _ => {
            unsupported_err!(pattern.span, "let_pattern", pattern)
        }
    }
}

pub(crate) fn stmt_to_vir<'tcx>(
    ctxt: &Ctxt<'tcx>,
    stmt: &Stmt<'tcx>,
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    match &stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
            let vir_expr = expr_to_vir(ctxt, expr)?;
            Ok(vec![spanned_new(expr.span, StmtX::Expr(vir_expr))])
        }
        StmtKind::Local(Local { pat, init, .. }) => {
            let_stmt_to_vir(ctxt, pat, init, ctxt.tcx.hir().attrs(stmt.hir_id))
        }
        _ => {
            unsupported_err!(stmt.span, "statement", stmt)
        }
    }
}
