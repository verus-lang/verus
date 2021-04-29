use crate::rust_to_vir_base::{
    get_var_mode, hack_check_def_name, hack_get_def_name, ident_to_var, mk_range, spanned_new,
    ty_to_vir, typ_of_node, Ctxt,
};
use crate::util::{slice_vec_map_result, vec_map_result};
use crate::{unsupported, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::def::Res;
use rustc_hir::{
    BinOpKind, BindingAnnotation, Expr, ExprKind, Local, Node, Pat, PatKind, QPath, Stmt, StmtKind,
    UnOp,
};
use rustc_middle::ty::TyKind;
use rustc_span::def_id::DefId;
use std::rc::Rc;
use vir::ast::{
    BinaryOp, ExprX, HeaderExpr, HeaderExprX, IntRange, ParamX, StmtX, Stmts, Typ, UnaryOp, VirErr,
};
use vir::ast_util::str_ident;
use vir::def::Spanned;

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
        Err(spanned_new(expr.span, "ensures needs a bool expression".to_string()))
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
                Err(spanned_new(expr.span, "expected 1 parameter in closure".to_string()))
            }
        }
        _ => {
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(ctxt, e))?;
            Ok(Rc::new(HeaderExprX::Ensures(None, Rc::new(args))))
        }
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
            let mut args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();
            let f = expr_to_function(fun);
            let is_assume = hack_check_def_name(tcx, f, "builtin", "assume");
            let is_assert = hack_check_def_name(tcx, f, "builtin", "assert");
            let is_requires = hack_check_def_name(tcx, f, "builtin", "requires");
            let is_ensures = hack_check_def_name(tcx, f, "builtin", "ensures");
            let is_hide = hack_check_def_name(tcx, f, "builtin", "hide");
            let is_reveal = hack_check_def_name(tcx, f, "builtin", "reveal");
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
            let is_cmp = is_eq || is_ne || is_le || is_ge || is_lt || is_gt;
            let is_arith_binary = is_add || is_sub || is_mul;

            if is_requires {
                args = extract_array(args[0]);
                for arg in &args {
                    if !matches!(tc.node_type(arg.hir_id).kind(), TyKind::Bool) {
                        let s = "requires needs a bool expression".to_string();
                        return Err(spanned_new(arg.span, s));
                    }
                }
            }
            if is_ensures {
                let header = extract_ensures(ctxt, args[0])?;
                let expr = spanned_new(args[0].span, ExprX::Header(header));
                return Ok(expr);
            }

            let vir_args = vec_map_result(&args, |arg| expr_to_vir(ctxt, arg))?;

            if is_requires {
                let header = Rc::new(HeaderExprX::Requires(Rc::new(vir_args)));
                Ok(spanned_new(expr.span, ExprX::Header(header)))
            } else if is_assume || is_assert {
                unsupported_unless!(args.len() == 1, "expected assume/assert", args, expr.span);
                let arg = vir_args[0].clone();
                if is_assume {
                    Ok(spanned_new(expr.span, ExprX::Assume(arg)))
                } else {
                    Ok(spanned_new(expr.span, ExprX::Assert(arg)))
                }
            } else if is_hide || is_reveal {
                unsupported_unless!(args.len() == 1, "expected hide/reveal", args, expr.span);
                let arg = vir_args[0].clone();
                if let ExprX::Var(x) = &arg.x {
                    if is_hide {
                        let header = Rc::new(HeaderExprX::Hide(x.clone()));
                        Ok(spanned_new(expr.span, ExprX::Header(header)))
                    } else {
                        Ok(spanned_new(expr.span, ExprX::Fuel(x.clone(), 1)))
                    }
                } else {
                    Err(spanned_new(expr.span, "hide/reveal: expected identifier".to_string()))
                }
            } else if is_cmp || is_arith_binary || is_implies {
                unsupported_unless!(args.len() == 2, "expected binary op", args, expr.span);
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
                let ty = tc.node_type(expr.hir_id);
                if is_arith_binary { Ok(mk_ty_clip(ty, &e)) } else { Ok(e) }
            } else {
                let name = hack_get_def_name(tcx, f); // TODO: proper handling of paths
                Ok(spanned_new(expr.span, ExprX::Call(Rc::new(name), Rc::new(vir_args))))
            }
        }
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Bool(b) => {
                let c = air::ast::Constant::Bool(b);
                Ok(spanned_new(expr.span, ExprX::Const(c)))
            }
            rustc_ast::LitKind::Int(i, _) => {
                let typ = typ_of_node(ctxt, &expr.hir_id);
                let c = air::ast::Constant::Nat(Rc::new(i.to_string()));
                if let Typ::Int(range) = typ {
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
                    dbg!(expr);
                    dbg!(expr.span);
                    unsupported!("unary expression")
                }
            };
            Ok(spanned_new(expr.span, ExprX::Unary(vop, varg)))
        }
        ExprKind::Binary(op, lhs, rhs) => {
            let vlhs = expr_to_vir(ctxt, lhs)?;
            let vrhs = expr_to_vir(ctxt, rhs)?;
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
                _ => unsupported!(format!("binary operator {:?} {:?}", op, expr.span)),
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
                node => unsupported!(format!("Path {:?} {:?}", node, expr.span)),
            },
            Res::Def(_, id) => {
                let name = hack_get_def_name(tcx, id); // TODO: proper handling of paths
                Ok(spanned_new(expr.span, ExprX::Var(Rc::new(name))))
            }
            res => unsupported!(format!("Path {:?} {:?}", res, expr.span)),
        },
        ExprKind::Assign(lhs, rhs, _) => Ok(spanned_new(
            expr.span,
            ExprX::Assign(expr_to_vir(ctxt, lhs)?, expr_to_vir(ctxt, rhs)?),
        )),
        ExprKind::Field(lhs, name) => {
            let vir_lhs = expr_to_vir(ctxt, lhs)?;
            let lhs_ty = tc.node_type(lhs.hir_id);
            let (datatype_name, field_name) = if let Some(adt_def) = lhs_ty.ty_adt_def() {
                unsupported_unless!(
                    adt_def.variants.len() == 1,
                    "field_of_adt_with_multiple_variants",
                    expr,
                    expr.span
                );
                (Rc::new(hack_get_def_name(tcx, adt_def.did)), str_ident(&name.as_str()))
            } else {
                unsupported!("field_of_non_adt", expr, expr.span);
            };
            Ok(spanned_new(expr.span, ExprX::Field { lhs: vir_lhs, datatype_name, field_name }))
        }
        _ => {
            dbg!(expr);
            dbg!(expr.span);
            unsupported!("expression")
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
    unsupported_unless!(default_binding_modes, "default_binding_modes");
    match pattern.kind {
        PatKind::Binding(annotation, _id, ident, pat) => {
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
            dbg!(pattern, pattern.span);
            unsupported!("let_pattern")
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
            dbg!(stmt);
            dbg!(stmt.span);
            unsupported!("statement")
        }
    }
}
