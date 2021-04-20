use crate::util::slice_vec_map;
use crate::{unsupported, unsupported_unless};
use rustc_ast::{AttrKind, Attribute};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{BindingAnnotation, Node, Pat, PatKind, PrimTy, QPath, Ty};
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::{BinOp, BorrowKind, UnOp};
use rustc_middle::ty::{ConstKind, TyCtxt, TyKind};
use rustc_mir_build::thir::{Expr, ExprKind, LogicalOp, Stmt, StmtKind};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{BinaryOp, ExprX, Mode, ParamX, StmtX, Typ, UnaryOp};
use vir::def::Spanned;

pub(crate) fn spanned_new<X>(span: Span, x: X) -> Rc<Spanned<X>> {
    let raw_span = Rc::new(span);
    let as_string = format!("{:?}", span);
    Spanned::new(air::ast::Span { raw_span, as_string }, x)
}

// TODO: proper handling of def_ids
pub(crate) fn hack_get_def_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    let debug_name = tcx.def_path_debug_str(def_id);
    let last_colon = debug_name.rfind(':').unwrap();
    debug_name[last_colon + 1..].to_string()
}

// TODO: proper handling of def_ids
pub(crate) fn hack_check_def_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    krate: &str,
    path: &str,
) -> bool {
    let debug_name = tcx.def_path_debug_str(def_id);
    let krate_prefix = format!("{}[", krate);
    let path_suffix = format!("]::{}", path);
    debug_name.starts_with(&krate_prefix) && debug_name.ends_with(&path_suffix)
}

pub(crate) fn ident_to_var<'tcx>(ident: &Ident) -> String {
    ident.to_string()
}

pub(crate) fn get_mode(attrs: &[Attribute]) -> Mode {
    let mut mode = Mode::Exec;
    for attr in attrs {
        match &attr.kind {
            AttrKind::Normal(item, _) => match &item.path.segments[..] {
                [segment] => match ident_to_var(&segment.ident).as_str() {
                    "spec" => mode = Mode::Spec,
                    "proof" => mode = Mode::Proof,
                    "exec" => mode = Mode::Exec,
                    _ => {}
                },
                _ => {}
            },
            _ => {}
        }
    }
    mode
}

pub(crate) fn get_fuel(attrs: &[Attribute]) -> u32 {
    let mut fuel: u32 = 1;
    for attr in attrs {
        match &attr.kind {
            AttrKind::Normal(item, _) => match &item.path.segments[..] {
                [segment] => match ident_to_var(&segment.ident).as_str() {
                    "opaque" => fuel = 0,
                    _ => {}
                },
                _ => {}
            },
            _ => {}
        }
    }
    fuel
}

pub(crate) fn ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> Typ {
    let Ty { hir_id: _, kind, span } = ty;
    match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::PrimTy(PrimTy::Bool) => Typ::Bool,
            Res::Def(DefKind::Struct, def_id) => {
                if hack_check_def_name(tcx, def_id, "builtin", "int") {
                    Typ::Int
                } else {
                    unsupported!(format!("type {:?} {:?}", kind, span))
                }
            }
            _ => {
                unsupported!(format!("type {:?} {:?}", kind, span))
            }
        },
        _ => {
            unsupported!(format!("type {:?} {:?}", kind, span))
        }
    }
}

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

fn expr_descope<'thir, 'tcx>(expr: &'thir Expr<'thir, 'tcx>) -> &'thir Expr<'thir, 'tcx> {
    match &expr.kind {
        ExprKind::Scope { value, .. } => value,
        _ => expr,
    }
}

fn expr_to_function<'thir, 'tcx>(expr: &'thir Expr<'thir, 'tcx>) -> DefId {
    let v = match &expr_descope(expr).kind {
        ExprKind::Literal { literal, .. } => match literal.ty.kind() {
            // TODO: proper handling of functions
            TyKind::FnDef(id, _) => Some(*id),
            _ => None,
        },
        _ => None,
    };
    match v {
        Some(def_id) => def_id,
        None => unsupported!(format!("complex function call {:?} {:?}", expr, expr.span)),
    }
}

pub(crate) fn expr_to_vir<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'thir Expr<'thir, 'tcx>,
) -> vir::ast::Expr {
    match &expr.kind {
        ExprKind::Scope { value, .. } => expr_to_vir(tcx, value),
        ExprKind::Block { body, .. } => {
            let vir_stmts =
                body.stmts.iter().flat_map(|stmt| stmt_to_vir(tcx, stmt)).collect::<Vec<_>>();
            let vir_expr = body.expr.map(|expr| expr_to_vir(tcx, &expr));
            spanned_new(expr.span, ExprX::Block(Rc::new(vir_stmts), vir_expr))
        }
        ExprKind::Borrow { arg, borrow_kind } => {
            match borrow_kind {
                BorrowKind::Shared => {}
                _ => {
                    unsupported!("borrow_kind", borrow_kind, expr.span);
                }
            }
            expr_to_vir(tcx, arg)
        }
        ExprKind::Call { fun, args, .. } => {
            let f = expr_to_function(fun);
            let is_assume = hack_check_def_name(tcx, f, "builtin", "assume");
            let is_assert = hack_check_def_name(tcx, f, "builtin", "assert");
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
            let vir_args = slice_vec_map(args, |arg| expr_to_vir(tcx, arg));
            if is_assume || is_assert {
                unsupported_unless!(args.len() == 1, "expected assume/assert", args, expr.span);
                let arg = vir_args[0].clone();
                if is_assume {
                    spanned_new(expr.span, ExprX::Assume(arg))
                } else {
                    spanned_new(expr.span, ExprX::Assert(arg))
                }
            } else if is_hide || is_reveal {
                unsupported_unless!(args.len() == 1, "expected hide/reveal", args, expr.span);
                let arg = vir_args[0].clone();
                if let ExprX::Var(x) = &arg.x {
                    let fuel = if is_hide { 0 } else { 1 };
                    spanned_new(expr.span, ExprX::Fuel(x.clone(), fuel))
                } else {
                    // TODO: this should be a VirErr, not a panic
                    panic!("hide/reveal: expected identifier at location {:?}", expr.span)
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
                spanned_new(expr.span, ExprX::Binary(vop, lhs, rhs))
            } else {
                let name = hack_get_def_name(tcx, f); // TODO: proper handling of paths
                spanned_new(expr.span, ExprX::Call(Rc::new(name), Rc::new(vir_args)))
            }
        }
        ExprKind::Literal { literal, user_ty: _, const_id: _ } => {
            unsupported_unless!(
                literal.ty.flags().is_empty(),
                "literal.ty.flags",
                literal,
                expr.span
            );
            match (literal.ty.kind(), literal.val) {
                (TyKind::Bool, ConstKind::Value(ConstValue::Scalar(Scalar::Int(v)))) => {
                    let b = v.assert_bits(v.size()) != 0;
                    let c = air::ast::Constant::Bool(b);
                    spanned_new(expr.span, ExprX::Const(c))
                }
                /*
                (TyKind::Uint(_), ConstKind::Value(ConstValue::Scalar(Scalar::Int(v)))) => {
                    let i = v.assert_bits(v.size());
                }
                */
                _ => {
                    let f = expr_to_function(expr);
                    let name = hack_get_def_name(tcx, f); // TODO: proper handling of paths
                    spanned_new(expr.span, ExprX::Var(Rc::new(name)))
                }
            }
        }
        ExprKind::Unary { op, arg } => {
            let varg = expr_to_vir(tcx, arg);
            let vop = match op {
                UnOp::Not => UnaryOp::Not,
                _ => {
                    dbg!(expr);
                    dbg!(expr.span);
                    unsupported!("unary expression")
                }
            };
            spanned_new(expr.span, ExprX::Unary(vop, varg))
        }
        ExprKind::LogicalOp { op, lhs, rhs } => {
            let vlhs = expr_to_vir(tcx, lhs);
            let vrhs = expr_to_vir(tcx, rhs);
            let vop = match op {
                LogicalOp::And => BinaryOp::And,
                LogicalOp::Or => BinaryOp::Or,
            };
            spanned_new(expr.span, ExprX::Binary(vop, vlhs, vrhs))
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let vlhs = expr_to_vir(tcx, lhs);
            let vrhs = expr_to_vir(tcx, rhs);
            let vop = match op {
                BinOp::Eq => BinaryOp::Eq,
                BinOp::Ne => BinaryOp::Ne,
                BinOp::Le => BinaryOp::Le,
                BinOp::Ge => BinaryOp::Ge,
                BinOp::Lt => BinaryOp::Lt,
                BinOp::Gt => BinaryOp::Gt,
                BinOp::Add => BinaryOp::Add,
                BinOp::Sub => BinaryOp::Sub,
                BinOp::Mul => BinaryOp::Mul,
                _ => unsupported!(format!("binary operator {:?} {:?}", op, expr.span)),
            };
            spanned_new(expr.span, ExprX::Binary(vop, vlhs, vrhs))
        }
        ExprKind::VarRef { id } => match tcx.hir().get(*id) {
            Node::Binding(pat) => spanned_new(expr.span, ExprX::Var(Rc::new(pat_to_var(pat)))),
            node => {
                unsupported!(format!("VarRef {:?}", node))
            }
        },
        ExprKind::Assign { lhs, rhs } => {
            spanned_new(expr.span, ExprX::Assign(expr_to_vir(tcx, lhs), expr_to_vir(tcx, rhs)))
        }
        _ => {
            dbg!(expr);
            dbg!(expr.span);
            unsupported!("expression")
        }
    }
}

pub(crate) fn let_stmt_to_vir<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    pattern: &'thir rustc_mir_build::thir::Pat<'thir>,
    initializer: &'thir Option<&'thir Expr<'thir, 'tcx>>,
) -> Vec<vir::ast::Stmt> {
    // dbg!(pattern);
    use std::ops::Deref;
    let (decl, var) = match pattern.kind.deref() {
        rustc_mir_build::thir::PatKind::Binding { var, mutability, mode, ty, .. } => {
            unsupported_unless!(
                *mode == rustc_mir_build::thir::BindingMode::ByValue,
                "by_ref_bindings"
            );
            // TODO: need unique identifiers!
            let name = Rc::new(match tcx.hir().get(*var) {
                Node::Binding(pat) => pat_to_var(pat),
                node => {
                    unsupported!(format!("VarRef {:?}", node))
                }
            });
            // TODO: what's the relationship of this with ty_to_vir
            let typ = match ty.kind() {
                rustc_middle::ty::TyKind::Bool => Typ::Bool,
                rustc_middle::ty::TyKind::Adt(adt, params)
                    if params.len() == 0 && hack_check_def_name(tcx, adt.did, "builtin", "int") =>
                {
                    Typ::Int
                }
                _ => {
                    unsupported!(format!("type {:?}", ty.kind()))
                }
            };
            (
                spanned_new(
                    pattern.span,
                    StmtX::Decl {
                        param: ParamX { name: name.clone(), typ },
                        mutable: match *mutability {
                            rustc_middle::mir::Mutability::Not => false,
                            rustc_middle::mir::Mutability::Mut => true,
                        },
                    },
                ),
                spanned_new(pattern.span, ExprX::Var(name)),
            )
        }
        _ => {
            unsupported!("let_pattern", pattern, pattern.span);
        }
    };

    let mut vir_stmts = vec![decl];

    if let Some(initializer) = initializer {
        let rhs = expr_to_vir(tcx, initializer);
        let expr = spanned_new(initializer.span, ExprX::Binary(BinaryOp::Eq, var, rhs));
        let assume = spanned_new(initializer.span, ExprX::Assume(expr));
        vir_stmts.push(spanned_new(initializer.span, StmtX::Expr(assume)));
    }

    vir_stmts
}

pub(crate) fn stmt_to_vir<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    stmt: &'thir Stmt<'thir, 'tcx>,
) -> Vec<vir::ast::Stmt> {
    match &stmt.kind {
        StmtKind::Expr { expr, .. } => {
            let vir_expr = expr_to_vir(tcx, expr);
            vec![spanned_new(expr.span, StmtX::Expr(vir_expr))]
        }
        StmtKind::Let { pattern, initializer, .. } => let_stmt_to_vir(tcx, pattern, initializer),
    }
}
