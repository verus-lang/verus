use crate::util::{slice_vec_map_result, vec_map_result};
use crate::{unsupported, unsupported_unless};
use rustc_ast::{AttrKind, Attribute, IntTy, UintTy};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{BindingAnnotation, BodyId, Node, Pat, PatKind, PrimTy, QPath, Ty};
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::{BinOp, BorrowKind, UnOp};
use rustc_middle::ty::{AdtDef, ConstKind, TyCtxt, TyKind};
use rustc_mir_build::thir::{build_thir, Arena, Expr, ExprKind, LogicalOp, Stmt, StmtKind};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{
    BinaryOp, ExprX, HeaderExpr, HeaderExprX, IntRange, Mode, ParamX, StmtX, Stmts, Typ, UnaryOp,
    VirErr,
};
use vir::ast_util::str_ident;
use vir::def::Spanned;

pub(crate) fn spanned_new<X>(span: Span, x: X) -> Rc<Spanned<X>> {
    let raw_span = Rc::new(span);
    let as_string = format!("{:?}", span);
    Spanned::new(air::ast::Span { description: None, raw_span, as_string }, x)
}

pub(crate) fn path_to_ty_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Typ {
    let ds =
        tcx.def_path(def_id).data.iter().map(|d| Rc::new(format!("{}", d))).collect::<Vec<_>>();
    Typ::Path(ds)
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

pub(crate) fn build_thir_body<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    arena: &'thir Arena<'thir, 'tcx>,
    body_id: &BodyId,
) -> &'thir Expr<'thir, 'tcx> {
    let body = tcx.hir().body(*body_id);
    let did = body_id.hir_id.owner;
    build_thir(tcx, rustc_middle::ty::WithOptConstParam::unknown(did), arena, &body.value)
}

fn mk_range<'tcx>(ty: rustc_middle::ty::Ty<'tcx>) -> IntRange {
    match ty.kind() {
        TyKind::Adt(_, _) if ty.to_string() == crate::typecheck::BUILTIN_INT => IntRange::Int,
        TyKind::Adt(_, _) if ty.to_string() == crate::typecheck::BUILTIN_NAT => IntRange::Nat,
        TyKind::Uint(rustc_middle::ty::UintTy::U8) => IntRange::U(8),
        TyKind::Uint(rustc_middle::ty::UintTy::U16) => IntRange::U(16),
        TyKind::Uint(rustc_middle::ty::UintTy::U32) => IntRange::U(32),
        TyKind::Uint(rustc_middle::ty::UintTy::U64) => IntRange::U(64),
        TyKind::Uint(rustc_middle::ty::UintTy::U128) => IntRange::U(128),
        TyKind::Uint(rustc_middle::ty::UintTy::Usize) => IntRange::USize,
        TyKind::Int(rustc_middle::ty::IntTy::I8) => IntRange::I(8),
        TyKind::Int(rustc_middle::ty::IntTy::I16) => IntRange::I(16),
        TyKind::Int(rustc_middle::ty::IntTy::I32) => IntRange::I(32),
        TyKind::Int(rustc_middle::ty::IntTy::I64) => IntRange::I(64),
        TyKind::Int(rustc_middle::ty::IntTy::I128) => IntRange::I(128),
        TyKind::Int(rustc_middle::ty::IntTy::Isize) => IntRange::ISize,
        _ => panic!("mk_range {:?}", ty),
    }
}

pub(crate) fn mid_ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty) -> Typ {
    unsupported_unless!(ty.flags().is_empty(), "ty.flags", ty);
    match ty.kind() {
        TyKind::Bool => Typ::Bool,
        TyKind::Adt(AdtDef { did, .. }, _) => {
            let s = ty.to_string();
            if s == crate::typecheck::BUILTIN_INT {
                Typ::Int(IntRange::Int)
            } else if s == crate::typecheck::BUILTIN_NAT {
                Typ::Int(IntRange::Nat)
            } else {
                path_to_ty_path(tcx, *did)
            }
        }
        TyKind::Uint(_) | TyKind::Int(_) => Typ::Int(mk_range(ty)),
        _ => {
            unsupported!(format!("type {:?}", ty))
        }
    }
}

pub(crate) fn ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> Typ {
    let Ty { hir_id: _, kind, span } = ty;
    match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::PrimTy(PrimTy::Bool) => Typ::Bool,
            Res::PrimTy(PrimTy::Uint(UintTy::U8)) => Typ::Int(IntRange::U(8)),
            Res::PrimTy(PrimTy::Uint(UintTy::U16)) => Typ::Int(IntRange::U(16)),
            Res::PrimTy(PrimTy::Uint(UintTy::U32)) => Typ::Int(IntRange::U(32)),
            Res::PrimTy(PrimTy::Uint(UintTy::U64)) => Typ::Int(IntRange::U(64)),
            Res::PrimTy(PrimTy::Uint(UintTy::U128)) => Typ::Int(IntRange::U(128)),
            Res::PrimTy(PrimTy::Uint(UintTy::Usize)) => Typ::Int(IntRange::USize),
            Res::PrimTy(PrimTy::Int(IntTy::I8)) => Typ::Int(IntRange::I(8)),
            Res::PrimTy(PrimTy::Int(IntTy::I16)) => Typ::Int(IntRange::I(16)),
            Res::PrimTy(PrimTy::Int(IntTy::I32)) => Typ::Int(IntRange::I(32)),
            Res::PrimTy(PrimTy::Int(IntTy::I64)) => Typ::Int(IntRange::I(64)),
            Res::PrimTy(PrimTy::Int(IntTy::I128)) => Typ::Int(IntRange::I(128)),
            Res::PrimTy(PrimTy::Int(IntTy::Isize)) => Typ::Int(IntRange::ISize),
            Res::Def(DefKind::Struct, def_id) => {
                if hack_check_def_name(tcx, def_id, "builtin", "int") {
                    Typ::Int(IntRange::Int)
                } else if hack_check_def_name(tcx, def_id, "builtin", "nat") {
                    Typ::Int(IntRange::Nat)
                } else {
                    path_to_ty_path(tcx, def_id)
                }
            }
            Res::Def(DefKind::Enum, def_id) => path_to_ty_path(tcx, def_id),
            _ => {
                unsupported!(format!("type {:?} {:?} {:?}", kind, path.res, span))
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

fn extract_array<'thir, 'tcx>(expr: &'thir Expr<'thir, 'tcx>) -> Vec<&'thir Expr<'thir, 'tcx>> {
    match &expr.kind {
        ExprKind::Scope { value, .. } => extract_array(value),
        ExprKind::Array { fields, .. } => fields.iter().collect(),
        _ => vec![expr],
    }
}

fn get_ensures_arg<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'thir Expr<'thir, 'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    if matches!(expr.ty.kind(), TyKind::Bool) {
        expr_to_vir(tcx, expr)
    } else {
        Err(spanned_new(expr.span, "ensures needs a bool expression".to_string()))
    }
}

fn extract_ensures<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'thir Expr<'thir, 'tcx>,
) -> Result<HeaderExpr, VirErr> {
    match &expr.kind {
        ExprKind::Scope { value, .. } => extract_ensures(tcx, value),
        ExprKind::Closure { closure_id, .. } => match tcx.hir().get_if_local(*closure_id) {
            Some(Node::Expr(expr)) => match expr.kind {
                rustc_hir::ExprKind::Closure(_, fn_decl, body_id, _, _) => {
                    let typs: Vec<Typ> = fn_decl.inputs.iter().map(|t| ty_to_vir(tcx, t)).collect();
                    let body = tcx.hir().body(body_id);
                    let xs: Vec<String> =
                        body.params.iter().map(|param| pat_to_var(param.pat)).collect();
                    let arena = Arena::default();
                    let expr = build_thir_body(tcx, &arena, &body_id);
                    let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(tcx, e))?;
                    if typs.len() == 1 && xs.len() == 1 {
                        let id_typ = Some((Rc::new(xs[0].clone()), typs[0].clone()));
                        Ok(Rc::new(HeaderExprX::Ensures(id_typ, Rc::new(args))))
                    } else {
                        Err(spanned_new(expr.span, "expected 1 parameter in closure".to_string()))
                    }
                }
                _ => panic!("internal error: expected closure"),
            },
            _ => panic!("internal error: expected closure"),
        },
        _ => {
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(tcx, e))?;
            Ok(Rc::new(HeaderExprX::Ensures(None, Rc::new(args))))
        }
    }
}

fn mk_clip<'tcx>(ty: rustc_middle::ty::Ty<'tcx>, expr: &vir::ast::Expr) -> vir::ast::Expr {
    match mk_range(ty) {
        IntRange::Int => expr.clone(),
        range => Spanned::new(expr.span.clone(), ExprX::Unary(UnaryOp::Clip(range), expr.clone())),
    }
}

pub(crate) fn expr_to_vir<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'thir Expr<'thir, 'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    match &expr.kind {
        ExprKind::Scope { value, .. } => expr_to_vir(tcx, value),
        ExprKind::Block { body, .. } => {
            let vir_stmts: Stmts = Rc::new(
                slice_vec_map_result(body.stmts, |stmt| stmt_to_vir(tcx, stmt))?
                    .into_iter()
                    .flatten()
                    .collect(),
            );
            let vir_expr = body.expr.map(|expr| expr_to_vir(tcx, &expr)).transpose()?;
            Ok(spanned_new(expr.span, ExprX::Block(vir_stmts, vir_expr)))
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
        ExprKind::Call { fun, args: args_slice, .. } => {
            let mut args: Vec<&'thir Expr<'thir, 'tcx>> = args_slice.iter().collect();
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
                    if !matches!(arg.ty.kind(), TyKind::Bool) {
                        let s = "requires needs a bool expression".to_string();
                        return Err(spanned_new(arg.span, s));
                    }
                }
            }
            if is_ensures {
                let header = extract_ensures(tcx, args[0])?;
                let expr = spanned_new(args[0].span, ExprX::Header(header));
                return Ok(expr);
            }

            let vir_args = vec_map_result(&args, |arg| expr_to_vir(tcx, arg))?;

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
                if is_arith_binary { Ok(mk_clip(expr.ty, &e)) } else { Ok(e) }
            } else {
                let name = hack_get_def_name(tcx, f); // TODO: proper handling of paths
                Ok(spanned_new(expr.span, ExprX::Call(Rc::new(name), Rc::new(vir_args))))
            }
        }
        ExprKind::Literal { literal, user_ty: _, const_id: _ } => {
            match literal.ty.kind() {
                TyKind::FnDef(_, _) => {
                    let f = expr_to_function(expr);
                    let name = hack_get_def_name(tcx, f); // TODO: proper handling of paths
                    return Ok(spanned_new(expr.span, ExprX::Var(Rc::new(name))));
                }
                _ => {}
            }
            let typ = mid_ty_to_vir(tcx, literal.ty);
            match (&typ, literal.val) {
                (Typ::Bool, ConstKind::Value(ConstValue::Scalar(Scalar::Int(v)))) => {
                    let b = v.assert_bits(v.size()) != 0;
                    let c = air::ast::Constant::Bool(b);
                    Ok(spanned_new(expr.span, ExprX::Const(c)))
                }
                (Typ::Int(range), ConstKind::Value(ConstValue::Scalar(Scalar::Int(v)))) => {
                    let v = v.assert_bits(v.size()).to_string();
                    let c = air::ast::Constant::Nat(Rc::new(v));
                    match range {
                        IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::USize => {
                            Ok(spanned_new(expr.span, ExprX::Const(c)))
                        }
                        IntRange::I(_) | IntRange::ISize => {
                            Ok(mk_clip(literal.ty, &spanned_new(expr.span, ExprX::Const(c))))
                        }
                    }
                }
                _ => {
                    panic!("unexpected constant: {:?} {:?}", literal, typ)
                }
            }
        }
        ExprKind::Cast { source } => Ok(mk_clip(expr.ty, &expr_to_vir(tcx, source)?)),
        ExprKind::Unary { op, arg } => {
            let varg = expr_to_vir(tcx, arg)?;
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
        ExprKind::LogicalOp { op, lhs, rhs } => {
            let vlhs = expr_to_vir(tcx, lhs)?;
            let vrhs = expr_to_vir(tcx, rhs)?;
            let vop = match op {
                LogicalOp::And => BinaryOp::And,
                LogicalOp::Or => BinaryOp::Or,
            };
            Ok(spanned_new(expr.span, ExprX::Binary(vop, vlhs, vrhs)))
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let vlhs = expr_to_vir(tcx, lhs)?;
            let vrhs = expr_to_vir(tcx, rhs)?;
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
            let e = spanned_new(expr.span, ExprX::Binary(vop, vlhs, vrhs));
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => Ok(mk_clip(expr.ty, &e)),
                _ => Ok(e),
            }
        }
        ExprKind::VarRef { id } => match tcx.hir().get(*id) {
            Node::Binding(pat) => Ok(spanned_new(expr.span, ExprX::Var(Rc::new(pat_to_var(pat))))),
            node => {
                unsupported!(format!("VarRef {:?}", node))
            }
        },
        ExprKind::Assign { lhs, rhs } => Ok(spanned_new(
            expr.span,
            ExprX::Assign(expr_to_vir(tcx, lhs)?, expr_to_vir(tcx, rhs)?),
        )),
        ExprKind::Field { lhs, name } => {
            let vir_lhs = expr_to_vir(tcx, lhs)?;
            let field_ident = if let Some(adt_def) = lhs.ty.ty_adt_def() {
                unsupported_unless!(
                    adt_def.variants.len() == 1,
                    "field_of_adt_with_multiple_variants",
                    expr,
                    expr.span
                );
                let variant = adt_def.variants.iter().next().unwrap();
                str_ident(&variant.fields[name.index()].ident.as_str())
            } else {
                unsupported!("field_of_non_adt", expr, expr.span);
            };
            Ok(spanned_new(expr.span, ExprX::Field(vir_lhs, field_ident)))
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
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    // dbg!(pattern);
    use std::ops::Deref;
    match pattern.kind.deref() {
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
            let typ = mid_ty_to_vir(tcx, ty);
            Ok(vec![spanned_new(
                pattern.span,
                StmtX::Decl {
                    param: ParamX { name: name.clone(), typ },
                    mutable: match *mutability {
                        rustc_middle::mir::Mutability::Not => false,
                        rustc_middle::mir::Mutability::Mut => true,
                    },
                    init: initializer.map(|e| expr_to_vir(tcx, e)).transpose()?,
                },
            )])
        }
        _ => {
            dbg!(pattern, pattern.span);
            unsupported!("let_pattern")
        }
    }
}

pub(crate) fn stmt_to_vir<'thir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    stmt: &'thir Stmt<'thir, 'tcx>,
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    match &stmt.kind {
        StmtKind::Expr { expr, .. } => {
            let vir_expr = expr_to_vir(tcx, expr)?;
            Ok(vec![spanned_new(expr.span, StmtX::Expr(vir_expr))])
        }
        StmtKind::Let { pattern, initializer, .. } => let_stmt_to_vir(tcx, pattern, initializer),
    }
}
