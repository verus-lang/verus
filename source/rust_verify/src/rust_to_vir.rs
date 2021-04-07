/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::util::box_slice_map;
use crate::{unsupported, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    BindingAnnotation, Body, BodyId, Crate, FnDecl, FnHeader, FnSig, Generics, HirId, Item, ItemId,
    ItemKind, ModuleItems, Node, Param, Pat, PatKind, PrimTy, QPath, Ty, Unsafety,
};
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::{BinOp, BorrowKind, UnOp};
use rustc_middle::ty::{ConstKind, TyCtxt, TyKind};
use rustc_mir_build::thir;
use rustc_mir_build::thir::{Expr, ExprKind, LogicalOp, Stmt, StmtKind};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{BinaryOp, ExprX, Function, FunctionX, ParamX, StmtX, Typ, UnaryOp};
use vir::def::Spanned;

fn spanned_new<X>(span: Span, x: X) -> Rc<Spanned<X>> {
    let raw_span = Rc::new(span);
    let as_string = format!("{:?}", span);
    Spanned::new(air::ast::Span { raw_span, as_string }, x)
}

// TODO: proper handling of def_ids
fn hack_check_def_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, krate: &str, path: &str) -> bool {
    let debug_name = tcx.def_path_debug_str(def_id);
    let krate_prefix = format!("{}[", krate);
    let path_suffix = format!("]::{}", path);
    debug_name.starts_with(&krate_prefix) && debug_name.ends_with(&path_suffix)
}

fn pat_to_var<'tcx>(pat: &Pat) -> String {
    let Pat { hir_id: _, kind, span: _, default_binding_modes } = pat;
    unsupported_unless!(default_binding_modes, "default_binding_modes");
    match kind {
        PatKind::Binding(annotation, _id, ident, pat) => {
            match annotation {
                BindingAnnotation::Unannotated => {}
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
            ident.to_string()
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

fn expr_to_vir<'thir, 'tcx>(tcx: TyCtxt<'tcx>, expr: &'thir Expr<'thir, 'tcx>) -> vir::ast::Expr {
    match &expr.kind {
        ExprKind::Scope { value, .. } => expr_to_vir(tcx, value),
        ExprKind::Block { body, .. } => {
            let vir_stmts = box_slice_map(body.stmts, |stmt| stmt_to_vir(tcx, stmt));
            spanned_new(expr.span, ExprX::Block(Rc::new(vir_stmts)))
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
            let is_eq = hack_check_def_name(tcx, f, "core", "cmp::PartialEq::eq");
            let is_ne = hack_check_def_name(tcx, f, "core", "cmp::PartialEq::ne");
            let is_le = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::le");
            let is_ge = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::ge");
            let is_lt = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::lt");
            let is_gt = hack_check_def_name(tcx, f, "core", "cmp::PartialOrd::gt");
            let is_add = hack_check_def_name(tcx, f, "core", "ops::arith::Add::add");
            let is_sub = hack_check_def_name(tcx, f, "core", "ops::arith::Sub::sub");
            let is_mul = hack_check_def_name(tcx, f, "core", "ops::arith::Mul::mul");
            let is_binary =
                is_eq || is_ne || is_le || is_ge || is_lt || is_gt || is_add || is_sub || is_mul;
            let vir_args = box_slice_map(args, |arg| expr_to_vir(tcx, arg));
            if is_assume || is_assert {
                unsupported_unless!(args.len() == 1, "expected assume/assert", args, expr.span);
                let arg = vir_args[0].clone();
                if is_assume {
                    spanned_new(expr.span, ExprX::Assume(arg))
                } else {
                    spanned_new(expr.span, ExprX::Assert(arg))
                }
            } else if is_binary {
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
                } else {
                    panic!("internal error")
                };
                spanned_new(expr.span, ExprX::Binary(vop, lhs, rhs))
            } else {
                unsupported!(format!(
                    "unsupported function {:?} {:?}",
                    tcx.def_path_debug_str(f),
                    expr.span
                ))
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
                    let c = air::ast::Const::Bool(b);
                    spanned_new(expr.span, ExprX::Const(c))
                }
                /*
                (TyKind::Uint(_), ConstKind::Value(ConstValue::Scalar(Scalar::Int(v)))) => {
                    let i = v.assert_bits(v.size());
                }
                */
                _ => {
                    dbg!(literal);
                    dbg!(expr.span);
                    unsupported!("literal")
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
        _ => {
            dbg!(expr);
            dbg!(expr.span);
            unsupported!("expression")
        }
    }
}

fn stmt_to_vir<'thir, 'tcx>(tcx: TyCtxt<'tcx>, stmt: &'thir Stmt<'thir, 'tcx>) -> vir::ast::Stmt {
    match &stmt.kind {
        StmtKind::Expr { expr, .. } => {
            let vir_expr = expr_to_vir(tcx, expr);
            spanned_new(expr.span, StmtX::Expr(vir_expr))
        }
        _ => {
            dbg!(stmt);
            unsupported!("statement")
        }
    }
}

fn body_to_vir<'tcx>(tcx: TyCtxt<'tcx>, id: &BodyId, body: &'tcx Body<'tcx>) -> vir::ast::Expr {
    let did = id.hir_id.owner;
    let arena = thir::Arena::default();
    let expr = thir::build_thir(
        tcx,
        rustc_middle::ty::WithOptConstParam::unknown(did),
        &arena,
        &body.value,
    );
    let vir_expr = expr_to_vir(tcx, expr);
    vir_expr
}

fn ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> Typ {
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

fn check_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &'tcx Crate<'tcx>,
    vir: &mut Vec<Function>,
    _id: &ItemId,
    item: &'tcx Item<'tcx>,
) {
    match &item.kind {
        ItemKind::Fn(sig, generics, body_id) => {
            match sig {
                FnSig {
                    header: FnHeader { unsafety, constness: _, asyncness: _, abi: _ },
                    decl: FnDecl { inputs: _, output, c_variadic, implicit_self },
                    span: _,
                } => {
                    unsupported_unless!(*unsafety == Unsafety::Normal, "unsafe");
                    match output {
                        rustc_hir::FnRetTy::DefaultReturn(_) => {}
                        _ => unsupported!("function return values"),
                    }
                    unsupported_unless!(!c_variadic, "c_variadic");
                    match implicit_self {
                        rustc_hir::ImplicitSelfKind::None => {}
                        _ => unsupported!("implicit_self"),
                    }
                }
            }
            match generics {
                Generics { params, where_clause, span: _ } => {
                    unsupported_unless!(params.len() == 0, "generics");
                    unsupported_unless!(where_clause.predicates.len() == 0, "where clause");
                }
            }
            let body = &krate.bodies[body_id];
            let Body { params, value: _, generator_kind } = body;
            let mut vir_params: Vec<vir::ast::Param> = Vec::new();
            for (param, input) in params.iter().zip(sig.decl.inputs.iter()) {
                let Param { hir_id: _, pat, ty_span: _, span } = param;
                let name = Rc::new(pat_to_var(pat));
                let typ = ty_to_vir(tcx, input);
                let vir_param = spanned_new(*span, ParamX { name, typ });
                vir_params.push(vir_param);
            }
            match generator_kind {
                None => {}
                _ => {
                    unsupported!("generator_kind", generator_kind);
                }
            }
            let vir_body = body_to_vir(tcx, body_id, body);
            let name = Rc::new(item.ident.to_string());
            let params = Rc::new(vir_params.into_boxed_slice());
            let function = spanned_new(sig.span, FunctionX { name, params, body: vir_body });
            vir.push(function);
        }
        ItemKind::Use { .. } => {}
        ItemKind::ExternCrate { .. } => {}
        ItemKind::Mod { .. } => {}
        _ => {
            unsupported!("unsupported item", item);
        }
    }
}

fn check_module<'tcx>(_tcx: TyCtxt<'tcx>, _id: &LocalDefId, module_items: &'tcx ModuleItems) {
    match module_items {
        ModuleItems { items, trait_items, impl_items, foreign_items } => {
            for _id in items {
                // TODO
            }
            unsupported_unless!(trait_items.len() == 0, "trait definitions", trait_items);
            unsupported_unless!(impl_items.len() == 0, "impl definitions", impl_items);
            unsupported_unless!(foreign_items.len() == 0, "foreign items", foreign_items);
        }
    }
}

fn check_attr<'tcx>(_tcx: TyCtxt<'tcx>, _id: &HirId, _attr: &'tcx [Attribute]) {
    // TODO
}

pub fn crate_to_vir<'tcx>(tcx: TyCtxt<'tcx>, krate: &'tcx Crate<'tcx>) -> Vec<Function> {
    let Crate {
        item: _,
        exported_macros,
        non_exported_macro_attrs,
        items,
        trait_items,
        impl_items,
        foreign_items,
        bodies: _,
        trait_impls,
        body_ids: _,
        modules,
        proc_macros,
        trait_map,
        attrs,
    } = krate;
    let mut vir: Vec<Function> = Vec::new();
    unsupported_unless!(
        exported_macros.len() == 0,
        "exported macros from a crate",
        exported_macros
    );
    unsupported_unless!(
        non_exported_macro_attrs.len() == 0,
        "non-exported macro attributes",
        non_exported_macro_attrs
    );
    for (id, item) in items {
        check_item(tcx, krate, &mut vir, id, item);
    }
    unsupported_unless!(trait_items.len() == 0, "trait definitions", trait_items);
    unsupported_unless!(impl_items.len() == 0, "impl definitions", impl_items);
    unsupported_unless!(foreign_items.len() == 0, "foreign items", foreign_items);
    unsupported_unless!(trait_impls.len() == 0, "trait implementations", trait_impls);
    for (id, module) in modules {
        check_module(tcx, id, module);
    }
    unsupported_unless!(proc_macros.len() == 0, "procedural macros", proc_macros);
    unsupported_unless!(trait_map.len() == 0, "traits", trait_map);
    for (id, attr) in attrs {
        check_attr(tcx, id, attr);
    }
    vir
}
