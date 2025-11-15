use crate::thir::cx::ThirBuildCx;
use crate::verus::{CallErasure, ExpectSpecArgs, VerusThirBuildCtxt};
use crate::verus::{
    erase_node_unadjusted, erase_tree_kind, handle_call, maybe_erase_node,
    maybe_erase_node_unadjusted, should_erase_var,
};
use rustc_hir::{Arm, Block, Expr, ExprField, ExprKind, Stmt, StmtKind, UnOp};
use rustc_middle::ty::adjustment::{Adjust, Adjustment, AutoBorrow};

impl VerusThirBuildCtxt {
    fn prep_exprs<'tcx>(&mut self, exprs: &'tcx [Expr<'tcx>], expect_spec: bool) {
        for expr in exprs {
            self.prep_expr(expr, expect_spec);
        }
    }

    fn prep_exprs_spec_args<'tcx>(
        &mut self,
        exprs: &'tcx [Expr<'tcx>],
        expect_spec: bool,
        spec_args: &ExpectSpecArgs,
    ) {
        for (i, expr) in exprs.iter().enumerate() {
            self.prep_expr(expr, spec_args.get(i).apply(expect_spec));
        }
    }

    fn prep_block<'tcx>(&mut self, block: &'tcx Block<'tcx>, expect_spec: bool) {
        self.prep_stmts(block.stmts);
        if let Some(expr) = block.expr {
            self.prep_expr(expr, expect_spec);
        }
    }

    fn prep_stmts<'tcx>(&mut self, stmts: &'tcx [Stmt<'tcx>]) {
        for stmt in stmts {
            match stmt.kind {
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                    self.prep_expr(expr, true);
                }
                StmtKind::Item(..) => {}
                StmtKind::Let(local) => {
                    if let Some(els) = local.els {
                        self.prep_block(els, false);
                    }
                    if let Some(init) = local.init {
                        let erase = should_erase_var(self, local.pat.hir_id);
                        self.prep_expr(init, erase);
                    }
                }
            }
        }
    }

    fn field_refs<'tcx>(
        &mut self,
        fields: &'tcx [ExprField<'tcx>],
        expect_spec: bool,
        spec_args: &ExpectSpecArgs,
    ) {
        for (i, field) in fields.iter().enumerate() {
            self.prep_expr(field.expr, spec_args.get(i).apply(expect_spec));
        }
    }

    fn prep_arm<'tcx>(&mut self, arm: &'tcx Arm<'tcx>, expect_spec: bool, discr_spec: bool) {
        if let Some(g) = arm.guard {
            self.prep_expr(g, discr_spec);
        }
        self.prep_expr(arm.body, expect_spec);
    }

    pub(crate) fn prep_expr<'tcx>(&mut self, expr: &'tcx Expr<'tcx>, expect_spec: bool) {
        if self.expr_is_spec.contains_key(&expr.hir_id) {
            assert!(self.expr_is_spec[&expr.hir_id] == expect_spec);
        } else {
            self.expr_is_spec.insert(expr.hir_id, expect_spec);
        }

        match expr.kind {
            ExprKind::MethodCall(_segment, receiver, args, _fn_span) => {
                let call_erasure = handle_call(self, expr);
                match call_erasure {
                    CallErasure::EraseTree => {}
                    CallErasure::Call(_node_erase, spec_args) => {
                        for (i, expr) in std::iter::once(receiver).chain(args.iter()).enumerate() {
                            self.prep_expr(expr, spec_args.get(i).apply(expect_spec));
                        }
                    }
                }
            }
            ExprKind::Call(fun, ref args) => {
                let call_erasure = handle_call(self, expr);
                match call_erasure {
                    CallErasure::EraseTree => {}
                    CallErasure::Call(_node_erase, spec_args) => {
                        self.prep_exprs_spec_args(args, expect_spec, &spec_args);
                        self.prep_expr(fun, false);
                    }
                }
            }
            ExprKind::Use(expr, _span) => {
                self.prep_expr(expr, expect_spec);
            }
            ExprKind::AddrOf(_, _, arg) => {
                self.prep_expr(arg, expect_spec);
            }
            ExprKind::Block(blk, _) => {
                self.prep_block(blk, expect_spec);
            }
            ExprKind::Assign(lhs, rhs, _) => {
                let erase = should_erase_var(self, lhs.hir_id);
                self.prep_expr(lhs, erase);
                self.prep_expr(rhs, erase);
            }
            ExprKind::AssignOp(_op, lhs, rhs) => {
                let erase = should_erase_var(self, lhs.hir_id);
                self.prep_expr(lhs, erase);
                self.prep_expr(rhs, erase);
            }
            ExprKind::Lit(_lit) => {}
            ExprKind::Binary(_op, lhs, rhs) => {
                self.prep_expr(lhs, expect_spec);
                self.prep_expr(rhs, expect_spec);
            }
            ExprKind::Index(lhs, index, _brackets_span) => {
                self.prep_expr(lhs, expect_spec);
                self.prep_expr(index, expect_spec);
            }
            ExprKind::Unary(_op, arg) => {
                self.prep_expr(arg, expect_spec);
            }
            ExprKind::Struct(_qpath, fields, base) => {
                let call_erasure = handle_call(self, expr);
                match call_erasure {
                    CallErasure::EraseTree => {}
                    CallErasure::Call(_node_erase, spec_args) => {
                        use rustc_hir::StructTailExpr;
                        self.field_refs(fields, expect_spec, &spec_args);
                        match base {
                            StructTailExpr::Base(base) => {
                                self.prep_expr(base, spec_args.last().apply(expect_spec));
                            }
                            StructTailExpr::DefaultFields(_) => {}
                            StructTailExpr::None => {}
                        }
                    }
                }
            }
            ExprKind::Closure(_) => {}
            ExprKind::Path(_) => {}
            ExprKind::InlineAsm(_) => {}
            ExprKind::OffsetOf(_, _) => {}
            ExprKind::ConstBlock(_) => {}
            ExprKind::Repeat(v, _) => {
                self.prep_expr(v, expect_spec);
            }
            ExprKind::Ret(v) => {
                if let Some(v) = v {
                    self.prep_expr(v, self.ret_spec());
                }
            }
            ExprKind::Become(call) => {
                self.prep_expr(call, self.ret_spec());
            }
            ExprKind::Break(_dest, value) => {
                if let Some(value) = value {
                    self.prep_expr(value, false);
                }
            }
            ExprKind::Continue(_dest) => {}
            ExprKind::Let(let_expr) => {
                self.prep_expr(let_expr.init, self.var_spec(let_expr.pat.hir_id));
            }
            ExprKind::If(cond, then, else_opt) => {
                self.prep_expr(cond, self.condition_spec(expr));
                self.prep_expr(then, expect_spec);
                if let Some(el) = else_opt {
                    self.prep_expr(el, expect_spec);
                }
            }
            ExprKind::Match(discr, arms, _match_source) => {
                self.prep_expr(discr, self.condition_spec(expr));
                for a in arms {
                    self.prep_arm(a, expect_spec, self.condition_spec(expr));
                }
            }
            ExprKind::Loop(body, ..) => {
                self.prep_block(body, false);
            }
            ExprKind::Field(source, ..) => {
                self.prep_expr(source, expect_spec);
            }
            ExprKind::Cast(source, _cast_ty) => {
                self.prep_expr(source, expect_spec);
            }
            ExprKind::Type(source, _ty) => {
                self.prep_expr(source, expect_spec);
            }
            ExprKind::UnsafeBinderCast(_, source, _ty) => {
                self.prep_expr(source, false);
            }
            ExprKind::DropTemps(source) => {
                self.prep_expr(source, expect_spec);
            }
            ExprKind::Array(fields) => {
                self.prep_exprs(fields, expect_spec);
            }
            ExprKind::Tup(fields) => {
                self.prep_exprs(fields, expect_spec);
            }
            ExprKind::Yield(v, _) => {
                self.prep_expr(v, false);
            }
            ExprKind::Err(_) => unreachable!("cannot lower a `ExprKind::Err` to THIR"),
        }
    }
}

// To avoid edits and conflicts in thir/cx/expr.rs, postprocess some of the work for expr.rs here
pub(crate) fn apply_adjustment_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
    adjustment: &Adjustment<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
    spec: bool,
) -> rustc_middle::thir::ExprKind<'tcx> {
    match adjustment.kind {
        Adjust::Deref(None | Some(_)) | Adjust::Borrow(AutoBorrow::Ref(_)) => {
            // Adjust::Deref(None) -> implicit *
            // Adjust::Borrow(AutoBorrow::Ref(_)) -> implicit &
            // Adjust::Deref(Some(_)) -> This case means inserting a Deref::deref function.
            //   In spec code that would usually be an error, except for some cases
            //   like Arc or Rc where we ignore the deref in spec code.
            //   In all those cases we also want to erase.
            maybe_erase_node(cx, expr, adjustment.target, kind, spec)
        }
        _ => kind,
    }
}

// To avoid edits and conflicts in thir/cx/expr.rs, preprocess some of the work for expr.rs here
pub(crate) fn mirror_expr_pre<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<rustc_middle::thir::ExprKind<'tcx>> {
    match expr.kind {
        ExprKind::MethodCall(..) | ExprKind::Call(..) | ExprKind::Struct(..) => {
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
            match call_erasure {
                CallErasure::EraseTree => Some(erase_tree_kind(cx, expr)),
                _ => None,
            }
        }
        _ => None,
    }
}

// To avoid edits and conflicts in thir/cx/expr.rs, postprocess some of the work for expr.rs here
pub(crate) fn mirror_expr_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    expr: &'tcx Expr<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
    spec: bool,
) -> rustc_middle::thir::ExprKind<'tcx> {
    match expr.kind {
        ExprKind::MethodCall(..) | ExprKind::Call(..) | ExprKind::Struct(..) => {
            let call_erasure = handle_call(&cx.verus_ctxt, expr);
            if call_erasure.should_erase(spec) {
                erase_node_unadjusted(cx, expr, kind)
            } else {
                kind
            }
        }
        ExprKind::Field(..) | ExprKind::AddrOf(..) => {
            maybe_erase_node_unadjusted(cx, expr, kind, spec)
        }
        ExprKind::Unary(UnOp::Deref, _) if !cx.typeck_results.is_method_call(expr) => {
            maybe_erase_node_unadjusted(cx, expr, kind, spec)
        }
        _ => kind,
    }
}
