use crate::rust_to_vir_base::{
    def_id_to_vir_path, get_mode, get_var_mode, get_verifier_attrs, mid_ty_to_vir,
};
use rustc_hir::intravisit::Visitor;
use rustc_hir::{BinOp, BinOpKind, Expr, ExprKind, HirId, PathSegment};
use rustc_middle::ty::{FormalVerifierTyping, Ty, TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use vir::ast::{Mode, Typ};

pub(crate) const BUILTIN_INT: &str = "builtin::int";
pub(crate) const BUILTIN_NAT: &str = "builtin::nat";

pub(crate) struct Typecheck {
    pub int_ty_id: Option<DefId>,
    pub nat_ty_id: Option<DefId>,
    pub exprs_in_spec: Arc<Mutex<HashSet<HirId>>>,
    pub autoviewed_calls: HashSet<HirId>,
    pub autoviewed_call_typs: Arc<Mutex<HashMap<HirId, Typ>>>,
}

struct VisitSpec<'tcx> {
    tcx: TyCtxt<'tcx>,
    exprs_in_spec: Arc<Mutex<HashSet<HirId>>>,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for VisitSpec<'tcx> {
    type Map = rustc_hir::intravisit::ErasedMap<'tcx>;

    fn nested_visit_map(&mut self) -> rustc_hir::intravisit::NestedVisitorMap<Self::Map> {
        rustc_hir::intravisit::NestedVisitorMap::None
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        {
            let mut exprs_in_spec = self.exprs_in_spec.lock().expect("visit_expr lock");
            if exprs_in_spec.contains(&expr.hir_id) {
                return;
            }
            exprs_in_spec.insert(expr.hir_id);
        }
        match &expr.kind {
            ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
                let body = self.tcx.hir().body(*body_id);
                self.visit_expr(&body.value);
            }
            _ => {}
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

fn is_t<'tcx>(ty: Ty<'tcx>, name: &str, def: &mut Option<DefId>) -> bool {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => {
            let def_id = adt_def.did;
            match *def {
                Some(id) => def_id == id,
                None => {
                    // TODO/HACK: it would be nice if we could compute int_ty_id/nat_ty_id earlier
                    // rather than (slowly) snooping for it here via ty.to_string()
                    if ty.to_string() == name {
                        *def = Some(def_id);
                        true
                    } else {
                        false
                    }
                }
            }
        }
        _ => false,
    }
}

fn allow_widen<'tcx>(expr: &'tcx Expr<'tcx>) -> bool {
    // Implicitly coercing arithmetic results could be confusing
    // and deceptive, so don't do it.
    // Example: if x: u64, then coercing (x + 1) to int would
    // only coerce to int *after* performing the + 1 and potentially overflowing.
    // Here, the programmer probably meant (x as int) + 1.
    match &expr.kind {
        ExprKind::Unary(_, _) | ExprKind::Binary(_, _, _) => false,
        _ => true,
    }
}

impl Typecheck {
    fn is_int<'tcx>(&mut self, ty: Ty<'tcx>) -> bool {
        is_t(ty, BUILTIN_INT, &mut self.int_ty_id)
    }

    fn is_nat<'tcx>(&mut self, ty: Ty<'tcx>) -> bool {
        is_t(ty, BUILTIN_NAT, &mut self.nat_ty_id)
    }

    fn is_int_or_nat<'tcx>(&mut self, ty: Ty<'tcx>) -> bool {
        self.is_int(ty) || self.is_nat(ty)
    }
}

impl FormalVerifierTyping for Typecheck {
    fn coerce_type<'tcx>(
        &mut self,
        _tcx: TyCtxt<'tcx>,
        expr: &'tcx Expr<'tcx>,
        ty: Ty<'tcx>,
        expected_ty: &Option<Ty<'tcx>>,
    ) -> Ty<'tcx> {
        // For convenience, allow implicit coercions from integral types to int in some situations.
        // This is strictly opportunistic; in many situations you still need "as int".
        match (ty.kind(), expected_ty, allow_widen(expr)) {
            (_, _, false) => ty,
            (TyKind::Int(_), Some(t_coerce), _) if self.is_int(t_coerce) => t_coerce,
            (TyKind::Uint(_), Some(t_coerce), _) if self.is_int_or_nat(t_coerce) => t_coerce,
            (_, Some(t_coerce), _) if self.is_int(t_coerce) && self.is_nat(ty) => t_coerce,
            _ => ty,
        }
    }

    fn widen_binary_types<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        op: BinOp,
        is_assign: bool,
        lhs_expr: &'tcx Expr<'tcx>,
        rhs_expr: &'tcx Expr<'tcx>,
        lhs_ty: Ty<'tcx>,
        rhs_ty: Ty<'tcx>,
    ) -> Option<(bool, Ty<'tcx>, bool)> {
        if is_assign {
            match (op.node, &lhs_ty.kind(), &rhs_ty.kind()) {
                (BinOpKind::Shr, TyKind::Bool, TyKind::Bool | TyKind::Infer(..)) => {
                    return Some((true, lhs_ty, true));
                }
                _ => return None,
            }
        }

        // For convenience, allow implicit coercions from integral types to int in some situations.
        // This is strictly opportunistic; in many situations you still need "as int".

        // widen_left = false: widen rhs_expr to lhs_ty
        // widen_left = true:  widen lhs_expr to rhs_ty
        let widen_left = match (&lhs_ty.kind(), &rhs_ty.kind()) {
            (_, TyKind::Int(_)) if self.is_int(lhs_ty) => false,
            (TyKind::Int(_), _) if self.is_int(rhs_ty) => true,
            (_, TyKind::Uint(_)) if self.is_int_or_nat(lhs_ty) => false,
            (TyKind::Uint(_), _) if self.is_int_or_nat(rhs_ty) => true,
            _ if self.is_int(lhs_ty) && self.is_nat(rhs_ty) => false,
            _ if self.is_nat(lhs_ty) && self.is_int(rhs_ty) => true,
            _ => return None,
        };
        let is_cmp = match op.node {
            BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul => false,
            BinOpKind::Eq | BinOpKind::Ne => true,
            BinOpKind::Lt | BinOpKind::Le | BinOpKind::Ge | BinOpKind::Gt => true,
            _ => return None,
        };
        let t = if is_cmp {
            tcx.types.bool
        } else if widen_left {
            rhs_ty
        } else {
            lhs_ty
        };
        match (widen_left, allow_widen(lhs_expr), allow_widen(rhs_expr)) {
            (false, _, false) => None,
            (true, false, _) => None,
            _ => Some((widen_left, t, false)),
        }
    }

    fn cast_type<'tcx>(&mut self, _tcx: TyCtxt<'tcx>, t_expr: Ty<'tcx>, t_cast: Ty<'tcx>) -> bool {
        if t_cast.is_integral() && self.is_int_or_nat(t_expr) {
            true
        } else if t_expr.is_integral() && self.is_int_or_nat(t_cast) {
            true
        } else if self.is_int_or_nat(t_expr) && self.is_int_or_nat(t_cast) {
            true
        } else {
            false
        }
    }

    fn is_infinite_range<'tcx>(&mut self, _tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
        self.is_int_or_nat(ty)
    }

    fn str_infinite_range<'tcx>(&mut self, _tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> &'static str {
        if self.is_nat(ty) { "nat" } else { "int" }
    }

    fn mk_infinite_range<'tcx>(&mut self, tcx: TyCtxt<'tcx>, name: &'static str) -> Ty<'tcx> {
        if name == "nat" {
            match self.nat_ty_id {
                None => panic!("internal error: nat_ty_id"),
                Some(nat_id) => tcx.type_of(nat_id),
            }
        } else {
            match self.int_ty_id {
                None => panic!("internal error: int_ty_id"),
                Some(int_id) => tcx.type_of(int_id),
            }
        }
    }

    fn interpose_call<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        expr: &'tcx Expr<'tcx>,
        def_id: DefId,
        args: &'tcx [Expr<'tcx>],
    ) -> Option<(PathSegment<'tcx>, &'tcx [Expr<'tcx>])> {
        let spec_walk_arg = |arg: &'tcx Expr<'tcx>| {
            let mut visitor = VisitSpec { tcx: tcx, exprs_in_spec: self.exprs_in_spec.clone() };
            visitor.visit_expr(arg);
        };

        match tcx.hir().get_if_local(def_id) {
            Some(rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
                kind: rustc_hir::ImplItemKind::Fn(_fn_sig, body_id),
                ..
            }))
            | Some(rustc_hir::Node::Item(rustc_hir::Item {
                kind: rustc_hir::ItemKind::Fn(_fn_sig, _, body_id),
                ..
            })) => {
                let local_id = def_id.as_local();
                if local_id.is_none() {
                    return None;
                }
                let hir_id = tcx.hir().local_def_id_to_hir_id(local_id.unwrap());
                if self.exprs_in_spec.lock().expect("interpose_call").contains(&expr.hir_id) {
                    // This call appears in a spec context.
                    let attrs = get_verifier_attrs(tcx.hir().attrs(hir_id));
                    if attrs.is_ok()
                        && attrs.unwrap().autoview
                        && !self.autoviewed_calls.contains(&expr.hir_id)
                    {
                        // This call is marked autoview.
                        // Replace e.f(args) it with e.view().f(args)
                        self.autoviewed_calls.insert(expr.hir_id);
                        let segment = PathSegment::from_ident(Ident::from_str("view"));
                        let args = &args[..1];
                        return Some((segment, args));
                    }
                    // No reason to do any more work; we're already registered in exprs_in_spec
                    return None;
                }

                let mode = get_mode(Mode::Exec, tcx.hir().attrs(hir_id));
                let params = tcx.hir().body(*body_id).params;
                if params.len() == args.len() {
                    for (param, arg) in params.iter().zip(args) {
                        let param_mode = get_var_mode(mode, tcx.hir().attrs(param.hir_id));
                        if param_mode == Mode::Spec {
                            // This is a spec argument, so register the argument's whole AST
                            // as appearing in a spec context.
                            spec_walk_arg(arg);
                        }
                    }
                }
                None
            }
            None => {
                if self.exprs_in_spec.lock().expect("interpose_call").contains(&expr.hir_id) {
                    return None;
                }
                let path = def_id_to_vir_path(tcx, def_id);
                if let Some(krate) = &path.krate {
                    if **krate == "builtin" {
                        let mode = get_mode(Mode::Exec, tcx.item_attrs(def_id));
                        if mode != Mode::Exec {
                            for arg in args {
                                // HACK: since we don't have the parameter attributes,
                                // assume builtin uses the defaults
                                // TODO: when we support multiple crates,
                                // we should be able to get the modes directly
                                spec_walk_arg(arg);
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn interposed_ty<'tcx>(&mut self, tcx: TyCtxt<'tcx>, expr: &'tcx Expr<'tcx>, ty: Ty<'tcx>) {
        let typ = mid_ty_to_vir(tcx, ty);
        self.autoviewed_call_typs
            .lock()
            .expect("lock autoviewed_call_typs")
            .insert(expr.hir_id, typ);
    }

    fn no_adjust<'tcx>(&mut self, _tcx: TyCtxt<'tcx>, expr: &'tcx Expr<'tcx>) -> bool {
        self.autoviewed_calls.contains(&expr.hir_id)
    }
}
