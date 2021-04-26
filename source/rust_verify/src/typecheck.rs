use rustc_hir::{Expr, ExprKind};
use rustc_middle::ty::{FormalVerifierTyping, Ty, TyCtxt, TyKind};
use rustc_span::def_id::DefId;

pub(crate) const BUILTIN_INT: &str = "builtin::int";
pub(crate) const BUILTIN_NAT: &str = "builtin::nat";

pub(crate) struct Typecheck {
    pub int_ty_id: Option<DefId>,
    pub nat_ty_id: Option<DefId>,
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
        // For example, "i == n" might work but "n == i" might fail (requiring "n as int == i").
        match (ty.kind(), expected_ty, &expr.kind) {
            (_, _, ExprKind::Unary(_, _)) | (_, _, ExprKind::Binary(_, _, _)) => {
                // Implicitly coercing arithmetic results could be confusing
                // and deceptive, so don't do it.
                // Example: if x: u64, then coercing (x + 1) to int would
                // only coerce to int *after* performing the + 1 and potentially overflowing.
                // Here, the programmer probably meant (x as int) + 1.
                ty
            }
            (TyKind::Int(_), Some(t_coerce), _) if self.is_int(t_coerce) => t_coerce,
            (TyKind::Uint(_), Some(t_coerce), _) if self.is_int_or_nat(t_coerce) => t_coerce,
            (_, Some(t_coerce), _) if self.is_int(t_coerce) && self.is_nat(ty) => t_coerce,
            _ => ty,
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
}
