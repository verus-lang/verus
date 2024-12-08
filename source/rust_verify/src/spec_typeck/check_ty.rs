use crate::{unsupported_err, unsupported_err_unless};
use crate::spec_typeck::State;
use vir::ast::{Typ, VirErr, TypX, Primitive};
use rustc_hir::{Ty, TyKind};
use std::sync::Arc;

impl State<'_> {
    pub fn check_ty<'tcx>(
        &mut self,
        ty: Ty,
    ) -> Result<Typ, VirErr> {
        match &ty.kind {
            TyKind::Slice(ty) => {
                let typ = self.check_ty(ty)?;
                let typs = Arc::new(vec![typ]);
                (Arc::new(TypX::Primitive(Primitive::Slice, typs)), false)
            }
            TyKind::Array(ty, array_len) => {
                let typ = self.check_ty(ty)?;
                let len = self.check_const(array_len)?;
                let typs = Arc::new(vec![typ, len]);
                (Arc::new(TypX::Primitive(Primitive::Slice, typs)), false)
            }
            TyKind::Ptr(..) => todo!(),
            TyKind::Ref(..) => todo!(),
            TyKind::BareFn(..) => todo!(),
            TyKind::Never => todo(),
            TyKind::Tup(types) => {
                let mut typs = vec![];
                for t in types.iter() {
                    typs.push(self.check_ty(t)?);
                }
                Ok(vir::ast_util::mk_tuple_typ(&Arc::new(typs)))
            }
            TyKind::Path(_qpath) => {
                /*match qpath {
                    QPath::Resolved(
                }*/
                todo!()
            }
            TyKind::Infer => {
                Ok(self.unifier.new_unif_variable_type())
            }
            TyKind::InferDelegation(_, _)
            | TyKind::AnonAdt(..)
            | TyKind::OpaqueDef(..)
            | TyKind::TraitObject(..)
            | TyKind::Typeof(..)
            | TyKind::Err(..)
            | TyKind::Pat(..)
            => {
                unsupported_err!("type: {:?}", ty);
            }
        }
    }
}
