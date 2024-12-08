use rustc_hir::def_id::DefId;
use rustc_hir::hir_id::HirId;
use rustc_hir::{PrimTy, QPath};
use rustc_hir::def::Res;
use vir::ast::{Typs, Ident, VirErr};
use crate::spec_typeck::State;
use rustc_hir::def::DefKind;

pub enum PathResolution {
    Local(HirId),
    Fn(DefId, Typs),
    Const(DefId),
    Datatype(DefId, Typs),
    DatatypeVariant(DefId, Ident, Typs),
    PrimTy(PrimTy),
}

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn check_qpath(
        &mut self,
        qpath: &QPath<'tcx>,
    ) -> Result<PathResolution, VirErr> {
        match qpath {
            QPath::Resolved(None, path) => {
                self.check_res(&path.res)
            }
            QPath::Resolved(Some(_), _path) => {
                todo!()
            }
            QPath::TypeRelative(_ty, _path_segment) => {
                todo!()
            }
            QPath::LangItem(..) => {
                todo!()
            }
        }
    }

    fn check_res(
        &mut self,
        res: &Res,
    ) -> Result<PathResolution, VirErr> {
        match res {
            Res::Def(def_kind, _def_id) => {
                match def_kind {
                    DefKind::Fn => {
                        todo!()
                    }
                    _ => todo!()
                }
            }
            Res::PrimTy(prim_ty) => Ok(PathResolution::PrimTy(*prim_ty)),
            Res::Local(id) => Ok(PathResolution::Local(*id)),
            _ => todo!(),
        }
    }
}

