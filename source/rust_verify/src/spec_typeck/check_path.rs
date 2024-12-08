use rustc_hir::def_id::DefId;
use rustc_hir::hir_id::HirId;
use rustc_hir::{PrimTy, QPath};
use rustc_hir::def::Res;
use vir::ast::{Typs, Ident, VirErr};
use crate::spec_typeck::State;
use rustc_hir::def::DefKind;
use std::sync::Arc;

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
            Res::Def(def_kind, def_id) => {
                match def_kind {
                    DefKind::Fn => {
                        Ok(PathResolution::Fn(*def_id, Arc::new(vec![])))
                    }
                    _ => todo!()
                }
            }
            Res::PrimTy(prim_ty) => Ok(PathResolution::PrimTy(*prim_ty)),
            Res::Local(id) => Ok(PathResolution::Local(*id)),
            _ => todo!(),
        }
    }

    pub fn get_item_mode(&self, def_id: DefId) -> Result<vir::ast::Mode, VirErr> {
        match def_id.as_local() {
            Some(local_def_id) => {
                let hir_id = self.tcx.local_def_id_to_hir_id(local_def_id);
                let attrs = self.tcx.hir().attrs(hir_id);
                let mode = crate::attributes::get_mode_opt(attrs);
                match mode {
                    Some(mode) => Ok(mode),
                    None => Ok(vir::ast::Mode::Exec),
                }
            }
            None => {
                todo!()
            }
        }
    }
}

