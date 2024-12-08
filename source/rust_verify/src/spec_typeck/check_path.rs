use rustc_hir::def_id::DefId;
use rustc_hir::hir_id::HirId;
use rustc_hir::{Path, PrimTy};
use rustc_hir::def::Res;
use vir::ast::{Typs, Ident};

pub enum PathResolution {
    Local(HirId),
    Fn(DefId, Typs),
    Const(DefId),
    Datatype(DefId, Typs),
    DatatypeVariant(DefId, Ident, Typs),
    PrimTy(PrimTy),
}

impl State<'_, '_> {
    pub fn check_qpath(
        &mut self,
        qpath: &QPath<'tcx>,
    ) {
        match &path.res {
            QPath::Resolved(None, path) => {
                check_res(path.res)
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
    ) -> {
        match &path.res {
            Res::Def(def_kind, def_id) => {
                match def_kind {
                    DefKind::Fn => {
                        todo!(),
                    }
                    todo!(),
                }
            }
            Res::PrimTy(prim_ty) => PathResolution::PrimTy(prim_ty),
            Res::Local(id) => PathResolution::Local(id),
            _ => todo!(),
        }
    }
}
