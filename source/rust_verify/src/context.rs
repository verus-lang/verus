use rustc_hir::Crate;
use rustc_middle::ty::TyCtxt;

#[derive(Clone)]
pub struct Context<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
}
