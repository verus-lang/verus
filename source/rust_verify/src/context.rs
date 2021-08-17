use rustc_middle::ty::TyCtxt;
use rustc_hir::Crate;
use rustc_span::source_map::SourceMap;

pub(crate) struct Context<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) source_map: &'tcx SourceMap,
}
