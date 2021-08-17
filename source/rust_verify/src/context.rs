use rustc_hir::Crate;
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;

pub struct Context<'tcx, 'sm> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) source_map: &'sm SourceMap,
}
