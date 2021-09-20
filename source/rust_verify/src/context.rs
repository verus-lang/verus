use crate::erase::ResolvedCall;
use rustc_hir::Crate;
use rustc_middle::ty::TyCtxt;
use rustc_span::SpanData;
use vir::ast::Mode;

#[derive(Clone)]
pub struct ErasureInfo {
    pub(crate) resolved_calls: Vec<(SpanData, ResolvedCall)>,
    pub(crate) condition_modes: Vec<(SpanData, Mode)>,
    pub(crate) external_functions: Vec<vir::ast::Path>,
}

type ErasureInfoRef = std::rc::Rc<std::cell::RefCell<ErasureInfo>>;

#[derive(Clone)]
pub struct Context<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) erasure_info: ErasureInfoRef,
}
