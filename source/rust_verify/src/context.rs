use crate::erase::ResolvedCall;
use rustc_hir::Crate;
use rustc_middle::ty::TyCtxt;
use rustc_span::SpanData;
use vir::ast::{Expr, Mode, Pattern};

#[derive(Clone)]
pub struct ErasureInfo {
    pub(crate) resolved_calls: Vec<(SpanData, ResolvedCall)>,
    pub(crate) resolved_exprs: Vec<(SpanData, Expr)>,
    pub(crate) resolved_pats: Vec<(SpanData, Pattern)>,
    pub(crate) condition_modes: Vec<(SpanData, Mode)>,
    pub(crate) external_functions: Vec<vir::ast::Fun>,
}

type ErasureInfoRef = std::rc::Rc<std::cell::RefCell<ErasureInfo>>;

#[derive(Clone)]
pub struct Context<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) erasure_info: ErasureInfoRef,
}
