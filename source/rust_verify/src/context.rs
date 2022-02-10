use rustc_hir::{Crate, HirId};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_span::SpanData;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Mode, Typ};

pub struct ErasureInfo {
    pub(crate) external_functions: Vec<vir::ast::Fun>,
    pub(crate) ignored_functions: Vec<SpanData>,
    pub(crate) external_body_functions: Vec<(SpanData, ExternalBodyErasureInfo)>,
}

#[derive(Clone)]
pub struct ExternalBodyErasureInfo {
    pub num_header_stmts: usize,
}

type ErasureInfoRef = std::rc::Rc<std::cell::RefCell<ErasureInfo>>;

pub type Context<'tcx> = Arc<ContextX<'tcx>>;
pub struct ContextX<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) erasure_info: ErasureInfoRef,
    pub(crate) autoviewed_call_typs: HashMap<HirId, Typ>,
}

#[derive(Clone)]
pub(crate) struct BodyCtxt<'tcx> {
    pub(crate) ctxt: Context<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) mode: Mode,
    pub(crate) external_body: bool,
}
