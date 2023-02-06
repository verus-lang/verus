use crate::erase::ResolvedCall;
use air::ast::AstId;
use rustc_hir::{Crate, HirId};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_span::SpanData;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Expr, InferMode, Mode, Pattern, Typ};

pub struct ErasureInfo {
    pub(crate) hir_vir_ids: Vec<(HirId, AstId)>,
    pub(crate) resolved_calls: Vec<(HirId, SpanData, ResolvedCall)>,
    pub(crate) resolved_exprs: Vec<(SpanData, Expr)>,
    pub(crate) resolved_pats: Vec<(SpanData, Pattern)>,
    pub(crate) external_functions: Vec<vir::ast::Fun>,
    pub(crate) ignored_functions: Vec<(rustc_span::def_id::DefId, SpanData)>,
}

type ErasureInfoRef = std::rc::Rc<std::cell::RefCell<ErasureInfo>>;

pub type ArchContext = Arc<ArchContextX>;
pub struct ArchContextX {
    pub(crate) word_bits: vir::prelude::ArchWordBits,
}

pub type Context<'tcx> = Arc<ContextX<'tcx>>;
pub struct ContextX<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) erasure_info: ErasureInfoRef,
    pub(crate) autoviewed_call_typs: HashMap<HirId, Typ>,
    pub(crate) unique_id: std::cell::Cell<u64>,
    pub(crate) arch: ArchContext,
}

#[derive(Clone)]
pub(crate) struct BodyCtxt<'tcx> {
    pub(crate) ctxt: Context<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) mode: Mode,
    pub(crate) external_body: bool,
    pub(crate) in_ghost: bool,
}

impl<'tcx> ContextX<'tcx> {
    pub(crate) fn infer_mode(&self) -> InferMode {
        let id = self.unique_id.get();
        self.unique_id.set(id + 1);
        id
    }
}
