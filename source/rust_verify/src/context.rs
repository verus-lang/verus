use crate::{erase::ResolvedCall, verus_items::VerusItems};
use rustc_ast::Attribute;
use rustc_hir::{Crate, HirId};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_span::def_id::DefId;
use rustc_span::SpanData;
use std::sync::Arc;
use std::rc::Rc;
use std::cell::RefCell;
use vir::ast::{Expr, Ident, Mode, Pattern};
use vir::messages::AstId;
use crate::spec_exprs::SpecHir;

pub struct ErasureInfo {
    pub(crate) hir_vir_ids: Vec<(HirId, AstId)>,
    pub(crate) resolved_calls: Vec<(HirId, SpanData, ResolvedCall)>,
    pub(crate) resolved_exprs: Vec<(SpanData, Expr)>,
    pub(crate) resolved_pats: Vec<(SpanData, Pattern)>,
    pub(crate) direct_var_modes: Vec<(HirId, Mode)>,
    pub(crate) external_functions: Vec<vir::ast::Fun>,
    pub(crate) ignored_functions: Vec<(rustc_span::def_id::DefId, SpanData)>,
}

type ErasureInfoRef = std::rc::Rc<std::cell::RefCell<ErasureInfo>>;

pub type Context<'tcx> = Arc<ContextX<'tcx>>;
#[derive(Clone)]
pub struct ContextX<'tcx> {
    pub(crate) cmd_line_args: crate::config::Args,
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) erasure_info: ErasureInfoRef,
    pub(crate) spans: crate::spans::SpanContext,
    pub(crate) verus_items: Arc<VerusItems>,
    pub(crate) diagnostics: std::rc::Rc<std::cell::RefCell<Vec<vir::ast::VirErrAs>>>,
    pub(crate) no_vstd: bool,
    pub(crate) arch_word_bits: Option<vir::ast::ArchWordBits>,
    pub(crate) crate_name: Ident,
    pub(crate) vstd_crate_name: Ident,
    pub(crate) spec_hir: Arc<SpecHir<'tcx>>,
}

#[derive(Clone)]
pub(crate) struct BodyCtxt<'tcx> {
    pub(crate) ctxt: Context<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) fun_id: DefId,
    pub(crate) mode: Mode,
    pub(crate) external_body: bool,
    pub(crate) in_ghost: bool,
    pub(crate) scope_map: Rc<RefCell<air::scope_map::ScopeMap<vir::ast::VarIdent, vir::ast::Typ>>>,
}

impl<'tcx> ContextX<'tcx> {
    pub(crate) fn get_verus_item(&self, def_id: DefId) -> Option<&crate::verus_items::VerusItem> {
        self.verus_items.id_to_name.get(&def_id)
    }

    pub(crate) fn get_verifier_attrs(
        &self,
        attrs: &[Attribute],
    ) -> Result<crate::attributes::VerifierAttrs, vir::ast::VirErr> {
        crate::attributes::get_verifier_attrs(
            attrs,
            Some(&mut *self.diagnostics.borrow_mut()),
            Some(&self.cmd_line_args),
        )
    }
}

impl<'tcx> BodyCtxt<'tcx> {
    pub(crate) fn push_scope(&self, shadow: bool) {
        self.scope_map.borrow_mut().push_scope(shadow);
    }

    pub(crate) fn pop_scope(&self) {
        self.scope_map.borrow_mut().pop_scope();
    }

    pub(crate) fn scope_map_insert(&self, v: vir::ast::VarIdent, typ: vir::ast::Typ) {
        self.scope_map.borrow_mut().insert(v, typ).unwrap()
    }
}
