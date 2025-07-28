use crate::{erase::ResolvedCall, verus_items::VerusItems};
use rustc_hir::Attribute;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{Crate, HirId};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_mir_build_verus::verus::BodyErasure;
use rustc_span::SpanData;
use rustc_span::def_id::DefId;
use std::sync::Arc;
use vir::ast::{Fun, Function, Ident, Krate, Mode, Path, Pattern, VirErr};
use vir::messages::AstId;

pub struct ErasureInfo {
    pub(crate) hir_vir_ids: Vec<(HirId, AstId)>,
    pub(crate) resolved_calls: Vec<(HirId, SpanData, ResolvedCall)>,
    pub(crate) resolved_pats: Vec<(SpanData, Pattern)>,
    pub(crate) direct_var_modes: Vec<(HirId, Mode)>,
    pub(crate) external_functions: Vec<vir::ast::Fun>,
    pub(crate) ignored_functions: Vec<(rustc_span::def_id::DefId, SpanData)>,
    pub(crate) bodies: Vec<(LocalDefId, BodyErasure)>,
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
}

#[derive(Clone)]
pub(crate) struct BodyCtxt<'tcx> {
    pub(crate) ctxt: Context<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) fun_id: DefId,
    pub(crate) external_trait_from_to: Option<Arc<(Path, Path, Option<Path>)>>,
    pub(crate) mode: Mode,
    pub(crate) external_body: bool,
    pub(crate) in_ghost: bool,
    // loop_isolation for the nearest enclosing loop, false otherwise
    pub(crate) loop_isolation: bool,
}

impl ErasureInfo {
    pub(crate) fn resolve_call_modes(&mut self, vir_crate: &Krate) {
        use std::collections::HashMap;
        let mut functions: HashMap<Fun, Function> = HashMap::new();
        for f in vir_crate.functions.iter() {
            functions.insert(f.x.name.clone(), f.clone());
        }
        for (_, _, r) in &mut self.resolved_calls {
            if let ResolvedCall::CallPlaceholder(ufun, rfun, in_ghost) = r {
                // Note: in principle, the unresolved function ufun should always be present,
                // but we currently allow external declarations of resolved trait functions
                // without a corresponding external trait declaration.
                if let Some(f) = functions.get(ufun).or_else(|| functions.get(rfun)) {
                    if *in_ghost && f.x.mode == Mode::Exec {
                        // This must be an autospec, so change exec -> spec
                        let param_modes = Arc::new(f.x.params.iter().map(|_| Mode::Spec).collect());
                        *r = ResolvedCall::CallModes(Mode::Spec, param_modes);
                    } else {
                        let param_modes = Arc::new(f.x.params.iter().map(|p| p.x.mode).collect());
                        *r = ResolvedCall::CallModes(f.x.mode, param_modes);
                    }
                }
                // If the function is missing, just leave the CallPlaceholder as-is,
                // and any future attempt to use the CallPlaceholder
                // is considered an internal Verus error.
                // The function can be missing for various reasons:
                // - the call is to an external function with no spec,
                //   which we want to report as an error later, not here.
                // - the called function was pruned
            }
        }
    }
}

impl<'tcx> ContextX<'tcx> {
    pub(crate) fn get_verus_item(&self, def_id: DefId) -> Option<&crate::verus_items::VerusItem> {
        self.verus_items.id_to_name.get(&def_id)
    }

    pub(crate) fn get_verifier_attrs(
        &self,
        attrs: &[Attribute],
    ) -> Result<crate::attributes::VerifierAttrs, VirErr> {
        crate::attributes::get_verifier_attrs(attrs, Some(&mut *self.diagnostics.borrow_mut()))
    }

    pub(crate) fn get_verifier_attrs_no_check(
        &self,
        attrs: &[Attribute],
    ) -> Result<crate::attributes::VerifierAttrs, VirErr> {
        crate::attributes::get_verifier_attrs_no_check(
            attrs,
            Some(&mut *self.diagnostics.borrow_mut()),
        )
    }

    pub(crate) fn get_external_attrs(
        &self,
        attrs: &[Attribute],
    ) -> Result<crate::attributes::ExternalAttrs, VirErr> {
        crate::attributes::get_external_attrs(attrs, Some(&mut *self.diagnostics.borrow_mut()))
    }

    pub(crate) fn push_body_erasure(&self, local_def_id: LocalDefId, c: BodyErasure) {
        let mut r = self.erasure_info.borrow_mut();
        r.bodies.push((local_def_id, c));
    }
}
