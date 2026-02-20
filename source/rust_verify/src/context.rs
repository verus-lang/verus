use crate::{erase::ResolvedCall, verus_items::VerusItems};
use rustc_hir::Attribute;
use rustc_hir::Crate;
use rustc_hir::HirId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_mir_build_verus::verus::BodyErasure;
use rustc_span::SpanData;
use rustc_span::def_id::DefId;
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::DerefMut;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::AtomicU64;
use vir::ast::{Ident, Mode, Path, Pattern, VirErr};
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

pub type Context<'tcx> = Rc<ContextX<'tcx>>;
pub struct ContextX<'tcx> {
    pub(crate) cmd_line_args: crate::config::Args,
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) krate: &'tcx Crate<'tcx>,
    pub(crate) erasure_info: ErasureInfoRef,
    pub(crate) spans: crate::spans::SpanContext,
    pub(crate) verus_items: Arc<VerusItems>,
    pub(crate) diagnostics: Rc<RefCell<Vec<vir::ast::VirErrAs>>>,
    pub(crate) no_vstd: bool,
    pub(crate) arch_word_bits: Option<vir::ast::ArchWordBits>,
    pub(crate) crate_name: Ident,
    pub(crate) vstd_crate_name: Ident,
    pub(crate) name_def_id_map: Rc<RefCell<std::collections::HashMap<Path, DefId>>>,
    pub(crate) next_read_kind_id: AtomicU64,
}

/// The context in which a given header node might be interpretted
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HeaderSetting {
    /// Fn signature headers (requires, ensures, unwind, mask, decreases)
    /// Including closures
    Fn,
    /// Loops (invariants, ensures, etc.)
    Loop,
    /// Requires or ensures on an assert-by, assert-by-nonlinear, assert-by-forall etc.
    Assert,
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
    pub(crate) new_mut_ref: bool,
    pub(crate) migrate_postcondition_vars: Option<std::collections::HashSet<vir::ast::VarIdent>>,
    /// Context to interpret a header if we encounter one
    /// (this is used to determine when it's correct to set `in_fn_sig`).
    pub(crate) header_setting: HeaderSetting,
    /// Are we in the signature of a function or closure?
    pub(crate) in_fn_sig: bool,
    /// Are we in a postcondition of a function or closure? (implies in_fn_sig)
    pub(crate) in_postcondition: bool,
    /// Are we inside an "old" node? (new-mut-ref only)
    pub(crate) in_old: bool,
    /// params for the enclosing function and all enclosing non-spec-closures
    pub(crate) params: Rc<Vec<Vec<vir::ast::VarIdent>>>,
    /// unwrapped params encountered so far (inner_name -> outer_name) e.g. (x -> verus_tmp_x)
    pub(crate) unwrap_param_map: Rc<RefCell<HashMap<vir::ast::VarIdent, vir::ast::VarIdent>>>,
}

impl<'tcx> ContextX<'tcx> {
    pub(crate) fn new(
        cmd_line_args: crate::config::Args,
        tcx: TyCtxt<'tcx>,
        erasure_info: ErasureInfoRef,
        spans: crate::spans::SpanContext,
        verus_items: Arc<VerusItems>,
        no_vstd: bool,
        crate_name: Ident,
        vstd_crate_name: Ident,
    ) -> Self {
        ContextX {
            cmd_line_args,
            tcx,
            krate: tcx.hir_crate(()),
            erasure_info,
            spans,
            verus_items,
            diagnostics: Rc::new(RefCell::new(Vec::new())),
            no_vstd,
            arch_word_bits: None,
            crate_name,
            vstd_crate_name,
            name_def_id_map: Rc::new(RefCell::new(HashMap::new())),
            next_read_kind_id: AtomicU64::new(0),
        }
    }

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

    pub(crate) fn path_def_id_ref(
        &self,
    ) -> Option<impl DerefMut<Target = HashMap<Path, DefId>> + use<'_>> {
        self.name_def_id_map.try_borrow_mut().ok()
    }

    pub(crate) fn def_id_to_vir_path(&self, def_id: DefId) -> Path {
        crate::rust_to_vir_base::def_id_to_vir_path(
            self.tcx,
            &self.verus_items,
            def_id,
            self.path_def_id_ref(),
        )
    }

    pub(crate) fn mid_ty_to_vir(
        &self,
        param_env_src: DefId,
        span: rustc_span::Span,
        ty: &rustc_middle::ty::Ty<'tcx>,
        allow_mut_ref: bool,
    ) -> Result<vir::ast::Typ, VirErr> {
        crate::rust_to_vir_base::mid_ty_to_vir(
            self.tcx,
            &self.verus_items,
            self.path_def_id_ref(),
            param_env_src,
            span,
            ty,
            allow_mut_ref,
        )
    }

    pub(crate) fn unique_read_kind_id(&self) -> u64 {
        self.next_read_kind_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }
}

impl<'tcx> BodyCtxt<'tcx> {
    pub(crate) fn is_copy(&self, ty: rustc_middle::ty::Ty<'tcx>) -> bool {
        let param_env = self.ctxt.tcx.param_env(self.fun_id);
        let typing_env = rustc_middle::ty::TypingEnv {
            param_env,
            typing_mode: rustc_middle::ty::TypingMode::non_body_analysis(),
        };
        self.ctxt.tcx.type_is_copy_modulo_regions(typing_env, ty)
    }

    pub(crate) fn mid_ty_to_vir(
        &self,
        span: rustc_span::Span,
        ty: &rustc_middle::ty::Ty<'tcx>,
        allow_mut_ref: bool,
    ) -> Result<vir::ast::Typ, VirErr> {
        self.ctxt.mid_ty_to_vir(self.fun_id, span, ty, allow_mut_ref)
    }

    pub(crate) fn is_param_migrated(&self, ident: &vir::ast::VarIdent) -> bool {
        let Some(vars) = &self.migrate_postcondition_vars else {
            return false;
        };
        let r = self.unwrap_param_map.borrow();
        let id = match r.get(ident) {
            Some(unwrap_param_outer_id) => unwrap_param_outer_id,
            None => ident,
        };
        vars.contains(id)
    }

    pub(crate) fn is_param_for_fn_or_non_spec_closure(&self, ident: &vir::ast::VarIdent) -> bool {
        let r = self.unwrap_param_map.borrow();
        let id = match r.get(ident) {
            Some(unwrap_param_outer_id) => unwrap_param_outer_id,
            None => ident,
        };
        self.params.iter().any(|params| params.iter().any(|param| param == id))
    }

    pub(crate) fn is_param_for_innermost_fn_or_non_spec_closure(
        &self,
        ident: &vir::ast::VarIdent,
    ) -> bool {
        let r = self.unwrap_param_map.borrow();
        let id = match r.get(ident) {
            Some(unwrap_param_outer_id) => unwrap_param_outer_id,
            None => ident,
        };
        self.params.last().unwrap().iter().any(|param| param == id)
    }

    pub(crate) fn set_header_setting(&self, s: HeaderSetting) -> BodyCtxt<'tcx> {
        BodyCtxt { header_setting: s, ..self.clone() }
    }
}
