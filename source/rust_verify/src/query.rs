use crate::boundary_suggestions::build_boundary_suggestion;
use crate::config::Args;
use crate::context::Context;
use crate::external::CrateItems;
use crate::import_export::ImportOutput;
use crate::rust_to_vir_func::FunctionOrConstInfo;
use crate::rust_to_vir_func::finish_item;
use air::messages::Diagnostics;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{CrateId, Datatype, Fun, Function, FunctionStub, Krate, Path, VirErr, VirErrAs};
use vir::context::WarningCtx;
use vir::messages::{MessageLevel, ToAny};
use vir::modes::ErasureModes;
use vir::resolution_inference::{ResolutionInfo, krate_infer_resolution};
use vir::traits::{DemoteTraitLookup, MergedTraits};
use vir::well_formed::{DynCompatabilityChecks, InitialWfResults};

/// Krate without the full functions (i.e., empty function list in the krate)
/// Instead we have FunctionOrConstInfos which contains FunctionStubs.
pub(crate) struct PreCrate<'tcx> {
    pub ctxt: Context<'tcx>,
    pub warning_ctx: Arc<WarningCtx>,
    pub krate_without_funs: Krate,
    pub infos: Vec<Arc<FunctionOrConstInfo<'tcx>>>,
    pub fun_name_to_info: HashMap<Fun, Arc<FunctionOrConstInfo<'tcx>>>,
}

/// Used to guarantee that we emitted an error
#[derive(Clone, Copy)]
pub(crate) struct QueryError {
    _i_just_emitted_an_error: (),
}

pub(crate) type Res<T> = Result<T, QueryError>;

pub(crate) struct Query<'r, 'tcx> {
    args: Args,
    reporter: &'r dyn Diagnostics,
    crate_id: CrateId,

    /// Imported crates
    cache_other_vir_crates: Option<Res<Arc<Vec<Krate>>>>,
    /// Pre-crate before functions are lowered to VIR and checked in full
    cache_pre_crate: Option<Res<Arc<PreCrate<'tcx>>>>,
    /// Info used for demoting external traits
    cache_demote_trait_lookup: Option<Res<Arc<DemoteTraitLookup>>>,
    /// Traits and Trait Impls from all crates, de-duplicated
    cache_merged_traits: Option<Res<MergedTraits>>,
    /// Info used for demoting external traits
    cache_initial_wf_results: Option<Res<InitialWfResults>>,
    /// All function stubs, across this crate and imported crates
    cache_all_function_stubs: Option<Res<Arc<HashMap<Fun, FunctionStub>>>>,
    /// Pre-check functions, immediately after translation from HIR
    cache_unchecked_functions: HashMap<Fun, Res<Function>>,
    /// Completed functions
    cache_checked_functions: HashMap<
        Fun,
        Res<(Function, Arc<ErasureModes>, Option<Arc<ResolutionInfo>>, DynCompatabilityChecks)>,
    >,
    /// Crate that can be exported
    cache_exportable_crate: Option<Res<Krate>>,
    /// Crate with trait demotion, resolution inference, merged with imported crates and pruned
    cache_merged_crate: Option<Res<(Krate, Arc<WarningCtx>)>>,
    /// Merged erasure modes
    cache_erasure_modes: Option<Res<Arc<ErasureModes>>>,

    /// Errors found along the way
    pub encountered_blocking_vir_error: bool,
    pub encountered_non_blocking_vir_error: bool,
    pub func_failed_proof_notes: HashMap<Fun, HashSet<String>>,
}

impl<'r, 'tcx> Query<'r, 'tcx> {
    pub fn new(
        args: Args,
        reporter: &'r dyn Diagnostics,
        other_vir_crates: Vec<Krate>,
        pre_crate: PreCrate<'tcx>,
        crate_id: CrateId,
    ) -> Self {
        Self {
            args,
            reporter,
            crate_id,

            cache_other_vir_crates: Some(Ok(Arc::new(other_vir_crates))),
            cache_pre_crate: Some(Ok(Arc::new(pre_crate))),
            cache_demote_trait_lookup: None,
            cache_merged_traits: None,
            cache_initial_wf_results: None,
            cache_all_function_stubs: None,
            cache_unchecked_functions: HashMap::new(),
            cache_checked_functions: HashMap::new(),
            cache_exportable_crate: None,
            cache_merged_crate: None,
            cache_erasure_modes: None,

            encountered_blocking_vir_error: false,
            encountered_non_blocking_vir_error: false,
            func_failed_proof_notes: HashMap::new(),
        }
    }

    fn emit_errors(&mut self, errs: Vec<VirErr>) -> QueryError {
        assert!(errs.len() > 0);
        self.encountered_blocking_vir_error = true;
        for err in errs {
            self.reporter.report_now(&err.to_any());
        }
        QueryError { _i_just_emitted_an_error: () }
    }

    fn emit_error(&mut self, err: VirErr) -> QueryError {
        self.emit_errors(vec![err])
    }

    fn handle_wf_error(
        &mut self,
        ctxt: &Context<'tcx>,
        fun: Option<Fun>,
        wf_err: vir::well_formed::WFErr,
    ) -> QueryError {
        let vir::well_formed::WFErr { errors, boundary_errors, func_failed_proof_notes } = wf_err;
        assert!(errors.len() > 0 || boundary_errors.len() > 0);
        if errors.len() > 0 {
            let err = self.emit_errors(errors);
        }
        for (path, mut err) in boundary_errors.into_iter() {
            let map = ctxt.name_def_id_map.borrow();
            let did = map.get(&path);
            if let Some(did) = did {
                if let Ok(s) = build_boundary_suggestion(&ctxt, *did, &path) {
                    err = err
                        .help(format!("The following declaration may resolve this error:\n{}", s));
                }
            }
            self.emit_error(err);
        }
        if let Some(fun) = fun {
            self.record_failed_proof_notes(&fun, func_failed_proof_notes);
        } else {
            assert!(func_failed_proof_notes.is_empty());
        }
        QueryError { _i_just_emitted_an_error: () }
    }

    fn record_failed_proof_notes(&mut self, fun: &Fun, func_failed_proof_notes: HashSet<String>) {
        for x in func_failed_proof_notes.iter() {
            self.func_failed_proof_notes.entry(fun.clone()).or_default().insert(x.clone());
        }
    }

    fn emit_non_blocking_errors(&mut self, errs: Vec<VirErr>) {
        self.encountered_non_blocking_vir_error = true;
        for err in errs {
            self.reporter.report_now(&err.to_any());
        }
    }

    fn emit_diags(&mut self, diags: Vec<VirErrAs>) {
        for diag in diags.into_iter() {
            match diag {
                vir::ast::VirErrAs::Warning(err) => {
                    self.reporter.report_as(&err.to_any(), MessageLevel::Warning)
                }
                vir::ast::VirErrAs::Note(err) => {
                    self.reporter.report_as(&err.to_any(), MessageLevel::Note)
                }
            }
        }
    }

    //// Import crate

    pub fn get_other_vir_crates(&mut self) -> Res<Arc<Vec<Krate>>> {
        if let Some(imported) = &self.cache_other_vir_crates {
            return imported.clone();
        }
        unreachable!();
    }

    /*fn _compute_imported(&mut self) -> Res<Arc<ImportOutput>> {
        match crate::import_export::import_crates(&self.args, self.import_virs_via_cargo.clone()) {
            Ok(imported) => Ok(Arc::new(imported)),
            Err(err) => {
                assert!(err.spans.len() == 0);
                assert!(err.level == vir::messages::MessageLevel::Error);
                self.compiler.sess.dcx().err(err.note.clone());
                self.encountered_vir_error = true;
                return Err(QueryError {});
            }
        }
    }*/

    //// Pre-crate

    pub fn get_pre_crate(&mut self) -> Res<Arc<PreCrate<'tcx>>> {
        if let Some(pre_crate) = &self.cache_pre_crate {
            return pre_crate.clone();
        }
        unreachable!();
        //self.cache_pre_crate = Some(self._compute_pre_crate());
        //self.cache_pre_crate.clone().unwrap()
    }

    /*fn _compute_pre_crate(&mut self) -> Res<Arc<PreCrate<'tcx>>> {
        let imported = self.get_imported()?;
        let mut ctxtx = None;
        std::mem::swap(&mut self.ctxtx, &mut ctxtx);
        let res = crate::rust_to_vir::crate_to_vir(ctxtx.unwrap(), &imported.vir_crates, &self.crate_items);
        match res {
            Ok(pre_crate) => {
                Ok(Arc::new(pre_crate))
            }
            Err(errs) => {
                self.emit_errors(errs)
            }
        }
    }*/

    //// Get all function stubs

    pub fn get_all_function_stubs(&mut self) -> Res<Arc<HashMap<Fun, FunctionStub>>> {
        if let Some(all_function_stubs) = &self.cache_all_function_stubs {
            return all_function_stubs.clone();
        }
        self.cache_all_function_stubs = Some(self._compute_all_function_stubs());
        self.cache_all_function_stubs.clone().unwrap()
    }

    fn _compute_all_function_stubs(&mut self) -> Res<Arc<HashMap<Fun, FunctionStub>>> {
        // combine all the function stubs from our crate and the external crates
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        let mut stubs = HashMap::new();
        for stub in pre_crate.infos.iter().map(|info| info.iter_stubs()).flatten() {
            let found = stubs.insert(stub.x.name.clone(), stub.clone());
            if let Some(found) = found {
                return Err(self.emit_error(vir::well_formed::func_conflict_error(&stub, &found)));
            }
        }
        for krate in other_vir_crates.iter() {
            for function in krate.functions.iter() {
                let stub = vir::ast_util::function_to_stub(function);
                let found = stubs.insert(stub.x.name.clone(), stub.clone());
                if let Some(found) = found {
                    return Err(
                        self.emit_error(vir::well_formed::func_conflict_error(&stub, &found))
                    );
                }
            }
        }

        Ok(Arc::new(stubs))
    }

    //// DemoteTraitsLookup

    pub fn get_demote_trait_lookup(&mut self) -> Res<Arc<DemoteTraitLookup>> {
        if let Some(demote_trait_lookup) = &self.cache_demote_trait_lookup {
            return demote_trait_lookup.clone();
        }
        self.cache_demote_trait_lookup = Some(self._compute_demote_trait_lookup());
        self.cache_demote_trait_lookup.clone().unwrap()
    }

    pub fn _compute_demote_trait_lookup(&mut self) -> Res<Arc<DemoteTraitLookup>> {
        if let Some(demote_trait_lookup) = &self.cache_demote_trait_lookup {
            return demote_trait_lookup.clone();
        }
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        let function_stubs = self.get_all_function_stubs()?;
        Ok(Arc::new(vir::traits::DemoteTraitLookup::new(
            &pre_crate.krate_without_funs,
            &other_vir_crates,
            &function_stubs,
        )))
    }

    //// Merged traits

    pub fn get_merged_traits(&mut self) -> Res<MergedTraits> {
        if let Some(merged_traits) = &self.cache_merged_traits {
            return merged_traits.clone();
        }
        self.cache_merged_traits = Some(self._compute_merged_traits());
        self.cache_merged_traits.clone().unwrap()
    }

    pub fn _compute_merged_traits(&mut self) -> Res<MergedTraits> {
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        vir::traits::merge_external_traits(&pre_crate.krate_without_funs, &other_vir_crates)
            .map_err(|e| self.emit_error(e))
    }

    //// check_crate_initial

    pub fn get_initial_wf_results(&mut self) -> Res<InitialWfResults> {
        if let Some(initial_wf_results) = &self.cache_initial_wf_results {
            return initial_wf_results.clone();
        }
        self.cache_initial_wf_results = Some(self._compute_initial_wf_results());
        self.cache_initial_wf_results.clone().unwrap()
    }

    fn _compute_initial_wf_results(&mut self) -> Res<InitialWfResults> {
        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;
        let other_vir_crates = self.get_other_vir_crates()?;
        let function_stubs = self.get_all_function_stubs()?;
        let merged_traits = self.get_merged_traits()?;

        let (wf, non_blocking_errors, diags) = vir::well_formed::check_crate_initial(
            &pre_crate.krate_without_funs,
            &other_vir_crates,
            function_stubs.clone(),
            merged_traits.clone(),
            self.args.no_cheating,
        );
        self.emit_non_blocking_errors(non_blocking_errors);
        self.emit_diags(diags);
        wf.map_err(|e| self.handle_wf_error(ctxt, None, e))
    }

    //// datatypes map

    pub fn get_datatypes_map(&mut self) -> Res<Arc<HashMap<Path, Datatype>>> {
        Ok(self.get_initial_wf_results()?.lookup.dts.clone())
    }

    //// Translating an individual function from HIR -> VIR

    pub fn get_unchecked_function(&mut self, fun: &Fun) -> Res<Function> {
        if let Some(f) = self.cache_unchecked_functions.get(fun) {
            return f.clone();
        }

        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;
        let info = &pre_crate.fun_name_to_info[fun];
        let mut new_functions = vec![];
        let result = finish_item(ctxt, &info, &mut new_functions);
        ctxt.flush_diagnostics(self.reporter);
        match result {
            Ok(()) => {
                for new_function in new_functions.into_iter() {
                    let found = self
                        .cache_unchecked_functions
                        .insert(new_function.x.name.clone(), Ok(new_function));
                    assert!(found.is_none());
                }
                // Sanity check we got all the functions we expected
                for stub in info.iter_stubs() {
                    assert!(self.cache_unchecked_functions.contains_key(&stub.x.name));
                }
                self.cache_unchecked_functions.get(fun).unwrap().clone()
            }
            Err(err) => {
                let err = self.emit_error(err);
                for stub in info.iter_stubs() {
                    let found =
                        self.cache_unchecked_functions.insert(stub.x.name.clone(), Err(err));
                    assert!(found.is_none());
                }
                Err(err)
            }
        }
    }

    //// Checking an individual function

    pub fn get_checked_function(
        &mut self,
        fun: &Fun,
    ) -> Res<(Function, Arc<ErasureModes>, Option<Arc<ResolutionInfo>>, DynCompatabilityChecks)>
    {
        if let Some(f) = self.cache_checked_functions.get(fun) {
            return f.clone();
        }
        let res = self._compute_checked_function(fun);
        self.cache_checked_functions.insert(fun.clone(), res.clone());
        res
    }

    fn _compute_checked_function(
        &mut self,
        fun: &Fun,
    ) -> Result<
        (Function, Arc<ErasureModes>, Option<Arc<ResolutionInfo>>, DynCompatabilityChecks),
        QueryError,
    > {
        let function = self.get_unchecked_function(fun)?;
        let lookup = self.get_demote_trait_lookup()?;
        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;

        // Demote external traits

        let function = vir::traits::demote_external_traits_function_calls(&lookup, &function)
            .map_err(|e| self.emit_error(e))?;

        // WF checking

        let initial_wf = self.get_initial_wf_results()?;
        let function_stubs = self.get_all_function_stubs()?;
        let (wf, non_blocking_errors, diags) = vir::well_formed::check_function(
            &pre_crate.krate_without_funs,
            function_stubs.clone(),
            initial_wf.lookup.clone(),
            &lookup,
            &function,
            &pre_crate.warning_ctx,
            self.args.no_cheating,
            self.args.no_verify,
        );
        self.emit_non_blocking_errors(non_blocking_errors);
        self.emit_diags(diags);
        let wf = wf.map_err(|e| self.handle_wf_error(ctxt, Some(fun.clone()), e))?;
        let vir::well_formed::PerFunctionCheckResults {
            func_failed_proof_notes,
            dyn_compatability_checks,
        } = wf;
        self.record_failed_proof_notes(fun, func_failed_proof_notes);

        // Autospec

        let function = vir::autospec::resolve_autospec_in_function(&function_stubs, &function)
            .map_err(|e| self.emit_error(e))?;

        // Mode checking

        let (function, erasure_modes, resolution_info) = vir::modes::check_function(
            function_stubs.clone(),
            initial_wf.lookup.clone(),
            &function,
        )
        .map_err(|e| self.emit_errors(e))?;
        let erasure_modes = Arc::new(erasure_modes);
        let resolution_info = resolution_info.map(Arc::new);

        Ok((function, erasure_modes, resolution_info, dyn_compatability_checks))
    }

    //// Getting the completed krate

    pub fn get_exportable_crate(&mut self) -> Res<Krate> {
        if let Some(exportable_crate) = &self.cache_exportable_crate {
            return exportable_crate.clone();
        }
        self.cache_exportable_crate = Some(self._compute_exportable_crate());
        self.cache_exportable_crate.clone().unwrap()
    }

    pub fn _compute_exportable_crate(&mut self) -> Res<Krate> {
        let initial_wf_results = self.get_initial_wf_results()?;
        let _ = self.get_initial_wf_results()?;
        let pre_crate = self.get_pre_crate()?;
        let mut cratex = (*pre_crate.krate_without_funs).clone();
        let mut found_err = None;
        let mut all_dyn_compatability_checks = vec![initial_wf_results.dyn_compatability_checks];
        for stub in pre_crate.infos.iter().map(|info| info.iter_stubs()).flatten() {
            match self.get_checked_function(&stub.x.name) {
                Ok((function, _, _, dyn_compatability_checks)) => {
                    cratex.functions.push(function);
                    all_dyn_compatability_checks.push(dyn_compatability_checks);
                }
                Err(err) => found_err = Some(err),
            }
        }
        if let Some(err) = found_err {
            return Err(err);
        }

        let other_vir_crates = self.get_other_vir_crates()?;
        vir::traits::set_krate_dyn_compatibility(&other_vir_crates, &mut cratex);
        let krate = Arc::new(cratex);

        let mut krate = vir::ast_sort::sort_krate(&krate);
        Arc::make_mut(&mut krate).arch =
            vir::ast_simplify::krate_merge_arch(&krate, &other_vir_crates)
                .map_err(|e| self.emit_error(e))?;

        let (check, diags) = vir::well_formed::check_crate_final(&krate, &pre_crate.warning_ctx);
        self.emit_diags(diags);
        let () = check.map_err(|e| self.emit_error(e))?;

        vir::well_formed::finish_dyn_compatability_checks(&krate, all_dyn_compatability_checks)
            .map_err(|e| self.emit_errors(e))?;

        Ok(krate)
    }

    //// Getting the merged krate

    pub fn get_merged_crate(&mut self) -> Res<Krate> {
        if let Some(merged_crate) = &self.cache_merged_crate {
            return Ok(merged_crate.clone()?.0);
        }
        self.cache_merged_crate = Some(self._compute_merged_crate());
        Ok(self.cache_merged_crate.clone().unwrap()?.0)
    }

    pub fn get_updated_warning_ctx(&mut self) -> Res<Arc<WarningCtx>> {
        if let Some(merged_crate) = &self.cache_merged_crate {
            return Ok(merged_crate.clone()?.1);
        }
        self.cache_merged_crate = Some(self._compute_merged_crate());
        Ok(self.cache_merged_crate.clone().unwrap()?.1)
    }

    pub fn _compute_merged_crate(&mut self) -> Res<(Krate, Arc<WarningCtx>)> {
        let krate = self.get_exportable_crate()?;
        let pre_crate = self.get_pre_crate()?;
        let demote_trait_lookup = self.get_demote_trait_lookup()?;
        let other_vir_crates = self.get_other_vir_crates()?;
        let merged_traits = self.get_merged_traits()?;

        // Merge
        let my_crate = krate.clone();
        let mut vir_crates: Vec<Krate> = (*other_vir_crates).clone();
        vir_crates.push(krate);
        let unpruned_crate = vir::ast_simplify::merge_krates(vir_crates, &merged_traits)
            .map_err(|e| self.emit_error(e))?;
        let (krate, _) = vir::prune::prune_krate_for_module_or_krate(
            &unpruned_crate,
            &self.crate_id,
            Some(&my_crate),
            None,
            None,
            false,
            false,
        );

        // Demote external traits
        let krate = vir::traits::demote_external_traits(
            self.reporter,
            &pre_crate.warning_ctx,
            &krate,
            &demote_trait_lookup,
        )
        .map_err(|e| self.emit_error(e))?;

        // Inherit default bodies
        let mut new_warning_ctx = (*pre_crate.warning_ctx).clone();
        let krate = vir::traits::inherit_default_bodies(&krate, &mut new_warning_ctx)
            .map_err(|e| self.emit_error(e))?;

        // Resolution inference
        // Make sure to do this before the res_info goes stale
        let mut res_infos = HashMap::<Fun, Arc<ResolutionInfo>>::new();
        for stub in pre_crate.infos.iter().map(|info| info.iter_stubs()).flatten() {
            match self.get_checked_function(&stub.x.name) {
                Ok((_, _, Some(res_info), _)) => {
                    let found = res_infos.insert(stub.x.name.clone(), res_info.clone());
                    assert!(found.is_none());
                }
                Ok((_, _, None, _)) => {}
                Err(err) => unreachable!(),
            }
        }
        let krate = krate_infer_resolution(&krate, &res_infos).map_err(|e| self.emit_errors(e))?;

        vir::well_formed::check_crate_merged(&krate).map_err(|e| self.emit_error(e))?;

        pre_crate.ctxt.flush_diagnostics(self.reporter);

        Ok((krate, Arc::new(new_warning_ctx)))
    }

    //// Erasure modes
    //// TODO: Ultimately, we will want to use these individually rather than
    //// merging them all together.

    pub fn get_erasure_modes(&mut self) -> Res<Arc<ErasureModes>> {
        if let Some(erasure_modes) = &self.cache_erasure_modes {
            return erasure_modes.clone();
        }
        self.cache_erasure_modes = Some(self._compute_erasure_modes());
        self.cache_erasure_modes.clone().unwrap()
    }

    pub fn _compute_erasure_modes(&mut self) -> Res<Arc<ErasureModes>> {
        fn merge_erasure_modes(a: &mut ErasureModes, b: Arc<ErasureModes>) {
            let ErasureModes { local_modes, binder_modes, ctor_modes } = a;
            local_modes.extend(b.local_modes.clone());
            binder_modes.extend(b.binder_modes.clone());
            ctor_modes.extend(b.ctor_modes.clone());
        }

        let pre_crate = self.get_pre_crate()?;
        let mut e = ErasureModes { local_modes: vec![], binder_modes: vec![], ctor_modes: vec![] };
        for stub in pre_crate.infos.iter().map(|info| info.iter_stubs()).flatten() {
            let (_, erasure_modes, _, _) = self.get_checked_function(&stub.x.name)?;
            merge_erasure_modes(&mut e, erasure_modes);
        }
        Ok(Arc::new(e))
    }
}
