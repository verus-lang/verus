use crate::config::Args;
use crate::context::Context;
use crate::external::CrateItems;
use crate::import_export::ImportOutput;
use crate::rust_to_vir_func::FunctionOrConstInfo;
use crate::rust_to_vir_func::finish_item;
use air::messages::Diagnostics;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{Fun, Function, FunctionStub, Krate, VirErr, VirErrAs};
use vir::context::WarningCtx;
use vir::messages::{MessageLevel, ToAny};
use vir::modes::ErasureModes;
use vir::traits::DemoteTraitLookup;
use vir::well_formed::InitialWfResults;

/// Krate without the full functions (i.e., empty function list in the krate)
/// Instead we have FunctionOrConstInfos which contains FunctionStubs.
pub(crate) struct PreCrate<'tcx> {
    pub ctxt: Context<'tcx>,
    pub warning_ctx: WarningCtx,
    pub krate_without_funs: Krate,
    pub infos: Vec<Arc<FunctionOrConstInfo<'tcx>>>,
    pub fun_name_to_info: HashMap<Fun, Arc<FunctionOrConstInfo<'tcx>>>,
}

/// Used to guarantee that we emitted an error
#[derive(Clone, Copy)]
pub(crate) struct ErrorGuaranteed {
    _i_just_emitted_an_error: (),
}

pub(crate) type Res<T> = Result<T, ErrorGuaranteed>;

pub(crate) struct Query<'r, 'tcx> {
    args: Args,
    reporter: &'r dyn Diagnostics,

    /// Imported crates
    pub cache_other_vir_crates: Option<Res<Arc<Vec<Krate>>>>,
    /// Pre-crate before functions are lowered to VIR and checked in full
    pub cache_pre_crate: Option<Res<Arc<PreCrate<'tcx>>>>,
    /// Info used for demoting external traits
    pub cache_demote_traits_lookup: Option<Res<Arc<DemoteTraitLookup>>>,
    /// Info used for demoting external traits
    pub cache_initial_wf_results: Option<Res<InitialWfResults>>,
    /// All function stubs, across this crate and imported crates
    pub cache_all_function_stubs: Option<Res<Arc<HashMap<Fun, FunctionStub>>>>,
    /// Pre-check functions, immediately after translation from HIR
    pub cache_unchecked_functions: HashMap<Fun, Res<Function>>,
    /// Completed functions
    pub cache_checked_functions: HashMap<Fun, Res<(Function, Arc<ErasureModes>)>>,
    /// Complete krate, with all functions filled in
    pub cache_finished_crate: Option<Res<Krate>>,

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
    ) -> Self {
        Self {
            args,
            reporter,

            cache_other_vir_crates: Some(Ok(Arc::new(other_vir_crates))),
            cache_pre_crate: Some(Ok(Arc::new(pre_crate))),
            cache_demote_traits_lookup: None,
            cache_initial_wf_results: None,
            cache_all_function_stubs: None,
            cache_unchecked_functions: HashMap::new(),
            cache_checked_functions: HashMap::new(),
            cache_finished_crate: None,

            encountered_blocking_vir_error: false,
            encountered_non_blocking_vir_error: false,
            func_failed_proof_notes: HashMap::new(),
        }
    }

    fn emit_errors(&mut self, errs: Vec<VirErr>) -> ErrorGuaranteed {
        assert!(errs.len() > 0);
        self.encountered_blocking_vir_error = true;
        for err in errs {
            self.reporter.report_now(&err.to_any());
        }
        ErrorGuaranteed { _i_just_emitted_an_error: () }
    }

    fn emit_error(&mut self, err: VirErr) -> ErrorGuaranteed {
        self.emit_errors(vec![err])
    }

    fn handle_wf_error(&mut self, wf_err: vir::well_formed::WFErr) -> ErrorGuaranteed {
        todo!();
    }

    fn handle_per_function_check_results(
        &mut self,
        fun: &Fun,
        wf_res: vir::well_formed::PerFunctionCheckResults,
    ) {
        let vir::well_formed::PerFunctionCheckResults { func_failed_proof_notes } = wf_res;
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
                return Err(ErrorGuaranteed {});
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

    pub fn get_demote_traits_lookup(&mut self) -> Res<Arc<DemoteTraitLookup>> {
        if let Some(demote_traits_lookup) = &self.cache_demote_traits_lookup {
            return demote_traits_lookup.clone();
        }
        self.cache_demote_traits_lookup = Some(self._compute_demote_traits_lookup());
        self.cache_demote_traits_lookup.clone().unwrap()
    }

    pub fn _compute_demote_traits_lookup(&mut self) -> Res<Arc<DemoteTraitLookup>> {
        if let Some(demote_traits_lookup) = &self.cache_demote_traits_lookup {
            return demote_traits_lookup.clone();
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
        let other_vir_crates = self.get_other_vir_crates()?;
        let function_stubs = self.get_all_function_stubs()?;

        let (wf, non_blocking_errors, diags) = vir::well_formed::check_crate_initial(
            &pre_crate.krate_without_funs,
            &other_vir_crates,
            function_stubs.clone(),
            self.args.no_cheating,
        );
        self.emit_non_blocking_errors(non_blocking_errors);
        self.emit_diags(diags);
        wf.map_err(|e| self.handle_wf_error(e))
    }

    //// Translating an individual function

    pub fn get_unchecked_function(&mut self, fun: &Fun) -> Res<Function> {
        if let Some(f) = self.cache_unchecked_functions.get(fun) {
            return f.clone();
        }

        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;
        let info = &pre_crate.fun_name_to_info[fun];
        let mut new_functions = vec![];
        match finish_item(ctxt, &info, &mut new_functions) {
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

    pub fn get_checked_function(&mut self, fun: &Fun) -> Res<(Function, Arc<ErasureModes>)> {
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
    ) -> Result<(Function, Arc<ErasureModes>), ErrorGuaranteed> {
        let function = self.get_unchecked_function(fun)?;
        let lookup = self.get_demote_traits_lookup()?;

        let function = vir::traits::demote_external_traits_function_calls(&lookup, &function)
            .map_err(|e| self.emit_error(e))?;

        let wf = self.get_initial_wf_results()?;
        let function_stubs = self.get_all_function_stubs()?;
        let pre_crate = self.get_pre_crate()?;
        let (wf, non_blocking_errors, diags) = vir::well_formed::check_function(
            &pre_crate.krate_without_funs,
            function_stubs.clone(),
            wf.lookup.clone(),
            &function,
            &pre_crate.warning_ctx,
            self.args.no_cheating,
        );
        self.emit_non_blocking_errors(non_blocking_errors);
        self.emit_diags(diags);
        let wf = wf.map_err(|e| self.handle_wf_error(e))?;
        self.handle_per_function_check_results(fun, wf);

        todo!();
    }

    //// Getting the completed krate

    pub fn get_finished_crate(&mut self) -> Res<Krate> {
        let _ = self.get_initial_wf_results()?;
        let pre_crate = self.get_pre_crate()?;
        let mut cratex = (*pre_crate.krate_without_funs).clone();
        let mut found_err = None;
        for stub in pre_crate.infos.iter().map(|info| info.iter_stubs()).flatten() {
            match self.get_checked_function(&stub.x.name) {
                Ok((function, _)) => {
                    cratex.functions.push(function);
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

        let (check, diags) = vir::well_formed::check_crate_final(&krate, &pre_crate.warning_ctx);
        self.emit_diags(diags);
        let () = check.map_err(|e| self.emit_error(e))?;

        Ok(krate)
    }
}
