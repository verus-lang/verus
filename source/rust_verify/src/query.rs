use crate::config::Args;
use crate::context::Context;
use crate::import_export::ImportOutput;
use crate::rust_to_vir_func::FunctionOrConstInfo;
use crate::rust_to_vir_func::finish_item;
use vir::ast::{FunctionStub, Krate, Fun, Function, VirErr};
use vir::context::WarningCtx;
use vir::traits::DemoteTraitLookup;
use std::sync::Arc;
use crate::external::CrateItems;
use std::collections::HashMap;
use vir::modes::ErasureModes;

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
pub(crate) struct ErrorGuaranteed {}

pub(crate) type Res<T> = Result<T, ErrorGuaranteed>;

pub(crate) struct Query<'tcx> {
    args: Args,
    import_virs_via_cargo: Vec<(String, String)>,
    crate_items: Arc<CrateItems>,
    ctxtx: Option<crate::context::ContextX<'tcx>>,
    compiler: &'tcx rustc_interface::interface::Compiler,

    /// Imported crates
    pub cache_imported: Option<Res<Arc<ImportOutput>>>,
    /// Pre-crate before functions are lowered to VIR and checked in full
    pub cache_pre_crate: Option<Res<Arc<PreCrate<'tcx>>>>,
    /// Info used for demoting external traits
    pub cache_demote_traits_lookup: Option<Res<Arc<DemoteTraitLookup>>>,
    /// All function stubs, across this crate and imported crates
    pub cache_all_function_stubs: Option<Res<Arc<HashMap<Fun, FunctionStub>>>>,
    /// Pre-check functions, immediately after translation from HIR
    pub cache_unchecked_functions: HashMap<Fun, Res<Function>>,
    /// Completed functions
    pub cache_checked_functions: HashMap<Fun, Res<(Function, Arc<ErasureModes>)>>,
    /// Complete krate, with all functions filled in
    pub cache_finished_crate: Option<Res<Krate>>,

    /// Errors found along the way
    pub encountered_vir_error: bool,
}

impl<'tcx> Query<'tcx> {
    fn new() -> Self {
        todo!()
    }

    fn emit_errors<T>(&mut self, err: Vec<VirErr>) -> Result<T, ErrorGuaranteed> {
        todo!()
        //Err(ErrorGuaranteed{})
    }

    //// Import crate

    pub fn get_imported(&mut self) -> Res<Arc<ImportOutput>> {
        if let Some(imported) = &self.cache_imported {
            return imported.clone();
        }
        self.cache_imported = Some(self._compute_imported());
        self.cache_imported.clone().unwrap()
    }

    fn _compute_imported(&mut self) -> Res<Arc<ImportOutput>> {
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
    }

    //// Pre-crate

    pub fn get_pre_crate(&mut self) -> Res<Arc<PreCrate<'tcx>>> {
        if let Some(pre_crate) = &self.cache_pre_crate {
            return pre_crate.clone();
        }
        self.cache_pre_crate = Some(self._compute_pre_crate());
        self.cache_pre_crate.clone().unwrap()
    }

    fn _compute_pre_crate(&mut self) -> Res<Arc<PreCrate<'tcx>>> {
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
    }

    //// DemoteTraitsLookup

    fn get_demote_traits_lookup(&mut self) -> Res<Arc<DemoteTraitLookup>> {
        if let Some(demote_traits_lookup) = &self.cache_demote_traits_lookup {
            return demote_traits_lookup.clone();
        }
        let imported = self.get_imported()?;
        let pre_crate = self.get_pre_crate()?;
        // need to modify DemoteTraitLookup::new to work with the information we have
        todo!()
    }

    fn get_all_function_stubs(&mut self) -> Res<Arc<HashMap<Fun, FunctionStub>>> {
        if let Some(all_function_stubs) = &self.cache_all_function_stubs {
            return all_function_stubs.clone();
        }
        let imported = self.get_imported()?;
        let pre_crate = self.get_pre_crate()?;
        // combine all the function stubs from our crate and the external crates
        todo!()
    }

    //// Translating an individual function

    fn get_unchecked_function(&mut self, fun: &Fun) -> Res<Function> {
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
                    let found = self.cache_unchecked_functions.insert(new_function.x.name.clone(), Ok(new_function));
                    assert!(found.is_none());
                }
                // Sanity check we got all the functions we expected
                for stub in info.iter_stubs() {
                    assert!(self.cache_unchecked_functions.contains_key(&stub.x.name));
                }
                self.cache_unchecked_functions.get(fun).unwrap().clone()
            }
            Err(err) => {
                self.compiler.sess.dcx().err(err.note.clone());
                self.encountered_vir_error = true;
                for stub in info.iter_stubs() {
                    let found = self.cache_unchecked_functions.insert(stub.x.name.clone(), Err(ErrorGuaranteed {}));
                    assert!(found.is_none());
                }
                Err(ErrorGuaranteed {})
            }
        }
    }

    //// Checking an individual function

    fn get_checked_function(&mut self, fun: &Fun) -> Res<(Function, Arc<ErasureModes>)> {
        if let Some(f) = self.cache_checked_functions.get(fun) {
            return f.clone();
        }
        let res = self._compute_checked_function(fun);
        self.cache_checked_functions.insert(fun.clone(), res.clone());
        res
    }

    fn _compute_checked_function(&mut self, fun: &Fun) -> Res<(Function, Arc<ErasureModes>)> {
        todo!()
    }

    //// Getting the completed krate

    fn get_finished_crate(&mut self) -> Res<Krate> {
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
        Ok(Arc::new(cratex))
    }
}
