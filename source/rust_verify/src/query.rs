use crate::config::Args;
use crate::context::Context;
use crate::external::CrateItems;
use crate::import_export::ImportOutput;
use crate::rust_to_vir_func::FunctionOrConstInfo;
use crate::rust_to_vir_func::finish_item;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Fun, Function, FunctionStub, Krate, VirErr};
use vir::context::WarningCtx;
use vir::modes::ErasureModes;
use vir::traits::DemoteTraitLookup;

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

    /// Imported crates
    pub cache_other_vir_crates: Option<Res<Arc<Vec<Krate>>>>,
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
    pub fn new(args: Args, other_vir_crates: Vec<Krate>, pre_crate: PreCrate<'tcx>) -> Self {
        Self {
            args,

            cache_other_vir_crates: Some(Ok(Arc::new(other_vir_crates))),
            cache_pre_crate: Some(Ok(Arc::new(pre_crate))),
            cache_demote_traits_lookup: None,
            cache_all_function_stubs: None,
            cache_unchecked_functions: HashMap::new(),
            cache_checked_functions: HashMap::new(),
            cache_finished_crate: None,

            encountered_vir_error: false,
        }
    }

    fn emit_errors(&mut self, err: Vec<VirErr>) -> ErrorGuaranteed {
        todo!()
        //Err(ErrorGuaranteed{})
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
        let duplicate_err = |stub: &FunctionStub, s: &mut Self| {
            let err = vir::messages::error(
                &stub.span,
                format!(
                    "duplicate function entry: {:}",
                    vir::ast_util::fun_as_friendly_rust_name(&stub.x.name)
                ),
            );
            Err(s.emit_errors(vec![err]))
        };

        // combine all the function stubs from our crate and the external crates
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        let mut stubs = HashMap::new();
        for stub in pre_crate.infos.iter().map(|info| info.iter_stubs()).flatten() {
            let found = stubs.insert(stub.x.name.clone(), stub.clone());
            if found.is_some() {
                return duplicate_err(stub, self);
            }
        }
        for krate in other_vir_crates.iter() {
            for function in krate.functions.iter() {
                let stub = vir::ast_util::function_to_stub(function);
                let found = stubs.insert(stub.x.name.clone(), stub.clone());
                if found.is_some() {
                    return duplicate_err(&stub, self);
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
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        let function_stubs = self.get_all_function_stubs()?;
        vir::traits::DemoteTraitLookup::new(
            &pre_crate.krate_without_funs,
            &other_vir_crates,
            &function_stubs,
        );

        todo!()
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
                let err = Err(self.emit_errors(vec![err]));
                for stub in info.iter_stubs() {
                    let found = self
                        .cache_unchecked_functions
                        .insert(stub.x.name.clone(), Err(ErrorGuaranteed {}));
                    assert!(found.is_none());
                }
                err
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
            .map_err(|e| self.emit_errors(vec![e]))?;

        todo!();
    }

    //// Getting the completed krate

    pub fn get_finished_crate(&mut self) -> Res<Krate> {
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
        Ok(Arc::new(cratex))
    }
}
