use crate::config::Args;
use crate::context::Context;
use crate::import_export::ImportOutput;
use crate::rust_to_vir_func::FunctionOrConstInfo;
use crate::rust_to_vir_func::finish_item;
use vir::ast::FunctionStub;
use vir::ast::Krate;
use vir::context::WarningCtx;

/// Krate without the full functions (i.e., empty function list in the krate)
/// Instead we have FunctionOrConstInfos which contains FunctionStubs.
pub struct PreCrate<'tcx> {
    pub ctxt: Context<'tcx>,
    pub warning_ctx: WarningCtx,
    pub krate_without_funs: Krate,
    pub function_infos: Vec<FunctionOrConstInfo<'tcx>>,
}

/// Used to guarantee that we emitted an error
pub struct ErrorGuaranteed {}

type Res<T> = Result<T, ErrorGuaranteed>;

struct Query<'tcx> {
    args: Args,
    import_virs_via_cargo: Option<Vec<(String, String)>>,
    crate_items: Arc<CrateItems>,
    ctxtx: Option<ContextX>,

    /// Imported crates
    pub imported: Option<Res<Arc<ImportOutput>>>,
    /// Pre-crate before functions are lowered to VIR and checked in full
    pub pre_crate: Option<Res<Arc<PreCrate<'tcx>>>>,
    /// Info used for demoting external traits
    pub demote_traits_lookup: Option<Res<Arc<DemoteTraitLookup>>>,
    /// All function stubs, across this crate and imported crates
    pub all_function_stubs: Option<Res<Arc<HashMap<Fun, FunctionStub>>>>,
    /// Pre-check functions, immediately after translation from HIR
    pub unchecked_functions: HashMap<Fun, Res<Function>>,
    /// Completed functions
    pub checked_functions: HashMap<Fun, Res<(Function, Arc<ErasureModes>)>>,

    /// Complete krate, with all functions filled in
    pub finished_crate: Option<Res<Krate>>,

    /// Errors found along the way
    pub encountered_vir_error: bool,
}

impl Query {
    fn new() -> Self {}

    //// Import crate

    pub fn get_imported(&mut self) -> Res<Arc<ImportOutput>> {
        if let Some(imported) = &self.imported {
            return Ok(imported.clone());
        }
        self.imported = Some(self.compute_imported());
        Ok(self.imported.unwrap())
    }

    fn compute_imported(&mut self) -> Res<Arc<ImportOutput>> {
        match crate::import_export::import_crates(&self.args, self.import_virs_via_cargo.clone()) {
            Ok(imported) => Ok(imported),
            Err(err) => {
                assert!(err.spans.len() == 0);
                assert!(err.level == MessageLevel::Error);
                compiler.sess.dcx().err(err.note.clone());
                self.encountered_vir_error = true;
                return Err(ErrorGuaranteed {});
            }
        }
    }

    //// Pre-crate

    pub fn get_pre_crate(&mut self) -> Res<Arc<PreCrate>> {
        if let Some(pre_crate) = &self.pre_crate {
            return Ok(pre_crate.clone());
        }

        Ok(self.pre_crate.unwrap())
    }

    fn compute_pre_crate(&mut self) -> Res<Arc<PreCrate>> {
        let mut ctxtx = None;
        mem::swap(&mut self.ctxtx, &mut ctxtx);
        let pre_crate =
            crate::rust_to_vir::crate_to_vir(ctxtx.unwrap(), &imported, &self.crate_items)?;
        Ok(pre_crate)
    }

    //// DemoteTraitsLookup

    fn get_demote_traits_lookup(&mut self) -> Res<Arc<DemoteTraitLookup>> {
        if let Some(demote_traits_lookup) = &self.demote_traits_lookup {
            return Ok(demote_traits_lookup.clone());
        }
        let imported = self.get_imported()?;
        let pre_crate = self.get_pre_crate()?;
        // need to modify DemoteTraitLookup::new to work with the information we have
        todo!()
    }

    fn get_all_function_stubs(&mut self) -> Res<Arc<HashMap<Fun, FunctionStub>>> {
        if let Some(all_function_stubs) = &self.all_function_stubs {
            return Ok(all_function_stubs.clone());
        }
        let imported = self.get_imported()?;
        let pre_crate = self.get_pre_crate()?;
        // combine all the function stubs from our crate and the external crates
        todo!()
    }

    //// Translating an individual function

    fn get_unchecked_function(&mut self, fun: &Fun) -> Res<Function> {
        if let Some(f) = self.unchecked_functions.get(fun) {
            return f.clone();
        }

        let pre_crate = self.get_pre_crate();
        let info = &compute_pre_crate.fun_name_to_info[fun];
        let mut new_functions = vec![];
        match finish_item(&ctxt, info.clone(), &mut new_functions) {
            Ok(()) => {
                for new_function in new_functions.into_iter() {
                    self.unchecked_functions.insert(new_function.x.name.clone(), new_function);
                }
                Ok(self.unchecked_functions.get(fun).unwrap().clone())
            }
            Err(err) => {
                compiler.sess.dcx().err(err.note.clone());
                self.encountered_vir_error = true;
                for stub in info.iter() {
                    self.unchecked_functions.insert(stub.x.name.clone(), Err(ErrorGuaranteed {}));
                }
                Err(ErrorGuaranteed {})
            }
        }
    }

    //// Checking an individual function

    fn get_checked_function(&mut self, fun: &Fun) -> Res<(Function, Arc<ErasureModes>)> {
        if let Some(f) = self.unchecked_functions.get(fun) {
            return f.clone();
        }
        let res = self.compute_checked_function(fun);
        self.unchecked_functions.insert(fun.clone(), res.clone());
        res
    }

    fn compute_checked_function(&mut self, fun: &Fun) -> Res<(Function, Arc<ErasureModes>)> {}

    //// Getting the completed krate

    fn get_finished_crate(&mut self) -> Res<Krate> {
        let pre_crate = self.get_pre_crate()?;
        let mut cratex = (*pre_crate.krate_without_funs).clone();
        for stub in pre_crate.infos.iter().flatten() {
            let function = self.get_checked_function(&stub.x.name)?;
            cratex.functions.push(function);
        }
        Ok(Arc::new(cratex))
    }
}
