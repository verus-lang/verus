use crate::rust_to_vir_func::FunctionInfo;
use crate::import_export::ImportOutput;
use vir::ast::FunctionStub;

/// Krate without the full functions (i.e., empty function list in the krate)
/// Instead we have FunctionInfos which contains FunctionStubs.
struct PreCrate {
    krate_without_funs: Option<Arc<Krate>>,
    function_infos: Vec<FunctionInfo>,
}

/// Used to guarantee that we emitted an error
pub struct ErrorGuaranteed{}

type Res<T> = Result<T, ErrorGuaranteed>

struct Query {
    /// Imported crates
    pub imported: Option<Res<Arc<ImportOutput>>>,
    /// Pre-crate before functions are lowered to VIR and checked in full
    pub pre_crate: Option<Res<Arc<PreCrate>>>,
    /// Info used for demoting external traits
    pub demote_traits_lookup: Option<Res<Arc<DemoteTraitLookup>>>,
    /// All function stubs, across this crate and imported crates
    pub all_function_stubs: Option<Res<Arc<HashMap<Fun, FunctionStub>>>>,
    /// Completed functions
    pub functions: HashMap<Fun, Res<(Function, Arc<ErasureModes>)>>,
    /// Complete krate, with all functions filled in
    pub finished_crate: Option<Res<Krate>>,

    /// Errors found along the way
    // TODO: plus diagnostics, etc.
    pub errors: Vec<VirErr>,
}


impl Query {
    fn get_imported(&mut self) -> Res<Arc<ImportOutput>> {
        if let Some(imported) = &self.imported {
            return Ok(imported.clone());
        }
        todo!()
    }

    fn get_pre_crate(&mut self) -> Res<Arc<PreCrate>> {
        if let Some(pre_crate) = &self.pre_crate {
            return Ok(pre_crate.clone());
        }
        todo!()
    }

    fn get_demote_traits_lookup(&mut self) -> Res<Arc<DemoteTraitLookup>> {
        if let Some(demote_traits_lookup) = &self.demote_traits_lookup {
            return Ok(demote_traits_lookup.clone());
        }
        let imported = self.get_imported()?;
        let pre_crate = self.get_pre_crate()?;
        todo!()
    }

    fn get_all_function_stubs(&mut self) -> Res<Arc<HashMap<Fun, FunctionStub>>> {
        if let Some(all_function_stubs) = &self.all_function_stubs {
            return Ok(all_function_stubs.clone());
        }
        let imported = self.get_imported()?;
        let pre_crate = self.get_pre_crate()?;
        todo!()
    }

    fn get_checked_function(&mut self, fun: &Fun) -> Res<(Function, Arc<ErasureModes>)> {
        match self.functions.entry(fun) {
            Entry::Occupied(occupied_entry) => todo!()
            Entry::Vacant(vacant_entry) => {
                // Demote foreign traits
                // autospec
                // well_formed checks
                // mode-checking
            }
        }
    }

    fn get_finished_crate(&mut self) -> Res<Krate> {
        todo!()
    }
}
