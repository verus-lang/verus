use crate::ast::Ident;
use crate::def::rm_suffix_local_id;
use air::model::Model as AModel;
use std::collections::HashMap;

#[derive(Debug)]
/// VIR-level model of a concrete counterexample
pub struct Model {
    /// Handle to the AIR-level model; only for internal use, e.g., for `eval`
    air_model: AModel,
    /// Internal mapping from snapshot IDs to snapshots that map VIR variables to values
    /// TODO: Upgrade to a semantics-preserving value type, instead of String.
    vir_snapshots: HashMap<Ident, HashMap<Ident, String>>,
}

impl Model {
    pub fn new(air_model: AModel) -> Model {
        let mut vir_snapshots = HashMap::new();

        for (snap_id, value_snapshot) in &air_model.value_snapshots {
            let mut vir_snapshot = HashMap::new();
            for (var_name, value) in &*value_snapshot {
                vir_snapshot.insert(rm_suffix_local_id(&var_name), value.clone());
            }
            vir_snapshots.insert(snap_id.clone(), vir_snapshot);
        }

        Model { air_model, vir_snapshots }
    }

    /// Look up the value of a VIR variable `name` in a given `snapshot`
    pub fn query_variable(&self, snapshot: Ident, name: Ident) -> Option<String> {
        Some(self.vir_snapshots.get(&snapshot)?.get(&name)?.to_string())
    }
}
