use crate::ast::Ident;
use crate::def::rm_suffix_local_id;
use air::model::Model as AModel;
use std::collections::HashMap;

#[derive(Debug)]
pub struct Model<'a> {
    air_model: AModel<'a>,
    vir_snapshots: HashMap<Ident, HashMap<Ident, String>>,
    line_snapshots: HashMap<usize, HashMap<Ident, String>>,
}

impl<'a> Model<'a> {
    pub fn new(air_model: AModel<'a>) -> Model<'a> {
        let mut vir_snapshots = HashMap::new();

        for (snap_id, value_snapshot) in &air_model.value_snapshots {
            let mut vir_snapshot = HashMap::new();
            for (var_name, value) in &*value_snapshot {
                vir_snapshot.insert(rm_suffix_local_id(&var_name), value.clone());
            }
            vir_snapshots.insert(snap_id.clone(), vir_snapshot);
        }

        let line_snapshots = HashMap::new();
        Model { air_model, vir_snapshots, line_snapshots }
    }
}
