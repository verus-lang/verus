use std::collections::{HashMap};
use std::fmt;
//use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use crate::ast::{Ident,SnapShots};
use crate::context::Context;
//use z3::ast::Dynamic;
//use z3::{FuncDecl, Sort};

#[derive(Debug)]
pub(crate) struct Model<'a> {
    z3_model: z3::Model<'a>,
    id_snapshots: SnapShots,
    value_snapshots: HashMap<Ident, HashMap<Ident, String>>
}


impl<'a> Model<'a> {
    pub fn new(model: z3::Model<'a>, snapshots:SnapShots) -> Model<'a> {
        Model {
            z3_model: model,
            id_snapshots: snapshots,
            value_snapshots: HashMap::new(),
        }
    }

//    pub fn save_snapshots(&self, snapshots: SnapShots) {
//        self.snapshots = snapshots.clone();
//    }

    /// Reconstruct an AIR-level model based on the Z3 model
    pub fn build(&self, context: &Context) {
        for (snap_id, id_snapshot) in &self.id_snapshots {
            let value_snapshot = HashMap::new();
            for (var_id, var_count) in *id_snapshot {
                let var_name = crate::var_to_const::rename_var(&*var_id, var_count);
                let var_smt = context.vars.get(&var_name).unwrap_or_else(|| panic!("internal error: variable {} not found", var_name));
                let val = if let Some(x) = self.z3_model.eval(var_smt) {
                    if let Some(b) = x.as_bool() {
                        format!("{}", b)
                    } else if let Some(i) = x.as_int() {
                        format!("{}", i)
                    } else {
                        println!("Unexpected type returned from model eval for {}", var_name);
                        "".to_string()
                    }
                } else {
                    println!("Failed to extract evaluation of var {} from Z3's model", var_name);
                    "".to_string()
                };
                value_snapshot.insert(Rc::new(var_name), val);
            }
            self.value_snapshots.insert(*snap_id, value_snapshot);
        }
    }

    pub fn query_variable(&self, snapshot: Ident, name:Ident) -> Option<String> {
        Some(self.value_snapshots.get(&snapshot)?.get(&name)?.to_string())
    }
}

impl<'a> fmt::Display for Model<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (snap_id, value_snapshot) in &self.value_snapshots {
            write!(f, "Snapshot: {}:\n", snap_id)?;
            for (var_name, value) in *value_snapshot {
                write!(f, "\t{} -> {}", var_name, value)?;
            }
        }
        Ok(())
    }
}

