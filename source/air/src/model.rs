//! Provides an AIR-level interface to the model returned by the SMT solver
//! when it reaches a SAT conclusion

use crate::ast::{Decl, DeclX, Ident, Snapshots};
use crate::context::Context;
use crate::smt_util::new_const;
use std::collections::HashMap;
use std::fmt;
use z3::ast::Dynamic;

#[derive(Debug)]
/// AIR-level model of a concrete counterexample
pub struct Model<'a> {
    /// Handle to the original Z3 model; only for internal use, e.g., for `eval`
    z3_model: z3::Model<'a>,
    /// Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    /// Generated when converting mutable variables to Z3-level constants.
    id_snapshots: Snapshots,
    /// Externally facing mapping from snapshot IDs to snapshots that map AIR variables
    /// to their concrete values.
    /// TODO: Upgrade to a semantics-preserving value type, instead of String.
    value_snapshots: HashMap<Ident, HashMap<Ident, String>>,
}

impl<'a> Model<'a> {
    /// Returns an (unpopulated) AIR model object.  Must call [build()] to fully populate.
    /// # Arguments
    /// * `model` - The model that Z3 returns
    /// * `snapshots` - Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    pub fn new(model: z3::Model<'a>, snapshots: Snapshots) -> Model<'a> {
        // println!("Creating a new model with {} snapshots", snapshots.len());
        Model { z3_model: model, id_snapshots: snapshots, value_snapshots: HashMap::new() }
    }

    /// Convert a Z3 AST variable `var_stmt` into a String value
    /// Uses `var_name` only for error reporting.
    fn lookup_z3_var(&self, var_name: &String, var_smt: &Dynamic) -> String {
        if let Some(x) = self.z3_model.eval(var_smt) {
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
        }
    }

    /// Populate the AIR-level model based on the Z3 model
    /// `local_vars` should be a list of [DeclX::Const] values
    /// representing the function's local non-mutable variables
    /// (e.g., function parameters)
    /// This is decoupled from the Model's constructor so that
    /// we only do this expensive work when called in debug mode.
    pub fn build(&mut self, context: &mut Context, local_vars: Vec<Decl>) {
        println!("Building the AIR model");
        for (snap_id, id_snapshot) in &self.id_snapshots {
            let mut value_snapshot = HashMap::new();
            println!("Snapshot {} has {} variables", snap_id, id_snapshot.len());
            for (var_id, var_count) in &*id_snapshot {
                let var_name = crate::var_to_const::rename_var(&*var_id, *var_count);
                println!("\t{}", var_name);
                let var_smt = context
                    .vars
                    .get(&var_name)
                    .unwrap_or_else(|| panic!("internal error: variable {} not found", var_name));
                let val = self.lookup_z3_var(&var_name, var_smt);
                value_snapshot.insert(var_id.clone(), val);
            }
            // Add the local variables to every snapshot for uniformity
            println!("local_vars has {} variables", local_vars.len());
            for decl in local_vars.iter() {
                if let DeclX::Const(var_name, typ) = &**decl {
                    println!("\t{}", var_name);
                    let var_smt = new_const(context, &var_name, &typ);
                    let val = self.lookup_z3_var(&var_name, &var_smt);
                    value_snapshot.insert(var_name.clone(), val);
                    //value_snapshot.insert(Rc::new((*var_name).clone()), val);
                } else {
                    panic!("Expected local vars to all be constants at this point");
                }
            }
            self.value_snapshots.insert(snap_id.clone(), value_snapshot);
        }
    }

    /// Look up the value of an AIR variable `name` in a given `snapshot`
    pub fn query_variable(&self, snapshot: Ident, name: Ident) -> Option<String> {
        Some(self.value_snapshots.get(&snapshot)?.get(&name)?.to_string())
    }
}

impl<'a> fmt::Display for Model<'a> {
    /// Dump the contents of the AIR model for debugging purposes
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\nDisplaying model with {} snapshots\n", self.value_snapshots.len())?;
        for (snap_id, value_snapshot) in &self.value_snapshots {
            write!(f, "Snapshot <{}>:\n", snap_id)?;
            for (var_name, value) in &*value_snapshot {
                write!(f, "\t{} -> {}\n", var_name, value)?;
            }
        }
        Ok(())
    }
}
