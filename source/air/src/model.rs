//! Provides an AIR-level interface to the model returned by the SMT solver
//! when it reaches a SAT conclusion

use crate::ast::{Binders, Decl, DeclX, Ident, Snapshots, Typ};
use crate::context::Context;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

/// For now, expressions are just strings, but we can later change this to a more detailed enum
pub type ModelExpr = Arc<String>;

/// Represent (define-fun f (...parameters...) return-type body) from SMT model
/// (This includes constants, which have an empty parameter list.)
pub type ModelDef = Arc<ModelDefX>;
pub type ModelDefs = Arc<Vec<ModelDef>>;
#[derive(Debug)]
pub struct ModelDefX {
    pub name: Ident,
    pub params: Binders<Typ>,
    pub ret: Typ,
    pub body: ModelExpr,
}

#[derive(Debug)]
/// AIR-level model of a concrete counterexample
pub struct Model {
    /// Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    /// Generated when converting mutable variables to Z3-level constants.
    id_snapshots: Snapshots,
    /// Externally facing mapping from snapshot IDs to snapshots that map AIR variables
    /// to their concrete values.
    /// TODO: Upgrade to a semantics-preserving value type, instead of String.
    /// TODO: Expose via a more abstract interface
    pub value_snapshots: HashMap<Ident, HashMap<Ident, String>>,
}

impl Model {
    /// Returns an (unpopulated) AIR model object.  Must call [build()] to fully populate.
    /// # Arguments
    /// * `model` - The model that Z3 returns
    /// * `snapshots` - Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    pub fn new(snapshots: Snapshots) -> Model {
        // println!("Creating a new model with {} snapshots", snapshots.len());
        Model { id_snapshots: snapshots, value_snapshots: HashMap::new() }
    }

    /// Convert a Z3 AST variable `var_stmt` into a String value
    /// Uses `var_name` only for error reporting.
    fn lookup_z3_var(&self, context: &mut Context, var_name: &String) -> String {
        context.smt_log.log_eval(Arc::new(var_name.clone()));
        let smt_output =
            context.smt_manager.get_smt_process().send_commands(context.smt_log.take_pipe_data());
        if smt_output.len() != 1 {
            panic!("unexpected output from SMT eval {:?}", &smt_output);
        }
        smt_output[0].clone()
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
                let val = self.lookup_z3_var(context, &var_name);
                value_snapshot.insert(var_id.clone(), val);
            }
            // Add the local variables to every snapshot for uniformity
            println!("local_vars has {} variables", local_vars.len());
            for decl in local_vars.iter() {
                if let DeclX::Const(var_name, _typ) = &**decl {
                    println!("\t{}", var_name);
                    let val = self.lookup_z3_var(context, &var_name);
                    value_snapshot.insert(var_name.clone(), val);
                    //value_snapshot.insert(Arc::new((*var_name).clone()), val);
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

impl fmt::Display for Model {
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
