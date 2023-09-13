//! Provides an AIR-level interface to the model returned by the SMT solver
//! when it reaches a SAT conclusion

use crate::ast::{Binders, Decl, DeclX, Ident, Snapshots, Typ};
use std::collections::HashSet;
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

#[derive(Clone, Debug)]
/// AIR-level model of a concrete counterexample
pub struct Model {
    /// Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    /// Generated when converting mutable variables to Z3-level constants.
    id_snapshots: Snapshots,
    /// The list of paramters of the function
    parameters: HashSet<Ident>,
}

impl Model {
    /// Returns an (unpopulated) AIR model object.  Must call [build()] to fully populate.
    /// # Arguments
    /// * `model` - The model that Z3 returns
    /// * `snapshots` - Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    pub fn new(snapshots: Snapshots, params: Vec<Decl>) -> Model {
        // println!("Creating a new model with {} snapshots", snapshots.len());
        // for (sid, snapshot) in &snapshots {
        //     println!("{:?}", sid);
        //     for (name, num) in snapshot {
        //         println!("{:?} {}", name, num);
        //     }
        // }

        let mut parameters = HashSet::new();
        for param in params {
            if let DeclX::Const(name, _) = &*param {
                parameters.insert(name.clone());
            }
        }

        Model { id_snapshots: snapshots, parameters }
    }

    pub fn translate_variable(&self, sid: &Ident, name: &Ident) -> Option<String> {
        // look for variable in the snapshot first
        let id_snapshot = &self.id_snapshots.get(sid)?;
        if let Some(var_label) = id_snapshot.get(name) {
            return Some(crate::var_to_const::rename_var(name, *var_label));
        }
        // then look in the parameter list
        if self.parameters.contains(name) {
            return Some((**name).clone());
        }
        None
    }
}
