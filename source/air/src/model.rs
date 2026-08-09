//! Provides an AIR-level interface to the model returned by the SMT solver
//! when it reaches a SAT conclusion

use crate::ast::{Binders, Decl, DeclX, Ident, Snapshots, Typ};
use std::collections::{HashMap, HashSet};
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
    /// Every zero-parameter `(define-fun name () type body)` from Z3's raw
    /// `(get-model)` dump - i.e. plain constants, exactly what an
    /// already-incarnated variable (`x@3`) is. Populated once, at the same
    /// point the model is originally parsed (`smt_verify::smt_get_model`).
    ///
    /// This exists so a caller can read a variable's concrete value
    /// directly off the returned `Model`, instead of issuing a *separate*
    /// `Context::eval_expr` call afterward - which is unsound here: getting
    /// a model triggers a "disable this label" `(assert ...)` to be queued
    /// for the *next* batch of commands sent to the solver (so a later
    /// `check-sat` finds additional errors), and that queued assert reaches
    /// Z3 before any subsequent `eval_expr` call's own command does,
    /// invalidating the model Z3 just produced (`(error "model is not
    /// available")`) - confirmed by hitting exactly this in practice, not
    /// guessed. Reading straight from `raw_values` (captured before that
    /// assert is ever queued) sidesteps the ordering hazard entirely.
    raw_values: HashMap<Ident, ModelExpr>,
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

        Model { id_snapshots: snapshots, parameters, raw_values: HashMap::new() }
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

    /// Populates `raw_values` from every zero-parameter model definition -
    /// called once, right where the model is parsed from Z3's raw output
    /// (see the field's doc comment for why this can't be done lazily via a
    /// later `eval_expr` call instead).
    pub fn set_raw_values(&mut self, defs: &[ModelDef]) {
        for def in defs {
            if def.params.is_empty() {
                self.raw_values.insert(def.name.clone(), def.body.clone());
            }
        }
    }

    /// The concrete value Z3 assigned a plain constant (e.g. an
    /// already-incarnated variable like `x@3`), if this model has one.
    pub fn raw_value(&self, name: &Ident) -> Option<&str> {
        self.raw_values.get(name).map(|v| v.as_str())
    }
}
