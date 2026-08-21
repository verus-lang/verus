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
    /// Every zero-parameter constant from Z3's raw model dump. Read this instead of a
    /// later `eval_expr` call, which can invalidate the model first.
    raw_values: HashMap<Ident, ModelExpr>,
    /// Every function definition from the same dump, parameterized or not.
    raw_defs: HashMap<Ident, ModelDef>,
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

        Model {
            id_snapshots: snapshots,
            parameters,
            raw_values: HashMap::new(),
            raw_defs: HashMap::new(),
        }
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

    /// Populates `raw_values`/`raw_defs` from Z3's raw model dump.
    pub fn set_raw_values(&mut self, defs: &[ModelDef]) {
        for def in defs {
            if def.params.is_empty() {
                self.raw_values.insert(def.name.clone(), def.body.clone());
            }
            self.raw_defs.insert(def.name.clone(), def.clone());
        }
    }

    /// The concrete value Z3 assigned a plain constant, if any.
    pub fn raw_value(&self, name: &Ident) -> Option<&str> {
        self.raw_values.get(name).map(|v| v.as_str())
    }

    /// A function's model definition, found by matching the tail of its AIR name (e.g.
    /// `"add_one.?"` for `"my_crate!add_one.?"`) rather than requiring the caller to
    /// know the full, crate-qualified name. Requires a `.`/`!` boundary right before the
    /// match (so `"add_one.?"` can't match a name like `"xadd_one.?"`), and returns
    /// `None` rather than an arbitrary pick if more than one name matches.
    pub fn find_def_by_suffix(&self, suffix: &str) -> Option<&ModelDefX> {
        let mut matches = self.raw_defs.iter().filter(|(name, _)| {
            name.strip_suffix(suffix)
                .is_some_and(|prefix| prefix.is_empty() || prefix.ends_with(['.', '!']))
        });
        let (_, def) = matches.next()?;
        if matches.next().is_some() { None } else { Some(&**def) }
    }
}
