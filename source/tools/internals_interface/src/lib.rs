use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UserQuantifier {
    pub span: String,
}

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum QuantifierKind {
    Internal,
    User(UserQuantifier),
}

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QuantifierX {
    pub qid: String,
    pub module: Option<String>,
    pub kind: QuantifierKind,
}
pub type Quantifier = Rc<QuantifierX>;

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InstantiationX {
    pub quantifier: Quantifier,
    pub id: (u64, usize),
}
pub type Instantiation = Rc<InstantiationX>;

#[derive(Serialize, Deserialize)]
pub struct Graph<N: PartialEq + Eq + std::hash::Hash, E: PartialEq + Eq + std::hash::Hash>(
    pub HashMap<N, HashSet<(E, N)>>,
);

#[derive(Serialize, Deserialize)]
pub struct InstantiationGraph {
    pub bucket_name: String,
    pub module: String,
    pub function: Option<String>,
    pub quantifiers: HashSet<Quantifier>,
    pub instantiations: HashSet<Instantiation>,
    pub graph: Graph<Instantiation, ()>,
}

impl InstantiationGraph {
    pub fn serialize(&self, w: impl std::io::Write) -> Result<(), String> {
        bincode::serialize_into(w, self).map_err(|x| x.to_string())
    }

    pub fn deserialize(r: impl std::io::Read) -> Result<Self, String> {
        bincode::deserialize_from(r).map_err(|x| x.to_string())
    }
}
