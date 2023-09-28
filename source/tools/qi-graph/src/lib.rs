use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    path::Path,
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
    pub graph: Graph<Instantiation, ()>,
}

impl<N: PartialEq + Eq + std::hash::Hash, E: PartialEq + Eq + std::hash::Hash> Graph<N, E> {
    pub fn to_dot_file(
        &self,
        path: &Path,
        node_name: impl Fn(&N) -> String,
        edge_label: impl Fn(&E) -> Option<String>,
    ) -> Result<(), String> {
        let Graph(edges) = self;
        use std::io::Write;

        let mut file = std::fs::File::create(path).expect("couldn't create dot file");
        fn io_err_string<V>(o: Result<V, std::io::Error>) -> Result<V, String> {
            o.map_err(|err| format!("i/o failed: {}", err))
        }

        io_err_string(writeln!(&mut file, "digraph M {{"))?;
        io_err_string(writeln!(&mut file, "  rankdir=LR;"))?;
        for (src, src_edges) in edges.iter() {
            for (edge, tgt) in src_edges {
                io_err_string(write!(
                    &mut file,
                    "  \"{}\" -> \"{}\" ",
                    node_name(src),
                    node_name(tgt)
                ))?;
                if let Some(lbl) = edge_label(edge) {
                    io_err_string(write!(&mut file, "[ label = \"{}\" ]", lbl))?;
                }
                io_err_string(writeln!(&mut file, ";"))?;
            }
        }
        io_err_string(writeln!(&mut file, "}}"))?;
        Ok(())
    }
}
