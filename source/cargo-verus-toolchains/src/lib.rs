use serde::{Deserialize, Serialize};

/// A set of Verus components meant to be used together.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Toolchain {
    /// The Verus version; the primary key to identify a toolchain.
    pub verus: String,
    /// The vstd version.
    pub vstd: Crate,
    /// The Z3 version.
    pub z3: String,
}

/// Identifies a crate in a registry (i.e. crates.io) or git.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Crate {
    /// A version published in a registry.
    Version(String),
    /// A commit in a git repository (e.g. GitHub).
    GitCommit { git: String, rev: String },
}

#[cfg(test)]
mod tests;
