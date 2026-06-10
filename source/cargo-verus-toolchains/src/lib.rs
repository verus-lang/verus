use serde::{Deserialize, Serialize};

/// A collection of Verus components meant to be used together.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Toolchain {
    /// The Verus version; the primary key to identify a toolchain.
    pub verus: String,
    /// The vstd version.
    pub vstd: Crate,
    /// The Z3 version.
    pub z3: String,
}

/// The version of a crate in a registry (usually crates.io) or on git.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Crate {
    /// Identifies a version published in a registry.
    Simple(String),
    /// Identifies a commit in a git repository (e.g. GitHub).
    Git { git: String, rev: String },
}

#[cfg(test)]
mod tests;
