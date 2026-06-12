use std::{fmt::Write, path::Path};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

/// A list of toolchains.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolchainList {
    pub items: Vec<Toolchain>,
}

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

impl ToolchainList {
    /// Format the toolchain list as Rust code.
    pub fn format_code(&self, i0: Indent, out: &mut impl Write) -> std::fmt::Result {
        writeln!(out, "{i0}pub const TOOLCHAINS: [Toolchain; {}] = [", self.items.len())?;
        let i1 = i0.increase();
        for toolchain in &self.items {
            toolchain.format_code(i1, out)?;
            writeln!(out, ",")?;
        }
        writeln!(out, "{i0}];")?;
        Ok(())
    }

    /// Attempts to parse each `*.toml` file under `dir` as a toolchain manifest.
    pub fn parse_from_dir(dir: impl AsRef<Path>) -> Self {
        // TODO: Implement proper error handling.

        let dir = dir.as_ref();
        assert!(dir.is_dir());

        let mut items = Vec::<Toolchain>::new();
        for entry in std::fs::read_dir(dir).expect("read toolchain manifest directory") {
            let entry = entry.expect("read toolchain manifest directory entry");
            let path = entry.path();
            if !path.is_file() {
                continue;
            }
            if path.extension().is_none_or(|ext| ext != "toml") {
                continue;
            }

            let contents = std::fs::read_to_string(&path).expect("read toolchain manifest file");
            let toolchain = toml::from_str(&contents).expect("parse toolchain manifest file");
            items.push(toolchain);
        }

        // Sort entries *descending* by Verus version.
        items.sort_by(|a, b| b.verus.cmp(&a.verus));

        // Check for duplicate Verus versions.
        for (a, b) in items.iter().tuple_windows() {
            if a.verus == b.verus {
                panic!("duplicate Verus versions in toolchain manifests: {}", a.verus);
            }
        }

        ToolchainList { items }
    }
}

impl Toolchain {
    pub fn format_code(&self, i0: Indent, out: &mut impl Write) -> std::fmt::Result {
        let i1 = i0.increase();
        writeln!(out, "{i0}Toolchain {{")?;
        writeln!(out, "{i1}verus: {:?},", self.verus)?;
        writeln!(out, "{i1}vstd: {},", self.vstd)?;
        writeln!(out, "{i1}z3: {:?},", self.z3)?;
        write!(out, "{i0}}}")?;
        Ok(())
    }
}

impl std::fmt::Display for Crate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Crate::Version(version) => write!(f, "Crate::Registry {{ version: {version:?} }}")?,
            Crate::GitCommit { git, rev } => {
                write!(f, "Crate::GitCommit {{ git: {git:?}, rev: {rev:?} }}")?
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Indent(usize);

impl Default for Indent {
    fn default() -> Self {
        Indent(0)
    }
}

impl Indent {
    pub fn increase(&self) -> Self {
        Indent(self.0 + 4)
    }
}

impl std::fmt::Display for Indent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for _ in 0..self.0 {
            f.write_char(' ')?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
