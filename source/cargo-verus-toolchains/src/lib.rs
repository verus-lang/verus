use std::{
    fmt::{Debug, Write},
    path::Path,
};

use anyhow::Context;
use itertools::Itertools;
use serde::{Deserialize, Serialize};

/// A list of toolchains.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolchainList {
    pub items: Vec<Toolchain>,
}

/// Format a toolchain manifest similar to a Cargo.toml file's [dependencies] section.
pub fn format_manifest(toolchain: &Toolchain) -> anyhow::Result<String> {
    use toml_edit::{DocumentMut, Item, Value};

    let value = toolchain
        .serialize(toml_edit::ser::ValueSerializer::new())
        .context("serialize manifest")?;

    let Value::InlineTable(table) = value else {
        anyhow::bail!("toolchain should serialize to an inline table");
    };

    let mut doc = DocumentMut::new();
    for (key, value) in table {
        doc.insert(&key, Item::Value(value));
    }

    Ok(doc.to_string())
}

/// A set of Verus components meant to be used together.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Toolchain<Str: AsRef<str> = String> {
    /// The Verus version; the primary key to identify a toolchain.
    pub verus: Str,
    /// The vstd version.
    pub vstd: Crate<Str>,
    /// The Z3 version.
    pub z3: Str,
    /// The Singular version.
    pub singular: Str,
}

/// Identifies a crate in a registry (i.e. crates.io) or git.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Crate<Str: AsRef<str> = String> {
    /// A version published in a registry.
    Registry(/*version*/ Str),
    /// A commit in a git repository (e.g. GitHub).
    GitCommit { git: Str, rev: Str },
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

        write!(out, "{i1}vstd: ")?;
        self.vstd.format_code(out)?;
        writeln!(out, ",")?;

        writeln!(out, "{i1}z3: {:?},", self.z3)?;

        writeln!(out, "{i1}singular: {:?},", self.singular)?;

        write!(out, "{i0}}}")?;
        Ok(())
    }
}

impl<Str: AsRef<str>> std::fmt::Display for Crate<Str> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Crate::Registry(version) => write!(f, "{:?}", version.as_ref())?,
            Crate::GitCommit { git, rev } => {
                write!(f, "{{ git = {:?}, rev = {:?} }}", git.as_ref(), rev.as_ref())?
            }
        }
        Ok(())
    }
}

impl<Str: AsRef<str>> Crate<Str> {
    fn format_code(&self, out: &mut impl Write) -> std::fmt::Result {
        match self {
            Crate::Registry(version) => write!(out, "Crate::Registry({:?})", version.as_ref())?,
            Crate::GitCommit { git, rev } => write!(
                out,
                "Crate::GitCommit {{ git: {:?}, rev: {:?} }}",
                git.as_ref(),
                rev.as_ref()
            )?,
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
