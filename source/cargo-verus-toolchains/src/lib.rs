use std::fmt::Write;

use serde::{Deserialize, Serialize};

/// A set of Verus components meant to be used together.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Toolchain {
    /// The Verus version; the primary key to identify a toolchain.
    pub verus: StrLit,
    /// The vstd version.
    pub vstd: Crate,
    /// The Z3 version.
    pub z3: StrLit,
}

/// Identifies a crate in a registry (i.e. crates.io) or git.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Crate {
    /// A version published in a registry.
    Version(StrLit),
    /// A commit in a git repository (e.g. GitHub).
    GitCommit { git: StrLit, rev: StrLit },
}

pub fn format_toolchains_code(
    toolchains: &[Toolchain],
    i0: Indent,
    out: &mut impl Write,
) -> std::fmt::Result {
    writeln!(out, "{i0}/// An entry for each file in the `toolchain-manifests` directory.")?;
    writeln!(out, "{i0}pub const TOOLCHAINS: [Toolchain; {}] = [", toolchains.len())?;
    let i1 = i0.increase();
    for toolchain in toolchains {
        toolchain.format_code(i1, out)?;
        writeln!(out, ",")?;
    }
    writeln!(out, "{i0}];")?;
    Ok(())
}

/// A string literal.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct StrLit {
    contents: String,
}

impl std::fmt::Display for StrLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Escape contents.
        write!(f, "\"{}\"", self.contents)
    }
}

impl From<&str> for StrLit {
    fn from(value: &str) -> Self {
        StrLit { contents: value.to_string() }
    }
}

impl Toolchain {
    pub fn format_code(&self, i0: Indent, out: &mut impl Write) -> std::fmt::Result {
        let i1 = i0.increase();
        writeln!(out, "{i0}Toolchain {{")?;
        writeln!(out, "{i1}verus: {},", self.verus)?;
        writeln!(out, "{i1}vstd: {},", self.vstd)?;
        writeln!(out, "{i1}z3: {},", self.z3)?;
        write!(out, "{i0}}}")?;
        Ok(())
    }
}

impl std::fmt::Display for Crate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Crate::Version(version) => write!(f, "Crate::Registry {{ version: {version} }}")?,
            Crate::GitCommit { git, rev } => {
                write!(f, "Crate::GitCommit {{ git: {git}, rev: {rev} }}")?
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
