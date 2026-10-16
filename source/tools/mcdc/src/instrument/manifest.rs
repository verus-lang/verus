//! The manifest: one JSON object per line, one line per instrumented decision.

use serde::{Deserialize, Serialize};
use std::io::Write;
use std::path::Path;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct Atom {
    pub line: usize,
    pub col: usize,
    pub text: String,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct Decision {
    /// Decision id, as passed to the runtime's `rec`.
    pub id: u32,
    #[serde(rename = "crate")]
    pub krate: String,
    /// Path relative to the instrumented source/ directory.
    pub file: String,
    pub line: usize,
    pub col: usize,
    /// Syntactic position: if, while, guard, let, return, closure, expr, if-letchain, while-letchain.
    pub kind: String,
    /// Name of the enclosing fn, empty outside fns.
    #[serde(rename = "fn")]
    pub func: String,
    /// Structure over atom indices, for example `((0&&1)||!2)`.
    pub tree: String,
    /// Source text of the then-branch, loop body or arm body (first 400 characters), used to rank gaps.
    pub guarded: String,
    pub text: String,
    pub atoms: Vec<Atom>,
}

impl Decision {
    pub fn n(&self) -> usize {
        self.atoms.len()
    }
    pub fn loc(&self) -> String {
        format!("{}:{}", self.file, self.line)
    }
}

pub fn write(path: &Path, decisions: &[Decision]) -> std::io::Result<()> {
    let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
    for d in decisions {
        serde_json::to_writer(&mut f, d)?;
        f.write_all(b"\n")?;
    }
    f.flush()
}

/// Reads a manifest. Lines with a `kind` of `arm` (written by earlier versions) are skipped.
pub fn read(path: &Path) -> Result<Vec<Decision>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {}", path.display(), e))?;
    let mut out = Vec::new();
    for (i, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let v: serde_json::Value = serde_json::from_str(line)
            .map_err(|e| format!("{}:{}: {}", path.display(), i + 1, e))?;
        if v.get("kind").and_then(|k| k.as_str()) == Some("arm") {
            continue;
        }
        out.push(
            serde_json::from_value(v)
                .map_err(|e| format!("{}:{}: {}", path.display(), i + 1, e))?,
        );
    }
    Ok(out)
}
