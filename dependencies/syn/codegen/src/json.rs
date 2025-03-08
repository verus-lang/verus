use crate::workspace_path;
use anyhow::Result;
use std::fs;
use syn_codegen::Definitions;

pub fn generate(defs: &Definitions) -> Result<()> {
    let mut j = serde_json::to_string_pretty(&defs)?;
    j.push('\n');

    let check: Definitions = serde_json::from_str(&j)?;
    assert_eq!(*defs, check);

    let json_path = workspace_path::get("syn.json");
    fs::write(json_path, j)?;

    Ok(())
}
