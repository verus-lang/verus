use anyhow::Result;
use std::fs;
use std::path::Path;
use syn_codegen::Definitions;

pub fn generate(defs: &Definitions) -> Result<()> {
    let mut j = serde_json::to_string_pretty(&defs)?;
    j.push('\n');

    let check: Definitions = serde_json::from_str(&j)?;
    assert_eq!(*defs, check);

    let codegen_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let json_path = codegen_root.join("../syn.json");
    fs::write(json_path, j)?;

    Ok(())
}
