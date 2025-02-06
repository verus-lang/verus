use anyhow::{bail, Result};
use std::ffi::OsStr;
use std::fs;
use std::path::Path;

fn main() -> Result<()> {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let cargo_expand_dir = manifest_dir.join("..");

    for entry in fs::read_dir(cargo_expand_dir)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        if !file_type.is_file() {
            continue;
        }

        let path = entry.path();
        if path.extension() != Some(OsStr::new("rs")) {
            continue;
        }

        let input_contents = fs::read_to_string(&path)?;
        let syntax_tree = match syn::parse_file(&input_contents) {
            Ok(syntax_tree) => syntax_tree,
            Err(err) => {
                let path = path.canonicalize().unwrap_or(path);
                let span = err.span().start();
                bail!("{}:{}:{}\n{}", path.display(), span.line, span.column, err);
            }
        };
        let string = prettyplease::unparse(&syntax_tree);
        fs::write(&path, string)?;
    }

    Ok(())
}
