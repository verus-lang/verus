use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;

/// Returns a list of all rust paths in the root path
/// Paths are relative to the root
pub fn find_rust_files<P: AsRef<Path>>(root: P) -> Result<Vec<PathBuf>, std::io::Error> {
    let mut v = Vec::new();
    let root_path = root.as_ref();
    find_rust_files_aux(root_path, &mut v)?;
    let v = v
        .into_iter()
        .map(|p| p.strip_prefix(root_path).map(|x| x.to_owned()))
        .collect::<Result<Vec<_>, _>>()
        .expect("should not have paths in this vector that are not relative to the root");
    Ok(v)
}

fn find_rust_files_aux(root: &Path, vec: &mut Vec<PathBuf>) -> Result<(), std::io::Error> {
    if !root.is_dir() {
        if root.extension() == Some(OsStr::new("rs")) {
            vec.push(root.to_owned());
        }
        return Ok(());
    }

    for entry in root.read_dir()? {
        let entry = entry?;
        find_rust_files_aux(entry.path().as_path(), vec)?
    }

    Ok(())
}
