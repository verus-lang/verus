use std::collections::HashSet;
use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;

// ASSUMPTIONS:
// - paths is not empty
// - paths are all canonicalized
fn find_common_root<'a>(paths: impl Iterator<Item = &'a Path>) -> PathBuf {
    let mut paths = paths.map(|p| {
        if p.is_dir() {
            p
        } else {
            p.parent().expect("canonicalized paths that are not dirs have a parent")
        }
    });
    let mut root = paths.next().expect("paths is not empty").to_owned();

    for path in paths {
        while !path.starts_with(&root) {
            root = root
                .parent()
                .expect("canonical path should either be a prefix (`/`) or have a parent")
                .to_owned();
        }
    }

    root
}

/// Returns a list of all rust paths in the roots, and the root of the roots
/// Paths are relative to the root of the roots
pub fn find_rust_files<P: AsRef<Path>>(
    roots: &[P],
) -> Result<(PathBuf, Vec<PathBuf>), std::io::Error> {
    let roots =
        roots.into_iter().map(|p| p.as_ref().canonicalize()).collect::<Result<HashSet<_>, _>>()?;
    let root_path = find_common_root(roots.iter().map(|f| f.as_path()));

    let mut v = Vec::new();
    for root in roots {
        find_rust_files_aux(&root, &mut v)?;
    }

    let v = v
        .into_iter()
        .map(|p| p.strip_prefix(&root_path).map(|x| x.to_owned()))
        .collect::<Result<Vec<_>, _>>()
        .expect("should not have paths in this vector that are not relative to the root");

    Ok((root_path, v))
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
