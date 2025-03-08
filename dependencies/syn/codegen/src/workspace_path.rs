use std::path::{Path, PathBuf};

pub fn get(relative_to_workspace_root: impl AsRef<Path>) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    assert!(path.pop());
    path.push(relative_to_workspace_root);
    path
}
