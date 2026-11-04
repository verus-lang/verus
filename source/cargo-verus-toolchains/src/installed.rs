use std::{
    env::consts::{DLL_EXTENSION, DLL_PREFIX},
    path::{Path, PathBuf},
};

/// Checks that `root` contains every artifact required to run Verus.
pub fn check_required_artifacts(root: &Path) -> Result<(), Vec<PathBuf>> {
    let missing: Vec<_> = required_artifacts()
        .into_iter()
        .map(|component| root.join(component))
        .filter(|component| !component.is_file())
        .collect();

    if missing.is_empty() { Ok(()) } else { Err(missing) }
}

/// The library artifacts required in a Verus installation.
pub fn required_artifacts() -> Vec<String> {
    vec![
        "libverus_builtin.rlib".to_owned(),
        format!("{DLL_PREFIX}verus_builtin_macros.{DLL_EXTENSION}"),
        format!("{DLL_PREFIX}verus_state_machines_macros.{DLL_EXTENSION}"),
        "libvstd.rlib".to_owned(),
        "vstd.vir".to_owned(),
    ]
}
