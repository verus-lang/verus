use std::{
    env::consts::{DLL_EXTENSION, DLL_PREFIX},
    path::{Path, PathBuf},
};

/// Checks that `root` contains every artifact required to run Verus.
pub fn check_required_artifacts(root: &Path) -> Result<(), Vec<PathBuf>> {
    let components = [
        "libverus_builtin.rlib".to_owned(),
        format!("{DLL_PREFIX}verus_builtin_macros.{DLL_EXTENSION}"),
        format!("{DLL_PREFIX}verus_state_machines_macros.{DLL_EXTENSION}"),
        "libvstd.rlib".to_owned(),
        "vstd.vir".to_owned(),
    ];

    let missing: Vec<_> = components
        .iter()
        .map(|component| root.join(component))
        .filter(|component| !component.is_file())
        .collect();

    if missing.is_empty() { Ok(()) } else { Err(missing) }
}
