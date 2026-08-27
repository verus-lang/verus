use std::{
    env::consts::{DLL_EXTENSION, DLL_PREFIX, EXE_SUFFIX},
    path::{Path, PathBuf},
};

/// Checks that `root` contains every component required to run Verus.
pub fn check_required_components(root: &Path) -> Result<(), Vec<PathBuf>> {
    let components = [
        format!("verus{EXE_SUFFIX}"),
        format!("rust_verify{EXE_SUFFIX}"),
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
