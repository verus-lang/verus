use std::collections::{BTreeMap, HashSet};
use std::env;
use std::path::PathBuf;

use sha2::{Digest, Sha256};

use crate::cargo_verus_dep_tracker::DepTracker;
use crate::config::Args;

// TODO: share these with cargo-verus
const VERUS_DRIVER_VERIFY: &str = "__VERUS_DRIVER_VERIFY_";

fn is_cargo_probling(rustc_args: &Vec<String>) -> bool {
    rustc_args.windows(2).any(|window| window[0] == "--crate-name" && window[1] == "___")
}

fn is_build_script(dep_tracker: &mut DepTracker) -> bool {
    dep_tracker
        .get_env("CARGO_CRATE_NAME")
        .map(|name| name.starts_with("build_script_"))
        .unwrap_or(false)
}

fn is_non_verus_crate(rustc_args: &mut Vec<String>, dep_tracker: &mut DepTracker) -> bool {
    let package_id = get_package_id_from_env(dep_tracker);
    let verus_crate = if let Some(package_id) = &package_id {
        let verify_package =
            dep_tracker.compare_env(&format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1");
        verify_package
    } else {
        false
    };
    if !verus_crate {
        if let Some(package_id) = &package_id {
            let is_builtin =
                dep_tracker.compare_env(&format!("__VERUS_DRIVER_IS_BUILTIN_{package_id}"), "1");
            let is_builtin_macros = dep_tracker
                .compare_env(&format!("__VERUS_DRIVER_IS_BUILTIN_MACROS_{package_id}"), "1");

            if is_builtin || is_builtin_macros {
                set_rustc_bootstrap();
                extend_rustc_args_for_builtin_and_builtin_macros(rustc_args);
            }
        }
    }
    !verus_crate
}

pub fn is_direct_cargo_call_to_rustc(
    rustc_args: &mut Vec<String>,
    dep_tracker: &mut DepTracker,
) -> bool {
    is_cargo_probling(rustc_args)
        || is_build_script(dep_tracker)
        || is_non_verus_crate(rustc_args, dep_tracker)
}

pub fn is_compile(args: &Args, dep_tracker: &mut DepTracker) -> bool {
    let is_primary_package = dep_tracker.get_env("CARGO_PRIMARY_PACKAGE").is_some();

    if is_primary_package {
        args.compile_when_primary_package
    } else {
        args.compile_when_not_primary_package
    }
}

pub(crate) fn handle_externs(
    externs: &rustc_session::config::Externs,
    mut import_deps_if_present: HashSet<String>,
    dep_tracker: &mut DepTracker,
) -> Result<(), String> {
    let mut extern_map = BTreeMap::<String, Vec<PathBuf>>::new();

    for (key, entry) in externs.iter() {
        if let Some(files) = entry.files() {
            let files = files.map(|path| path.canonicalized()).cloned().collect();
            extern_map.insert(key.clone(), files).map(|_| panic!("already inserted"));
        }
    }

    let mut imports: Vec<(String, String)> = Vec::new();
    for (key, paths) in &extern_map {
        if import_deps_if_present.remove(key) {
            let mut found = false;
            for path in paths {
                let vir_path = path.with_extension("vir");
                if vir_path.exists() {
                    imports.push((key.clone(), vir_path.display().to_string()));
                    dep_tracker.mark_file(vir_path);
                    found = true;
                    break;
                }
            }
            if !found {
                return Err(format!("could not find .vir file for '{key}'"));
            }
        }
    }
    Ok(())
}

fn get_package_id_from_env(dep_tracker: &mut DepTracker) -> Option<String> {
    match (
        dep_tracker.get_env("CARGO_PKG_NAME"),
        dep_tracker.get_env("CARGO_PKG_VERSION"),
        dep_tracker.get_env("CARGO_MANIFEST_DIR"),
    ) {
        (Some(name), Some(version), Some(manifest_dir)) => {
            Some(mk_package_id(name, version, format!("{manifest_dir}/Cargo.toml")))
        }
        _ => None,
    }
}

fn mk_package_id(
    name: impl AsRef<str>,
    version: impl AsRef<str>,
    manifest_path: impl AsRef<str>,
) -> String {
    let manifest_path_hash = {
        let mut hasher = Sha256::new();
        hasher.update(manifest_path.as_ref().as_bytes());
        hex::encode(hasher.finalize())
    };
    format!("{}-{}-{}", name.as_ref(), version.as_ref(), &manifest_path_hash[..12])
}

fn extend_rustc_args_for_builtin_and_builtin_macros(args: &mut Vec<String>) {
    args.extend(["--cfg", "verus_keep_ghost"].map(ToOwned::to_owned));
}

fn set_rustc_bootstrap() {
    env::set_var("RUSTC_BOOTSTRAP", "1");
}
