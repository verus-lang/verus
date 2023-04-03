#![feature(rustc_private)]

extern crate rustc_driver;

// For diagnostics when something goes wrong, try "cargo build -vv"

// the build script’s current directory is the source directory of the build script’s package

// path to vstd.rs relative to our directory (source/vstd)
const VSTD_RS_PATH: &str = "../pervasive/vstd.rs";
// path to pervasive relative to our directory (source/vstd)
const PERVASIVE_PATH: &str = "../pervasive";
// name of generated veruslib.vir in target
const VSTD_VIR: &str = "vstd.vir";

fn wait_exists(path: &std::path::Path) {
    for _ in 0..200 {
        if path.exists() {
            return;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    panic!("path {} does not exist after 20 seconds", path.display());
}

fn main() {
    if std::env::var("VERUS_IN_VARGO").is_err() {
        panic!("not running in vargo, read the README for instructions");
    }

    // Consider using links for the rlib paths instead
    // https://rust-lang.zulipchat.com/#narrow/stream/122651-general/topic/cargo.20build.2Ers.20artifact/near/340569806
    let out_dir = std::env::var("OUT_DIR").unwrap();

    #[cfg(target_os = "macos")]
    let (pre, dl) = ("lib", "dylib");

    #[cfg(target_os = "linux")]
    let (pre, dl) = ("lib", "so");

    #[cfg(target_os = "windows")]
    let (pre, dl) = ("", "dll");

    let profile = std::env::var("PROFILE").unwrap();

    let target_path =
        std::path::Path::new(&out_dir).parent().unwrap().parent().unwrap().parent().unwrap();
    let verus_target_path = target_path
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
        .join("target-verus")
        .join(profile);

    let lib_builtin_path = verus_target_path.join("libbuiltin.rlib");
    wait_exists(&lib_builtin_path);
    assert!(lib_builtin_path.exists());
    let lib_builtin_path = lib_builtin_path.to_str().unwrap();
    let lib_builtin_macros_path = verus_target_path.join(format!("{}builtin_macros.{}", pre, dl));
    wait_exists(&lib_builtin_macros_path);
    assert!(lib_builtin_macros_path.exists());
    let lib_builtin_macros_path = lib_builtin_macros_path.to_str().unwrap();
    let lib_state_machines_macros_path =
        verus_target_path.join(format!("{}state_machines_macros.{}", pre, dl));
    wait_exists(&lib_state_machines_macros_path);
    assert!(lib_state_machines_macros_path.exists());
    let lib_state_machines_macros_path = lib_state_machines_macros_path.to_str().unwrap();

    let target_deps_path_str = target_path.join("deps").to_str().unwrap().to_string() + "/";

    let child_args: Vec<String> = vec![
        "--internal-build-vstd-driver".to_string(),
        PERVASIVE_PATH.to_string(),
        VSTD_VIR.to_string(),
        target_deps_path_str.to_string(),
        "../z3".to_string(),
        "--extern".to_string(),
        format!("builtin={lib_builtin_path}"),
        "--extern".to_string(),
        format!("builtin_macros={lib_builtin_macros_path}"),
        "--extern".to_string(),
        format!("state_machines_macros={lib_state_machines_macros_path}"),
        "--edition=2018".to_string(),
        "--cfg".to_string(),
        "erasure_macro_todo".to_string(),
        "--crate-type=lib".to_string(),
        "--out-dir".to_string(),
        target_deps_path_str.to_string(),
        VSTD_RS_PATH.to_string(),
    ];

    let cmd = std::env::var("CARGO_BIN_FILE_RUST_VERIFY_rust_verify").unwrap();
    let mut child = std::process::Command::new(cmd)
        .args(&child_args[..])
        .spawn()
        .expect("could not execute lifetime rustc process");
    if !child.wait().expect("vstd verus wait failed").success() {
        panic!("vstd build failed");
    }

    println!("cargo:rerun-if-changed={PERVASIVE_PATH}");
}
