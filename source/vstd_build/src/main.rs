#![feature(rustc_private)]

extern crate rustc_driver;

// For diagnostics when something goes wrong, try "cargo build -vv"

// the build script’s current directory is the source directory of the build script’s package

// path to vstd.rs relative to our directory (source/vstd)
const VSTD_RS_PATH: &str = "pervasive/vstd.rs";
// path to pervasive relative to our directory (source/vstd)
const PERVASIVE_PATH: &str = "pervasive";
// name of generated veruslib.vir in target
const VSTD_VIR: &str = "vstd.vir";

fn main() {
    if std::env::var("VERUS_IN_VARGO").is_err() {
        panic!("not running in vargo, read the README for instructions");
    }

    let mut args = std::env::args();
    args.next().expect("executable name");
    let verus_target_path =
        std::path::PathBuf::from(args.next().expect("missing verus target path"));
    let release = match args.next().as_ref().map(|x| x.as_str()) {
        Some("--release") => true,
        Some(_) => panic!("unexpected profile argument"),
        None => false,
    };

    #[cfg(target_os = "macos")]
    let (pre, dl) = ("lib", "dylib");

    #[cfg(target_os = "linux")]
    let (pre, dl) = ("lib", "so");

    #[cfg(target_os = "windows")]
    let (pre, dl) = ("", "dll");

    let lib_builtin_path = verus_target_path.join("libbuiltin.rlib");
    assert!(lib_builtin_path.exists());
    let lib_builtin_path = lib_builtin_path.to_str().unwrap();
    let lib_builtin_macros_path = verus_target_path.join(format!("{}builtin_macros.{}", pre, dl));
    assert!(lib_builtin_macros_path.exists());
    let lib_builtin_macros_path = lib_builtin_macros_path.to_str().unwrap();
    let lib_state_machines_macros_path =
        verus_target_path.join(format!("{}state_machines_macros.{}", pre, dl));
    assert!(lib_state_machines_macros_path.exists());
    let lib_state_machines_macros_path = lib_state_machines_macros_path.to_str().unwrap();

    if !std::env::var("VERUS_Z3_PATH").is_ok() {
        std::env::set_var("VERUS_Z3_PATH", if cfg!(windows) { ".\\z3.exe" } else { "./z3" });
    }

    let mut child_args: Vec<String> = vec![
        "--internal-build-vstd-driver".to_string(),
        PERVASIVE_PATH.to_string(),
        VSTD_VIR.to_string(),
        verus_target_path.to_str().expect("invalid path").to_string(),
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
        verus_target_path.to_str().expect("invalid path").to_string(),
    ];
    if release {
        child_args.push("-C".to_string());
        child_args.push("opt-level=3".to_string());
    }
    child_args.push(VSTD_RS_PATH.to_string());

    let cmd = verus_target_path.join("rust_verify");
    let mut child = std::process::Command::new(cmd)
        .args(&child_args[..])
        .spawn()
        .expect("could not execute lifetime rustc process");
    let result = child.wait().expect("vstd verus wait failed");
    if !result.success() {
        let code = result.code();
        panic!("vstd build failed with exit code {:?}", code);
    }
}
