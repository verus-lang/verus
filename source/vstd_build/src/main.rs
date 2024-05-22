#![feature(rustc_private)]

extern crate rustc_driver;

// For diagnostics when something goes wrong, try "cargo build -vv"

// the build script’s current directory is the source directory of the build script’s package

// path to vstd.rs relative to our directory (source/vstd)
const VSTD_RS_PATH: &str = "vstd/vstd.rs";
// name of generated veruslib.vir in target
const VSTD_VIR: &str = "vstd.vir";

fn log_command(cmd: &std::process::Command) {
    eprintln!("{}", yansi::Paint::magenta(format!("vstd_build running: {:?}", cmd)));
}

fn main() {
    if std::env::var("VERUS_IN_VARGO").is_err() {
        panic!("not running in vargo, read the README for instructions");
    }

    let mut args = std::env::args();
    args.next().expect("executable name");
    let verus_target_path =
        std::path::PathBuf::from(args.next().expect("missing verus target path"));

    let mut release = false;
    let mut no_verify = false;
    let mut no_std = false;
    let mut no_alloc = false;
    let mut verbose = false;
    let mut trace = false;
    let mut log_all = false;
    for arg in args {
        if arg == "--release" {
            release = true;
        } else if arg == "--no-verify" {
            no_verify = true;
        } else if arg == "--verbose" {
            verbose = true;
        } else if arg == "--no-std" {
            no_std = true;
        } else if arg == "--no-alloc" {
            no_alloc = true;
        } else if arg == "--trace" {
            trace = true;
        } else if arg == "--log-all" {
            log_all = true;
        } else {
            panic!("unexpected argument: {:}", arg)
        }
    }

    if !no_std && no_alloc {
        panic!("--no-alloc must be specified along with --no-std");
    }

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
        "--internal-test-mode".to_string(),
        "--extern".to_string(),
        format!("builtin={lib_builtin_path}"),
        "--extern".to_string(),
        format!("builtin_macros={lib_builtin_macros_path}"),
        "--extern".to_string(),
        format!("state_machines_macros={lib_state_machines_macros_path}"),
        "--cfg".to_string(),
        "erasure_macro_todo".to_string(),
        "--crate-type=lib".to_string(),
        "--export".to_string(),
        verus_target_path.join(VSTD_VIR).to_str().unwrap().to_string(),
        "--out-dir".to_string(),
        verus_target_path.to_str().expect("invalid path").to_string(),
        "--multiple-errors".to_string(),
        "2".to_string(),
        "--is-vstd".to_string(),
        "--compile".to_string(),
    ];
    if no_verify {
        child_args.push("--no-verify".to_string());
        child_args.push("--no-lifetime".to_string());
    }
    if trace {
        child_args.push("--trace".to_string());
    }
    if log_all {
        child_args.push("--log-all".to_string());
    }
    if release {
        child_args.push("-C".to_string());
        child_args.push("opt-level=3".to_string());
    }
    if !no_std {
        child_args.push("--cfg".to_string());
        child_args.push("feature=\"std\"".to_string());
    }
    if !no_alloc {
        child_args.push("--cfg".to_string());
        child_args.push("feature=\"alloc\"".to_string());
    }
    child_args.push(VSTD_RS_PATH.to_string());

    let cmd = verus_target_path.join("rust_verify");
    let mut child = std::process::Command::new(cmd);
    child.env("RUST_MIN_STACK", (10 * 1024 * 1024).to_string());
    child.args(&child_args[..]);

    if verbose {
        log_command(&child);
    }

    let mut child = child.spawn().expect("could not execute lifetime rustc process");
    let result = child.wait().expect("vstd verus wait failed");
    if !result.success() {
        let code = result.code();
        panic!("vstd build failed with exit code {:?}", code);
    }
}
