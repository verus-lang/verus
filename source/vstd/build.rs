use rust_verify::config::Args;
use rust_verify::file_loader::PervasiveFileLoader;
use rust_verify::verifier::Verifier;

// For diagnostics when something goes wrong, try "cargo build -vv"

// path to install relative to our directory (source/vstd)
const INSTALL_REL_PATH: &str = "../../rust/install";
// path to install/bin relative to our directory (source/vstd)
const INSTALL_BIN_REL_PATH: &str = "../../rust/install/bin/";
// path to vstd.rs relative to our directory (source/vstd)
const VSTD_RS_PATH: &str = "../pervasive/vstd.rs";
// path to pervasive relative to our directory (source/vstd)
const PERVASIVE_PATH: &str = "../pervasive";
// name of generated veruslib.vir in install/bin
const VSTD_VIR: &str = "vstd.vir";

fn main() {
    #[cfg(target_os = "macos")]
    let (pre, dl) = ("lib", "dylib");

    #[cfg(target_os = "linux")]
    let (pre, dl) = ("lib", "so");

    #[cfg(target_os = "windows")]
    let (pre, dl) = ("", "dll");

    let rustc_args: Vec<String> = vec![
        format!("{INSTALL_BIN_REL_PATH}rust_verify"),
        "--extern".to_string(),
        format!("builtin={INSTALL_BIN_REL_PATH}libbuiltin.rlib"),
        "--extern".to_string(),
        format!("builtin_macros={INSTALL_BIN_REL_PATH}{pre}builtin_macros.{dl}"),
        "--extern".to_string(),
        format!("state_machines_macros={INSTALL_BIN_REL_PATH}{pre}state_machines_macros.{dl}"),
        "--edition=2018".to_string(),
        "--sysroot".to_string(),
        INSTALL_REL_PATH.to_string(),
        "--cfg".to_string(),
        "erasure_macro_todo".to_string(),
        "--crate-type=lib".to_string(),
        "--out-dir".to_string(),
        INSTALL_BIN_REL_PATH.to_string(),
        VSTD_RS_PATH.to_string(),
    ];

    let mut our_args: Args = Default::default();
    our_args.pervasive_path = Some(PERVASIVE_PATH.to_string());
    our_args.verify_pervasive = true;
    our_args.multiple_errors = 2;
    our_args.erasure = rust_verify::config::Erasure::Macro;
    our_args.export = Some(INSTALL_BIN_REL_PATH.to_string() + VSTD_VIR);
    our_args.compile = true;
    let file_loader = PervasiveFileLoader::new(Some(PERVASIVE_PATH.to_string()));
    let verifier = Verifier::new(our_args);
    let (_verifier, _stats, status) = rust_verify::driver::run(verifier, rustc_args, file_loader);
    status.expect("failed to build vstd library");

    println!("cargo:rerun-if-changed={PERVASIVE_PATH}");
}
