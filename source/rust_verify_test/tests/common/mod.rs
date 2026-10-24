#![allow(dead_code, clippy::result_large_err)]

extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_span;

use serde::Deserialize;

#[allow(unused_imports)]
pub use rust_verify_test_macros::{code, code_str, verus_code, verus_code_str};

#[derive(Clone, Debug, Deserialize)]
pub struct DiagnosticText {
    pub text: String,
    pub highlight_start: usize,
    pub highlight_end: usize,
}

#[derive(Clone, Debug, Deserialize)]
pub struct DiagnosticSpan {
    pub file_name: String,
    pub line_start: usize,
    pub line_end: usize,
    pub column_start: usize,
    pub column_end: usize,
    pub byte_start: usize,
    pub byte_end: usize,
    pub is_primary: bool,
    pub label: Option<String>,
    pub text: Vec<DiagnosticText>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct DiagnosticCode {
    pub code: String,
    pub explanation: Option<String>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct Diagnostic {
    pub code: Option<DiagnosticCode>,
    pub message: String,
    pub level: String,
    pub spans: Vec<DiagnosticSpan>,
    pub rendered: String,
}

#[derive(Clone, Debug)]
pub struct TestErr {
    pub errors: Vec<Diagnostic>,
    pub warnings: Vec<Diagnostic>,
    pub notes: Vec<Diagnostic>,
    pub expand_errors_notes: Vec<Diagnostic>, // produced by the `--expand-errors` flag
    pub json_output: Option<serde_json::Value>, // captured when `--output-json` is used
}

pub fn verify_files(
    name: &str,
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
    options: &[&str],
) -> Result<(), TestErr> {
    verify_files_vstd(name, files, entry_file, false, options)
}

use std::{cell::RefCell, path};
thread_local! {
    pub static THREAD_LOCAL_TEST_NAME: RefCell<Option<String>> = const { RefCell::new(None) };
}

pub fn verify_files_vstd(
    name: &str,
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
    import_vstd: bool,
    options: &[&str],
) -> Result<(), TestErr> {
    verify_files_vstd_all_diags(name, files, entry_file, import_vstd, options).map(|_| ())
}

pub fn verify_files_vstd_all_diags(
    name: &str,
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
    import_vstd: bool,
    options: &[&str],
) -> Result<TestErr, TestErr> {
    THREAD_LOCAL_TEST_NAME.with(|tn| *tn.borrow_mut() = Some(name.to_string()));

    fn print_input_dir_rerun_info(
        test_input_dir: &std::path::PathBuf,
        options: &[&str],
        entry_file: &String,
    ) {
        eprintln!("the input directory is {}", test_input_dir.to_string_lossy());
        eprintln!("{}", yansi::Paint::blue("rerun this test with:"));
        eprintln!(
            "vargo run -p rust_verify -- --crate-type=lib {} {}",
            options.join(" "),
            test_input_dir.join(entry_file).to_string_lossy()
        );
        eprintln!();
    }

    let files: Vec<(String, String)> = files.into_iter().collect();

    let deps_dir = std::env::current_exe().unwrap();
    let deps_dir = deps_dir.parent().unwrap();
    let target_dir = deps_dir.parent().unwrap();

    let (test_binary, test_name) = {
        let mut args = std::env::args();
        let test_binary = std::path::PathBuf::from(args.next().unwrap());
        let test_name = THREAD_LOCAL_TEST_NAME.with(|tn| tn.take().unwrap());
        (test_binary.file_name().unwrap().to_str().unwrap().to_string(), test_name)
    };
    let test_input_dir_parent = target_dir.join("test_inputs");

    std::fs::create_dir_all(&test_input_dir_parent).unwrap();
    let test_input_dir = test_input_dir_parent.join(format!("{test_binary}-{test_name}"));
    if test_input_dir.exists() {
        std::fs::remove_dir_all(&test_input_dir).unwrap();
    }
    std::fs::create_dir(&test_input_dir).unwrap();

    let keep_test_dir = std::env::var("VERUS_KEEP_TEST_DIR")
        .ok()
        .and_then(|x| if x.trim() == "0" { None } else { Some(()) })
        .is_some();
    if keep_test_dir {
        print_input_dir_rerun_info(&test_input_dir, options, &entry_file);
    }

    for (file_name, file_contents) in files {
        use std::io::Write;
        let mut f = std::fs::File::create(test_input_dir.join(file_name))
            .expect("failed to create test file");
        f.write_all(file_contents.as_bytes()).expect("failed to write test file contents");
    }

    let run =
        run_verus(options, &test_input_dir, &test_input_dir.join(&entry_file), import_vstd, true);
    let rust_output = std::str::from_utf8(&run.stderr[..]).unwrap().trim();
    let json_output = if options.contains(&"--output-json") {
        let stdout_str = std::str::from_utf8(&run.stdout[..]).unwrap_or("").trim();
        serde_json::from_str(stdout_str).ok()
    } else {
        None
    };

    let mut errors = Vec::new();
    let mut expand_errors_notes = Vec::new();

    #[cfg(target_os = "windows")]
    let is_run_success = run.status.success();

    #[cfg(not(target_os = "windows"))]
    let is_run_success = run.status.success();

    #[cfg(not(target_os = "windows"))]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = run.status.signal() {
            eprintln!("test terminated by a signal: {:?}", signal);
        }
    }

    let mut is_failure = !is_run_success;
    let (warnings, notes) =
        parse_diags(rust_output, &mut errors, &mut expand_errors_notes, &mut is_failure);

    if !keep_test_dir {
        if !is_failure {
            std::fs::remove_dir_all(&test_input_dir).unwrap();
        } else {
            print_input_dir_rerun_info(&test_input_dir, options, &entry_file);
        }
    }

    if is_failure {
        Err(TestErr { errors, warnings, notes, expand_errors_notes, json_output })
    } else {
        Ok(TestErr { errors, warnings, notes, expand_errors_notes, json_output })
    }
}

pub fn parse_diags(
    rust_output: &str,
    errors: &mut Vec<Diagnostic>,
    expand_errors_notes: &mut Vec<Diagnostic>,
    is_failure: &mut bool,
) -> (Vec<Diagnostic>, Vec<Diagnostic>) {
    let aborting_due_to_re =
        regex::Regex::new(r"^aborting due to( [0-9]+)? previous errors?").unwrap();

    let mut warnings = Vec::new();
    let mut notes = Vec::new();

    // eprintln!("rust_output: {}", &rust_output);
    if rust_output.len() > 0 {
        for ss in rust_output.split("\n") {
            let diag: Result<Diagnostic, _> = serde_json::from_str(ss);
            if let Ok(diag) = diag {
                eprintln!("{}", diag.rendered);
                if diag.level == "note" && diag.message.starts_with("diagnostics via expansion") {
                    // TODO(main_new) define in defs
                    expand_errors_notes.push(diag);
                    continue;
                } else if diag.level == "note" {
                    notes.push(diag);
                    continue;
                } else if diag.level == "warning" {
                    warnings.push(diag);
                    continue;
                } else if diag.level == "failure-note" {
                    continue;
                }
                assert!(diag.level == "error");
                if aborting_due_to_re.is_match(&diag.message) {
                    continue;
                }
                errors.push(diag);
            } else {
                *is_failure = true;
                eprintln!("[unexpected json] \"{}\"", ss);
            }
        }
    }
    (warnings, notes)
}

pub fn run_verus(
    options: &[&str],
    test_dir: &std::path::Path,
    entry_file: &std::path::PathBuf,
    import_vstd: bool,
    json_errors: bool,
) -> std::process::Output {
    if std::env::var("VERUS_IN_VARGO").is_err() {
        panic!("not running in vargo, read the README for instructions");
    }

    let extra_args: Vec<_> = std::env::var("VERUS_EXTRA_ARGS")
        .map(|x| x.split_whitespace().map(|x| x.to_string()).collect::<Vec<_>>())
        .unwrap_or(Vec::new());

    #[cfg(target_os = "macos")]
    let (pre, dl, exe) = ("lib", "dylib", "");

    #[cfg(target_os = "linux")]
    let (pre, dl, exe) = ("lib", "so", "");

    #[cfg(target_os = "windows")]
    let (pre, dl, exe) = ("", "dll", ".exe");

    let current_exe = std::env::current_exe().unwrap();
    let deps_path = current_exe.parent().unwrap();
    let target_path = deps_path.parent().unwrap();
    let profile = target_path.file_name().unwrap().to_str().unwrap();
    let verus_target_path = target_path
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
        .join("target-verus")
        .join(profile);

    let verus_target_path_str = verus_target_path.to_str().unwrap();

    let lib_builtin_path = verus_target_path.join("libverus_builtin.rlib");
    assert!(lib_builtin_path.exists());
    let lib_builtin_path = lib_builtin_path.to_str().unwrap();
    let lib_builtin_macros_path =
        verus_target_path.join(format!("{}verus_builtin_macros.{}", pre, dl));
    assert!(lib_builtin_macros_path.exists());
    let lib_builtin_macros_path = lib_builtin_macros_path.to_str().unwrap();
    let lib_state_machines_macros_path =
        verus_target_path.join(format!("{}verus_state_machines_macros.{}", pre, dl));
    assert!(lib_state_machines_macros_path.exists());
    let lib_state_machines_macros_path = lib_state_machines_macros_path.to_str().unwrap();

    let bin = verus_target_path.join(format!("rust_verify{exe}"));

    // Delay so that we not only "wait_exists" for the files to be created,
    // but also wait for the files to be written to and closed.
    #[cfg(target_os = "windows")]
    std::thread::sleep(std::time::Duration::from_millis(1000));

    let mut verus_args = Vec::new();
    let mut no_external_by_default = false;
    let mut is_core = false;
    let mut use_internal_test_mode = true;
    let mut crate_name = "test_crate";

    for option in options.iter() {
        if let Some(name) = option.strip_prefix("--crate-name=") {
            crate_name = name;
        } else if *option == "--expand-errors" {
            verus_args.push("--expand-errors".to_string());
            verus_args.push("--multiple-errors".to_string());
            verus_args.push("2".to_string());
        } else if *option == "--compile" {
            verus_args.push("--compile".to_string());
        } else if *option == "--no-external-by-default" {
            no_external_by_default = true;
        } else if *option == "--no-lifetime" {
            verus_args.push("--no-lifetime".to_string());
        } else if *option == "--no-erasure-check" {
            verus_args.push("--no-erasure-check".to_string());
        } else if *option == "--no-verify" {
            verus_args.push("--no-verify".to_string());
        } else if *option == "--no-report-long-running" {
            verus_args.push("--no-report-long-running".to_string());
        } else if *option == "--no-cheating" {
            verus_args.push("--no-cheating".to_string());
        } else if *option == "--output-json" {
            verus_args.push("--output-json".to_string());
        } else if *option == "vstd" {
            // ignore
        } else if *option == "-V allow-inline-air" {
            verus_args.push("-V".to_string());
            verus_args.push("allow-inline-air".to_string());
        } else if *option == "-V check-api-safety" {
            verus_args.push("-V".to_string());
            verus_args.push("check-api-safety".to_string());
        } else if *option == "-V spinoff-all" {
            verus_args.push("-V".to_string());
            verus_args.push("spinoff-all".to_string());
        } else if *option == "--is-core" {
            verus_args.push("--is-core".to_string());
            is_core = true;
        } else if *option == "--disable-internal-test-mode" {
            use_internal_test_mode = false;
        } else if *option == "no-bv-simplify" {
            verus_args.push("-V".to_string());
            verus_args.push("no-bv-simplify".to_string());
        } else if *option == "--edition 2024" {
            verus_args.push("--edition".to_string());
            verus_args.push("2024".to_string());
        } else if *option == "--edition 2021" {
            verus_args.push("--edition".to_string());
            verus_args.push("2021".to_string());
        } else if *option == "--edition 2018" {
            verus_args.push("--edition".to_string());
            verus_args.push("2018".to_string());
        } else if *option == TSM_VERIFIED_OPTION {
            verus_args.push("--cfg".to_string());
            verus_args.push(TSM_VERIFIED_CFG.to_string());
        } else {
            panic!("option '{}' not recognized by test harness", option);
        }
    }
    if use_internal_test_mode {
        verus_args.insert(0, "--internal-test-mode".to_string());
    }
    // VERUS_TSM=verified selects the checked macro for every test of this run (including
    // tests and examples not written with `test_verify_tsm!`); see `tsm_verified_forced`.
    if tsm_verified_forced() && !options.contains(&TSM_VERIFIED_OPTION) {
        verus_args.push("--cfg".to_string());
        verus_args.push(TSM_VERIFIED_CFG.to_string());
    }
    if no_external_by_default {
        verus_args.push("--no-external-by-default".to_string());
    }

    verus_args.extend(
        vec![
            "--crate-name".to_string(),
            crate_name.to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
        ]
        .into_iter(),
    );
    if !is_core {
        verus_args.extend(
            vec!["--extern".to_string(), format!("verus_builtin={lib_builtin_path}")].into_iter(),
        );
    }
    verus_args.extend(
        vec![
            "--extern".to_string(),
            format!("verus_builtin_macros={lib_builtin_macros_path}"),
            "--extern".to_string(),
            format!("verus_state_machines_macros={lib_state_machines_macros_path}"),
            "-L".to_string(),
            format!("dependency={verus_target_path_str}"),
            // suppress Rust's generation of long-type files
            "-Z".to_string(),
            "write_long_types_to_disk=no".to_string(),
            // suppress common warnings in examples and tests
            "-A".to_string(),
            "non_snake_case".to_string(),
            "-A".to_string(),
            "deprecated".to_string(),
        ]
        .into_iter(),
    );

    let compile = options.contains(&"--compile");
    verus_args.push("-o".to_string());
    if compile {
        verus_args.push(test_dir.join("libtest.rlib").to_str().expect("valid path").to_owned());
    } else {
        verus_args
            .push(test_dir.join("libtest_crate.rmeta").to_str().expect("valid path").to_owned());
        verus_args.push("--emit=metadata".to_string());
    }

    if json_errors {
        verus_args.push("--error-format=json".to_string());
    }

    verus_args.extend(extra_args.into_iter());

    verus_args.push(entry_file.to_str().unwrap().to_string());

    if import_vstd && !is_core && use_internal_test_mode {
        let lib_vstd_vir_path = verus_target_path.join("vstd.vir");
        let lib_vstd_vir_path = lib_vstd_vir_path.to_str().unwrap();
        let lib_vstd_path = verus_target_path.join("libvstd.rlib");
        let lib_vstd_path = lib_vstd_path.to_str().unwrap();
        verus_args.append(&mut vec!["--cfg".to_string(), "vstd_todo".to_string()]);
        verus_args.append(&mut vec![
            "--extern".to_string(),
            format!("vstd={lib_vstd_path}"),
            "--import".to_string(),
            format!("vstd={lib_vstd_vir_path}"),
        ]);
    }

    if !import_vstd {
        verus_args.append(&mut vec!["--cfg".to_string(), "verus_no_vstd".to_string()]);
    }

    let mut child = std::process::Command::new(bin);
    child.env(
        "VERUS_Z3_PATH",
        std::env::var("VERUS_Z3_PATH")
            .map(|p| {
                let p = std::path::PathBuf::from(p);
                (if p.is_relative() { std::path::PathBuf::from("..").join(p) } else { p })
                    .into_os_string()
            })
            .unwrap_or({
                if cfg!(target_os = "windows") {
                    std::ffi::OsString::from("..\\z3.exe")
                } else {
                    std::ffi::OsString::from("../z3")
                }
            }),
    );
    let child = child
        .args(&verus_args[..])
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("could not execute test rustc process");
    let run = child.wait_with_output().expect("lifetime rustc wait failed");
    run
}

pub fn run_verus_raw(args: &[&str], dir: &std::path::Path) -> std::process::Output {
    if std::env::var("VERUS_IN_VARGO").is_err() {
        panic!("not running in vargo, read the README for instructions");
    }
    let exe = if cfg!(target_os = "windows") { ".exe" } else { "" };

    let current_exe = std::env::current_exe().unwrap();
    let deps_path = current_exe.parent().unwrap();
    let target_path = deps_path.parent().unwrap();
    let profile = target_path.file_name().unwrap().to_str().unwrap();
    let verus_target_path = target_path
        .ancestors()
        .nth(2)
        .expect("expected path to have at least two parents")
        .join("target-verus")
        .join(profile);
    let bin = verus_target_path.join(format!("rust_verify{exe}"));

    let z3 = std::env::var("VERUS_Z3_PATH")
        .map(|p| {
            let p = std::path::PathBuf::from(p);
            if p.is_relative() { std::path::PathBuf::from("..").join(p) } else { p }
        })
        .unwrap_or({
            if cfg!(target_os = "windows") {
                std::path::PathBuf::from("..\\z3.exe")
            } else {
                std::path::PathBuf::from("../z3")
            }
        });
    let z3 = path::absolute(z3).expect("Failed to find absolute path for Z3 executable");

    std::process::Command::new(bin)
        .current_dir(dir)
        .env("VERUS_Z3_PATH", z3)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("could not execute verus")
        .wait_with_output()
        .expect("raw verus wait failed")
}

pub fn run_cargo_verus(args: &[&str], dir: &std::path::Path) -> std::process::Output {
    run_cargo_verus_with_target(args, dir, &dir.join("target"))
}

pub fn run_cargo_verus_with_target(
    args: &[&str],
    dir: &std::path::Path,
    target_dir: &std::path::Path,
) -> std::process::Output {
    if std::env::var("VERUS_IN_VARGO").is_err() {
        panic!("not running in vargo, read the README for instructions");
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let exe = "";

    #[cfg(target_os = "windows")]
    let exe = ".exe";

    // Compute the path to the cargo-verus executable,
    // following the pattern from run_verus
    let current_exe = std::env::current_exe().unwrap();
    let deps_path = current_exe.parent().unwrap();
    let target_path = deps_path.parent().unwrap();
    let profile = target_path.file_name().unwrap().to_str().unwrap();
    let verus_target_path = target_path
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
        .join("target-verus")
        .join(profile);
    let bin = verus_target_path.join(format!("cargo-verus{exe}"));

    let mut child = std::process::Command::new(bin);
    let invocation_dir = tempfile::tempdir().expect("temporary cargo invocation directory");
    let manifest_path = dir.join("Cargo.toml");
    if args.first() == Some(&"new") {
        child.current_dir(dir);
    } else {
        child.current_dir(invocation_dir.path());
    }
    child.env("CARGO_TARGET_DIR", target_dir);
    child.env("CARGO_BUILD_TARGET_DIR", target_dir);
    child.env("CARGO_BUILD_BUILD_DIR", target_dir);

    let z3 = std::env::var("VERUS_Z3_PATH")
        .map(|p| {
            let p = std::path::PathBuf::from(p);
            (if p.is_relative() { std::path::PathBuf::from("..").join(p) } else { p })
                .into_os_string()
        })
        .unwrap_or({
            if cfg!(target_os = "windows") {
                std::ffi::OsString::from("..\\z3.exe")
            } else {
                std::ffi::OsString::from("../z3")
            }
        });
    let z3 = path::absolute(z3).expect("Failed to find absolute path for Z3 executable");
    child.env("VERUS_Z3_PATH", z3);

    let mut cargo_verus_args = Vec::new();
    cargo_verus_args.push(args[0]);
    if args.first() != Some(&"new") {
        cargo_verus_args
            .extend(["--manifest-path", manifest_path.to_str().expect("valid manifest path")]);
    }
    cargo_verus_args.extend(&args[1..]);

    let child = child
        .args(cargo_verus_args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("could not execute cargo-verus process");
    let run = child.wait_with_output().expect("cargo-verus wait failed");
    if !run.status.success() {
        let rust_output = std::str::from_utf8(&run.stderr[..]).unwrap().trim();
        eprintln!("Failed with output:\n{}", rust_output);
    }
    run
}

// Assumes normal `cargo` is in the caller's path
pub fn run_cargo(args: &[&str], dir: &std::path::Path) -> std::process::Output {
    run_cargo_with_target(args, dir, &dir.join("target"))
}

pub fn run_cargo_with_target(
    args: &[&str],
    dir: &std::path::Path,
    target_dir: &std::path::Path,
) -> std::process::Output {
    // if std::env::var("VERUS_IN_VARGO").is_err() {
    //     panic!("not running in vargo, read the README for instructions");
    // }
    let invocation_dir = tempfile::tempdir().expect("temporary cargo invocation directory");
    let manifest_path = dir.join("Cargo.toml");
    let mut child = std::process::Command::new("cargo");
    child.current_dir(invocation_dir.path());

    // Remove Verus-specific RUSTFLAGS that are set by vargo, as they cause
    // verus_builtin and vstd to require unstable features not available on stable Rust
    child.env_remove("RUSTFLAGS");
    child.env("CARGO_TARGET_DIR", target_dir);
    child.env("CARGO_BUILD_TARGET_DIR", target_dir);
    child.env("CARGO_BUILD_BUILD_DIR", target_dir);

    let child = child
        .args(args)
        .args(["--manifest-path", manifest_path.to_str().expect("valid manifest path")])
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("could not execute cargo process");
    let run = child.wait_with_output().expect("cargo wait failed");
    if !run.status.success() {
        let rust_output = std::str::from_utf8(&run.stderr[..]).unwrap().trim();
        eprintln!("Failed with output:\n{}", rust_output);
    }
    run
}

pub const FEATURE_PRELUDE: &str = crate::common::code_str! {
    // If we're using the pre-macro-expanded vstd lib, then it might have
    // some macro-internal stuff in it, and rustc needs this option in order to accept it.
    #![feature(fmt_internals)]

    #![allow(unused_imports)]
    #![allow(unused_features)]
    #![allow(unused_macros)]
    #![allow(deprecated)]
    #![allow(non_snake_case)]
    #![allow(non_camel_case_types)]
    #![allow(non_upper_case_globals)]
    #![allow(unused_comparisons)]
    #![allow(noop_method_call)]
    #![feature(allocator_api)]
    #![feature(proc_macro_hygiene)]
    #![feature(never_type)]
    #![feature(core_intrinsics)]
    #![feature(ptr_metadata)]
    #![feature(sized_hierarchy)]
    #![feature(btree_cursors)]
    #![feature(const_destruct)]
    #![feature(print_internals)]
};

pub const USE_PRELUDE: &str = crate::common::code_str! {
    use verus_builtin::*;
    use verus_builtin_macros::*;
};

pub fn verify_one_file(name: &str, code: String, options: &[&str]) -> Result<TestErr, TestErr> {
    let mut options: Vec<_> = options.into_iter().map(|x| *x).collect();
    let mut no_prelude = false;
    let mut exec_allows_no_decreases_clause = false;
    options.retain(|x| {
        if *x == "exec_allows_no_decreases_clause" {
            exec_allows_no_decreases_clause = true;
            false
        } else if *x == "no-auto-import-verus_builtin" {
            no_prelude = true;
            false
        } else {
            true
        }
    });

    let vstd = code.contains("vstd::") || options.contains(&"vstd");
    let code = if no_prelude {
        code
    } else {
        let exec_allows_no_decreases_clause_str = if exec_allows_no_decreases_clause {
            "#![verifier::exec_allows_no_decreases_clause]\n"
        } else {
            ""
        };
        format!(
            "{}{}{}\n{}",
            FEATURE_PRELUDE,
            exec_allows_no_decreases_clause_str,
            USE_PRELUDE,
            code.as_str()
        )
    };

    let files = vec![("test.rs".to_string(), code)];
    verify_files_vstd_all_diags(name, files, "test.rs".to_string(), vstd, &options[..])
}

#[macro_export]
macro_rules! test_verify_one_file_with_options {
    ($(#[$attrs:meta])* $name:ident $options:expr => $body:expr => $result:pat => $assertions:expr ) => {
        $(#[$attrs])*
        fn $name() {
            let result = verify_one_file(::std::stringify!($name), $body, &$options);
            #[allow(irrefutable_let_patterns)]
            if let $result = result {
                $assertions
            } else {
                assert!(false, "Err(_) does not match $result");
            }
        }
    };
    ($(#[$attrs:meta])* $name:ident $options:expr => $body:expr => $result:pat) => {
        $(#[$attrs])*
        fn $name() {
            let result = verify_one_file(::std::stringify!($name), $body, &$options);
            let result_unit = result.as_ref().map(|_| ());
            #[allow(irrefutable_let_patterns)]
            if let $result = result_unit {
                if let Ok(err) = result {
                    assert_eq!(err.warnings.len(), 0);
                }
            } else {
                assert!(false, "Err(_) does not match $result");
            }
        }
    };
}

#[macro_export]
macro_rules! test_verify_one_file {
    ($(#[$attrs:meta])* $name:ident $body:expr => $result:pat => $assertions:expr ) => {
        test_verify_one_file_with_options!($(#[$attrs])* $name [] => $body => $result => $assertions);
    };
    ($(#[$attrs:meta])* $name:ident $body:expr => $result:pat) => {
        test_verify_one_file_with_options!($(#[$attrs])* $name [] => $body => $result);
    };
}

/// Test option selecting the checked `verified_tokenized_state_machine!`: the verifier gets
/// `--cfg verus_verified_tsm`, under which the test prelude (and example files) import
/// `verified_tokenized_state_machine as tokenized_state_machine` and
/// `verified_state_machine_model as state_machine`.
pub const TSM_VERIFIED_OPTION: &str = "--verified-tsm";
pub const TSM_VERIFIED_CFG: &str = "verus_verified_tsm";

/// `VERUS_TSM=verified` forces the checked macro for every test and example of the run.
pub fn tsm_verified_forced() -> bool {
    std::env::var("VERUS_TSM").map(|v| v == "verified").unwrap_or(false)
}

/// The options of a run with the checked state-machine macro: `options` plus
/// `TSM_VERIFIED_OPTION`, and `--no-cheating` unless the test opts out
/// (`; verified cheating "<reason>"`), so that a verified run also checks that the checked
/// macro introduces no `assume`/`admit`/`external_body`.
pub fn with_tsm_verified<'a>(options: &[&'a str], no_cheating: bool) -> Vec<&'a str> {
    let mut options = options.to_vec();
    options.push(TSM_VERIFIED_OPTION);
    if no_cheating && !options.contains(&"--no-cheating") {
        options.push("--no-cheating");
    }
    options
}

/// The words of the user-written assumptions that `--no-cheating` rejects.
pub const CHEATING_MARKERS: &[&str] = &[
    "assume",
    "admit",
    "external_body",
    "assume_specification",
    "assume_termination",
    "externals_available_without_declaration",
];

/// Whether a `--no-cheating` error points at a user-written assumption: the highlighted
/// source of a primary span, or an attribute line directly above it (such as
/// `#[verifier::external_body]` above a function), contains one of `CHEATING_MARKERS`.
fn no_cheating_error_at_user_site(source: &str, err: &Diagnostic) -> bool {
    let lines: Vec<&str> = source.lines().collect();
    let primary: Vec<_> = err.spans.iter().filter(|s| s.is_primary).collect();
    !primary.is_empty()
        && primary.iter().all(|s| {
            let highlighted = s.text.iter().any(|t| {
                let start = t.highlight_start.saturating_sub(1).min(t.text.len());
                let end = t.highlight_end.saturating_sub(1).clamp(start, t.text.len());
                let h = t.text.get(start..end).unwrap_or(&t.text);
                CHEATING_MARKERS.iter().any(|m| h.contains(m))
            });
            // the attribute lines directly above the span, in `source` (1-based lines; checked
            // to be the file of the span by comparing the span's first line)
            let in_source = s.line_start >= 1
                && s.text
                    .first()
                    .is_some_and(|t| lines.get(s.line_start - 1) == Some(&t.text.as_str()));
            let attribute_above = in_source
                && lines[..s.line_start - 1]
                    .iter()
                    .rev()
                    .take_while(|l| l.trim_start().starts_with("#["))
                    .any(|l| CHEATING_MARKERS.iter().any(|m| l.contains(m)));
            highlighted || attribute_above
        })
}

/// For a verified run that opted out of `--no-cheating` (`; verified cheating "<reason>"`):
/// checks the run with `--no-cheating` is rejected only for the test's own assumptions, i.e.
/// that there is a `--no-cheating` error and every one points at a user-written
/// `assume`/`admit`/`external_body` (see `no_cheating_error_at_user_site`). Verus reports the
/// first `--no-cheating` error of each function, so a macro-introduced assumption in a
/// function that also contains a user assumption is not seen.
pub fn assert_cheating_only_at_user_sites(source: &str, result: Result<TestErr, TestErr>) {
    let err = match result {
        Err(err) => err,
        Ok(_) => panic!(
            "the test opts out of --no-cheating (`verified cheating`), but it verifies with \
             --no-cheating: remove the opt-out"
        ),
    };
    assert_no_cheating_errors_at_user_sites(source, &err.errors);
}

/// `errors` (of a run with `--no-cheating`) contain a `--no-cheating` error, and each points
/// at a user-written assumption of `source`.
pub fn assert_no_cheating_errors_at_user_sites(source: &str, errors: &[Diagnostic]) {
    let cheating: Vec<_> =
        errors.iter().filter(|e| e.message.contains("not allowed with --no-cheating")).collect();
    assert!(
        !cheating.is_empty(),
        "the test opts out of --no-cheating (`verified cheating`), but --no-cheating reports no \
         assumption: {:#?}",
        errors
    );
    for e in cheating {
        assert!(
            no_cheating_error_at_user_site(source, e),
            "--no-cheating error outside a user-written assumption (macro-generated?):\n{}",
            e.rendered
        );
    }
}

/// Runs one test for both state-machine macros: generates `mod <name> { fn trusted; fn verified }`.
///
/// ```ignore
/// test_verify_tsm! { #[test] name IMPORTS.to_string() + verus_code_str!{..} => Ok(()) }
/// test_verify_tsm! { #[test] name [options] BODY => Err(e) => assert_vir_error_msg(e, "x") }
/// // per-macro expectation for the checked macro:
/// test_verify_tsm! { #[test] name BODY => Ok(()) ; verified => Err(e) => assert_fails(e, 1) }
/// // case not (yet) supported by the checked macro (reported as an ignored test):
/// test_verify_tsm! { #[test] name BODY => Ok(()) ; verified ignore "reason" }
/// // case only meaningful for the trusted macro (no checked test is generated):
/// test_verify_tsm! { #[test] name BODY => Ok(()) ; trusted_only "reason" }
/// // the verified run uses --no-cheating unless the test's source contains an assumption:
/// test_verify_tsm! { #[test] name BODY => Ok(()) ; verified cheating "test contains assume(false)" }
/// ```
#[macro_export]
macro_rules! test_verify_tsm {
    ($(#[$attrs:meta])* $name:ident $([$($opt:expr),* $(,)?])? $body:expr => Ok(()) $(; $($v:tt)*)?) => {
        $crate::test_verify_tsm!(@mod [$(#[$attrs])*] $name [$($($opt),*)?] [$body]
            [Ok(())] [] [$($($v)*)?]);
    };
    ($(#[$attrs:meta])* $name:ident $([$($opt:expr),* $(,)?])? $body:expr => $result:pat => $assertions:expr $(; $($v:tt)*)?) => {
        $crate::test_verify_tsm!(@mod [$(#[$attrs])*] $name [$($($opt),*)?] [$body]
            [$result] [$assertions] [$($($v)*)?]);
    };
    (@mod [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($tr:tt)*] [$($ta:tt)*] [$($v:tt)*]) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;
            $($attrs)*
            fn trusted() {
                let result = verify_one_file(::std::stringify!($name), $body, &[$($opt),*]);
                $crate::test_verify_tsm!(@check result [$($tr)*] [$($ta)*]);
            }
            $crate::test_verify_tsm!(@verified [$($attrs)*] $name [$($opt),*] [$body] [$($tr)*] [$($ta)*] [] $($v)*);
        }
    };
    // The clauses after the trusted expectation, separated by `;`, in any order. `[$($c)*]`
    // is the `verified cheating` reason (empty: the verified run uses `--no-cheating`).
    (@verified [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($tr:tt)*] [$($ta:tt)*] [$($c:tt)*]) => {
        $crate::test_verify_tsm!(@verified_fn [$($attrs)*] $name [$($opt),*] [$body] [$($tr)*] [$($ta)*] [$($c)*]);
    };
    (@verified [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($tr:tt)*] [$($ta:tt)*] [$($c:tt)*] verified cheating $reason:literal $(; $($rest:tt)*)?) => {
        $crate::test_verify_tsm!(@verified [$($attrs)*] $name [$($opt),*] [$body] [$($tr)*] [$($ta)*] [$reason] $($($rest)*)?);
    };
    (@verified [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($tr:tt)*] [$($ta:tt)*] [$($c:tt)*] verified => Ok(()) $(; $($rest:tt)*)?) => {
        $crate::test_verify_tsm!(@verified [$($attrs)*] $name [$($opt),*] [$body] [Ok(())] [] [$($c)*] $($($rest)*)?);
    };
    (@verified [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($tr:tt)*] [$($ta:tt)*] [$($c:tt)*] verified => $vr:pat => $va:expr $(; $($rest:tt)*)?) => {
        $crate::test_verify_tsm!(@verified [$($attrs)*] $name [$($opt),*] [$body] [$vr] [$va] [$($c)*] $($($rest)*)?);
    };
    (@verified [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($tr:tt)*] [$($ta:tt)*] [$($c:tt)*] verified ignore $reason:literal $(; $($rest:tt)*)?) => {
        $crate::test_verify_tsm!(@verified [$($attrs)* #[ignore = $reason]] $name [$($opt),*] [$body] [$($tr)*] [$($ta)*] [$($c)*] $($($rest)*)?);
    };
    (@verified [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($tr:tt)*] [$($ta:tt)*] [$($c:tt)*] trusted_only $reason:literal) => {
        const _: &str = $reason;
    };
    (@verified_fn [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($vr:tt)*] [$($va:tt)*] []) => {
        $($attrs)*
        fn verified() {
            let options = with_tsm_verified(&[$($opt),*], true);
            let result = verify_one_file(
                &::std::format!("{}__verified", ::std::stringify!($name)), $body, &options);
            $crate::test_verify_tsm!(@check result [$($vr)*] [$($va)*]);
        }
    };
    // `verified cheating "<reason>"`: the test's own source contains an assumption, so the
    // verified run is without `--no-cheating`; a second run with `--no-cheating` checks that
    // it is rejected only at the user's assumptions.
    (@verified_fn [$($attrs:tt)*] $name:ident [$($opt:expr),*] [$body:expr] [$($vr:tt)*] [$($va:tt)*] [$reason:literal]) => {
        $($attrs)*
        fn verified() {
            const _: &str = $reason;
            let body: String = $body;
            let options = with_tsm_verified(&[$($opt),*], false);
            let result = verify_one_file(
                &::std::format!("{}__verified", ::std::stringify!($name)), body.clone(), &options);
            $crate::test_verify_tsm!(@check result [$($vr)*] [$($va)*]);
            let options = with_tsm_verified(&[$($opt),*], true);
            let result = verify_one_file(
                &::std::format!("{}__verified_no_cheating", ::std::stringify!($name)),
                body.clone(), &options);
            assert_cheating_only_at_user_sites(&body, result);
        }
    };
    (@check $result:ident [Ok(())] []) => {
        match $result {
            Ok(err) => assert_eq!(err.warnings.len(), 0),
            Err(err) => assert!(false, "expected Ok(()), got {:?}", err),
        }
    };
    (@check $result:ident [$p:pat] [$a:expr]) => {
        #[allow(irrefutable_let_patterns)]
        if let $p = $result {
            $a
        } else {
            assert!(false, "result does not match the expected pattern");
        }
    };
}

/// `test_verify_one_file_with_options!` syntax for `test_verify_tsm!`.
#[macro_export]
macro_rules! test_verify_tsm_with_options {
    ($(#[$attrs:meta])* $name:ident [$($opt:expr),* $(,)?] => $body:expr => Ok(()) $(; $($v:tt)*)?) => {
        $crate::test_verify_tsm!(@mod [$(#[$attrs])*] $name [$($opt),*] [$body]
            [Ok(())] [] [$($($v)*)?]);
    };
    ($(#[$attrs:meta])* $name:ident [$($opt:expr),* $(,)?] => $body:expr => $result:pat => $assertions:expr $(; $($v:tt)*)?) => {
        $crate::test_verify_tsm!(@mod [$(#[$attrs])*] $name [$($opt),*] [$body]
            [$result] [$assertions] [$($($v)*)?]);
    };
}

// We run the bit-vector tests twice; once with interpreter-based simplification on
// (to mirror what the end-user sees) and once with it off (to check that our SMT encoding
// of bit-vector operations is correct).
#[macro_export]
macro_rules! test_verify_one_bv_file_with_options {
    ($(#[$attrs:meta])* $name:ident $options:expr => $body:expr => $result:pat => $assertions:expr ) => {
        $(#[$attrs])*
        fn $name() {
            let result = verify_one_file(::std::stringify!($name), $body, &$options);
            #[allow(irrefutable_let_patterns)]
            if let $result = result {
                $assertions
            } else {
                assert!(false, "Err(_) does not match $result");
            }
            // Run a second time with simplification off
            let mut opts = Vec::new();
            opts.extend_from_slice(&$options);
            opts.push("no-bv-simplify");
            let result = verify_one_file(::std::stringify!($name), $body, opts.as_slice());
            #[allow(irrefutable_let_patterns)]
            if let $result = result {
                $assertions
            } else {
                assert!(false, "Err(_) does not match $result, with bit-vector simplification disabled");
            }
        }
    };
    ($(#[$attrs:meta])* $name:ident $options:expr => $body:expr => $result:pat) => {
        $(#[$attrs])*
        fn $name() {
            let result = verify_one_file(::std::stringify!($name), $body, &$options);
            let result_unit = result.as_ref().map(|_| ());
            #[allow(irrefutable_let_patterns)]
            if let $result = result_unit {
                if let Ok(err) = result {
                    assert_eq!(err.warnings.len(), 0);
                }
            } else {
                assert!(false, "Err(_) does not match $result");
            }

            // Run a second time with simplification off
            let mut opts = Vec::new();
            opts.extend_from_slice(&$options);
            opts.push("no-bv-simplify");
            let result = verify_one_file(::std::stringify!($name), $body, opts.as_slice());
            let result_unit = result.as_ref().map(|_| ());
            #[allow(irrefutable_let_patterns)]
            if let $result = result_unit {
                if let Ok(err) = result {
                    assert_eq!(err.warnings.len(), 0);
                }
            } else {
                assert!(false, "Err(_) does not match $result, with bit-vector simplification disabled");
            }
        }
    };
}

#[macro_export]
macro_rules! test_verify_one_bv_file {
    ($(#[$attrs:meta])* $name:ident $body:expr => $result:pat => $assertions:expr ) => {
        test_verify_one_bv_file_with_options!($(#[$attrs])* $name [] => $body => $result => $assertions);
    };
    ($(#[$attrs:meta])* $name:ident $body:expr => $result:pat) => {
        test_verify_one_bv_file_with_options!($(#[$attrs])* $name [] => $body => $result);
    };
}

pub fn relevant_error_span(err: &Vec<DiagnosticSpan>) -> &DiagnosticSpan {
    if let Some(e) = err.iter().find(|e| e.label == Some("at this exit".to_string())) {
        return e;
    } else if let Some(e) = err.iter().find(|e| e.label == Some("at this call-site".to_string())) {
        return e;
    } else if let Some(e) =
        err.iter().find(|e| e.label == Some("might not be allowed at this call-site".to_string()))
    {
        return e;
    } else if let Some(e) = err.iter().find(|e| {
        e.label == Some(vir::def::THIS_POST_FAILED.to_string()) && !e.text[0].text.contains("TRAIT")
    }) {
        return e;
    }
    err.iter().find(|e| e.label != Some(vir::def::THIS_PRE_FAILED.to_string())).expect("span")
}

/// Assert that one verification failure happened on source lines containing the string "FAILS".
pub fn assert_one_fails(err: TestErr) {
    assert_eq!(err.errors.len(), 1);
    assert!(
        relevant_error_span(&err.errors[0].spans)
            .text
            .iter()
            .find(|x| x.text.contains("FAILS"))
            .is_some()
    );
}

/// When this testcase has ONE verification failure,
/// assert that all spans are properly reported (All spans are respoinsible to the verification failure)
pub fn assert_expand_fails(err: TestErr, span_count: usize) {
    assert_fails(err.clone(), 1);

    assert_eq!(err.expand_errors_notes.len(), 1);
    let expand_errors_diag = &err.expand_errors_notes.last().unwrap();
    assert_eq!(expand_errors_diag.spans.len(), span_count);
    for c in 0..span_count {
        assert!(&expand_errors_diag.spans[c].text[0].text.contains("EXPAND-ERRORS"));
    }
}

/// Assert that `count` verification failures happened on source lines containin the string "FAILS".
pub fn assert_fails(err: TestErr, count: usize) {
    assert_eq!(err.errors.len(), count);
    for c in 0..count {
        assert!(
            relevant_error_span(&err.errors[c].spans)
                .text
                .iter()
                .find(|x| x.text.contains("FAILS"))
                .is_some()
        );
    }
}

/// Assert `count` verification failures, wherever reported (for the checked state-machine
/// macro, whose generated safety-condition proofs report at the macro invocation).
pub fn assert_fails_anywhere(err: TestErr, count: usize) {
    assert_eq!(err.errors.len(), count, "errors: {:?}", err.errors);
    for e in &err.errors {
        assert!(
            e.code.is_none(),
            "expected a verification failure, got rustc error: {}",
            e.message
        );
    }
}

pub fn assert_vir_error_msg(err: TestErr, expected_msg: &str) {
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].code.is_none()); // thus likely a VIR error
    assert!(err.errors[0].message.contains(expected_msg));
}

pub fn assert_any_vir_error_msg(err: TestErr, expected_msg: &str) {
    assert!(err.errors.iter().all(|x| x.code.is_none())); // thus likely a VIR error
    assert!(err.errors.iter().any(|x| x.message.contains(expected_msg)));
}

pub fn assert_vir_error_msgs(err: TestErr, expected_msgs: &[&str]) {
    assert!(err.errors.len() == expected_msgs.len());
    assert!(err.errors.iter().all(|x| x.code.is_none())); // thus likely a VIR error
    for (error, expected_msg) in err.errors.iter().zip(expected_msgs.iter()) {
        assert!(error.message.contains(expected_msg));
    }
}

pub fn assert_custom_attr_error_msg(err: TestErr, expected_msg: &str) {
    assert!(
        err.errors.iter().any(|x| x.message.contains("custom attribute panicked")
            && x.rendered.contains(expected_msg))
    );
}

pub fn assert_help_error_msg(err: TestErr, expected_msg: &str) {
    assert!(err.errors.iter().any(|x| x.rendered.contains(expected_msg)));
}

pub fn assert_help_error_msgs(err: TestErr, expected_msgs: &[&str]) {
    assert!(
        expected_msgs
            .iter()
            .all(|expected_msg| err.errors.iter().any(|x| x.rendered.contains(expected_msg)))
    );
}

pub fn assert_rust_error_msg(err: TestErr, expected_msg: &str) {
    assert_eq!(err.errors.len(), 1);
    let error_re = regex::Regex::new(r"^E[0-9]{4}$").unwrap();
    // usually we can use the existence of an error code to tell if something is a
    // Rust error message, though some error messages don't come with error codes
    assert!(
        err.errors[0].code.as_ref().map(|x| error_re.is_match(&x.code)) == Some(true)
            || err.errors[0].message.contains("lifetime may not live long enough")
    ); // thus a Rust error
    assert!(err.errors[0].message.contains(expected_msg));
}

pub fn assert_rust_error_msg_skip_spec_msgs(mut err: TestErr, expected_msg: &str) {
    err.errors.retain(|e| !e.message.contains("(Verus spec"));
    assert_rust_error_msg(err, expected_msg)
}

pub fn assert_rust_error_msgs(err: TestErr, expected_msgs: &[&str]) {
    assert_eq!(err.errors.len(), expected_msgs.len());
    let error_re = regex::Regex::new(r"^E[0-9]{4}$").unwrap();
    // usually we can use the existence of an error code to tell if something is a
    // Rust error message, though some error messages don't come with error codes
    assert!(
        err.errors[0].code.as_ref().map(|x| error_re.is_match(&x.code)) == Some(true)
            || err.errors[0].message.contains("lifetime may not live long enough")
    ); // thus a Rust error
    for (error, expected_msg) in err.errors.iter().zip(expected_msgs.iter()) {
        assert!(error.message.contains(expected_msg));
    }
}

pub fn assert_rust_error_msg_all(err: TestErr, expected_msg: &str) {
    assert!(err.errors.len() >= 1);
    let error_re = regex::Regex::new(r"^E[0-9]{4}$").unwrap();
    for e in &err.errors {
        assert!(e.code.as_ref().map(|x| error_re.is_match(&x.code)) == Some(true)); // thus a Rust error
        assert!(e.message.contains(expected_msg));
    }
}

pub fn assert_rust_error_msg_any(err: TestErr, expected_msg: &str) {
    assert!(err.errors.len() >= 1);
    let error_re = regex::Regex::new(r"^E[0-9]{4}$").unwrap();
    let mut found = false;
    for e in &err.errors {
        assert!(e.code.as_ref().map(|x| error_re.is_match(&x.code)) == Some(true)); // thus a Rust error
        if e.message.contains(expected_msg) {
            found = true;
        }
    }
    assert!(found);
}

pub fn assert_spans_contain(err: &Diagnostic, needle: &str) {
    assert!(
        err.spans
            .iter()
            .find(|s| s.label.is_some() && s.label.as_ref().unwrap().contains(needle))
            .is_some()
    );
}

pub fn assert_fails_bv(err: TestErr, fail32: bool, fail64: bool) {
    assert_eq!(err.errors.len(), (if fail32 { 1 } else { 0 }) + (if fail64 { 1 } else { 0 }));
    if fail32 {
        assert!(err.errors[0].message.contains("with arch-size set to 32 bits"));
    }
    if fail64 {
        let i = err.errors.len() - 1;
        assert!(err.errors[i].message.contains("with arch-size set to 64 bits"));
    }
}

pub fn assert_fails_bv_32bit(err: TestErr) {
    assert_fails_bv(err, true, false);
}

pub fn assert_fails_bv_64bit(err: TestErr) {
    assert_fails_bv(err, false, true);
}

pub fn assert_fails_bv_32bit_64bit(err: TestErr) {
    assert_fails_bv(err, true, true);
}

pub fn typ_inv_relevant_error_span(err: &Vec<DiagnosticSpan>) -> &DiagnosticSpan {
    err.iter().find(|e| e.label != Some("type invariant declared here".to_string())).expect("span")
}

pub fn assert_has_recommends_failure(err: TestErr) {
    assert!(err.errors.len() > 0);
    let mut found_rec_failure = false;
    for note in err.notes.iter() {
        if note.message.contains("recommendation not met") {
            found_rec_failure = true;
            break;
        }
    }
    assert!(found_rec_failure);
}

pub fn assert_fails_type_invariant_error(err: TestErr, count: usize) {
    assert_eq!(err.errors.len(), count);
    for c in 0..count {
        assert!(err.errors[c].message.contains("may fail to meet its declared type invariant"));
        assert!(
            typ_inv_relevant_error_span(&err.errors[c].spans)
                .text
                .iter()
                .find(|x| x.text.contains("FAILS"))
                .is_some()
        );
    }
}
