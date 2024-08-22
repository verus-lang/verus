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
}

#[allow(dead_code)]
pub fn verify_files(
    name: &str,
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
    options: &[&str],
) -> Result<(), TestErr> {
    verify_files_vstd(name, files, entry_file, false, options)
}

use std::cell::RefCell;
thread_local! {
    pub static THREAD_LOCAL_TEST_NAME: RefCell<Option<String>> = RefCell::new(None);
}

#[allow(dead_code)]
pub fn verify_files_vstd(
    name: &str,
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
    import_vstd: bool,
    options: &[&str],
) -> Result<(), TestErr> {
    verify_files_vstd_all_diags(name, files, entry_file, import_vstd, options).map(|_| ())
}

#[allow(dead_code)]
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

    let mut errors = Vec::new();
    let mut expand_errors_notes = Vec::new();
    let aborting_due_to_re =
        regex::Regex::new(r"^aborting due to( [0-9]+)? previous errors?").unwrap();

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
                is_failure = true;
                eprintln!("[unexpected json] {}", ss);
            }
        }
    }

    if !keep_test_dir {
        if !is_failure {
            std::fs::remove_dir_all(&test_input_dir).unwrap();
        } else {
            print_input_dir_rerun_info(&test_input_dir, options, &entry_file);
        }
    }

    if is_failure {
        Err(TestErr { errors, warnings, notes, expand_errors_notes })
    } else {
        Ok(TestErr { errors, warnings, notes, expand_errors_notes })
    }
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

    let bin = verus_target_path.join(format!("rust_verify{exe}"));

    // Delay so that we not only "wait_exists" for the files to be created,
    // but also wait for the files to be written to and closed.
    #[cfg(target_os = "windows")]
    std::thread::sleep(std::time::Duration::from_millis(1000));

    let mut verus_args = Vec::new();
    let mut external_by_default = false;
    let mut is_core = false;
    verus_args.push("--internal-test-mode".to_string());

    for option in options.iter() {
        if *option == "--expand-errors" {
            verus_args.push("--expand-errors".to_string());
            verus_args.push("--multiple-errors".to_string());
            verus_args.push("2".to_string());
        } else if *option == "--compile" {
            verus_args.push("--compile".to_string());
            verus_args.push("-o".to_string());
            verus_args.push(test_dir.join("libtest.rlib").to_str().expect("valid path").to_owned());
        } else if *option == "--external-by-default" {
            external_by_default = true;
        } else if *option == "--no-lifetime" {
            verus_args.push("--no-lifetime".to_string());
        } else if *option == "vstd" {
            // ignore
        } else if *option == "-V allow-inline-air" {
            verus_args.push("-V".to_string());
            verus_args.push("allow-inline-air".to_string());
        } else if *option == "--is-core" {
            verus_args.push("--is-core".to_string());
            is_core = true;
        } else {
            panic!("option '{}' not recognized by test harness", option);
        }
    }
    if !external_by_default {
        verus_args.push("--no-external-by-default".to_string());
    }

    verus_args.extend(
        vec![
            "--crate-name".to_string(),
            "test_crate".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--extern".to_string(),
            format!("builtin={lib_builtin_path}"),
            "--extern".to_string(),
            format!("builtin_macros={lib_builtin_macros_path}"),
            "--extern".to_string(),
            format!("state_machines_macros={lib_state_machines_macros_path}"),
            "-L".to_string(),
            format!("dependency={verus_target_path_str}"),
        ]
        .into_iter(),
    );

    if json_errors {
        verus_args.push("--error-format=json".to_string());
    }

    verus_args.extend(extra_args.into_iter());

    verus_args.push(entry_file.to_str().unwrap().to_string());
    verus_args.append(&mut vec!["--cfg".to_string(), "erasure_macro_todo".to_string()]);

    if import_vstd && !is_core {
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

#[allow(dead_code)]
pub const USE_PRELUDE: &str = crate::common::code_str! {
    // If we're using the pre-macro-expanded vstd lib, then it might have
    // some macro-internal stuff in it, and rustc needs this option in order to accept it.
    #![feature(fmt_internals)]

    #![allow(unused_imports)]
    #![allow(unused_macros)]
    #![allow(deprecated)]
    #![feature(exclusive_range_pattern)]
    #![feature(strict_provenance)]
    #![feature(allocator_api)]

    use builtin::*;
    use builtin_macros::*;
};

#[allow(dead_code)]
pub fn verify_one_file(name: &str, code: String, options: &[&str]) -> Result<TestErr, TestErr> {
    let o: Vec<&str>;
    let (no_prelude, options) = if options.contains(&"no-auto-import-builtin") {
        o = options.iter().filter(|opt| **opt != "no-auto-import-builtin").map(|x| *x).collect();
        (true, &o[..])
    } else {
        (false, options)
    };

    let vstd = code.contains("vstd::") || options.contains(&"vstd");
    let code = if no_prelude { code } else { format!("{}\n{}", USE_PRELUDE, code.as_str()) };

    let files = vec![("test.rs".to_string(), code)];
    verify_files_vstd_all_diags(name, files, "test.rs".to_string(), vstd, options)
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
    err.iter()
        .filter(|e| e.label != Some(vir::def::THIS_PRE_FAILED.to_string()))
        .next()
        .expect("span")
}

/// Assert that one verification failure happened on source lines containing the string "FAILS".
#[allow(dead_code)]
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
#[allow(dead_code)]
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
#[allow(dead_code)]
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

#[allow(dead_code)]
pub fn assert_vir_error_msg(err: TestErr, expected_msg: &str) {
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].code.is_none()); // thus likely a VIR error
    assert!(err.errors[0].message.contains(expected_msg));
}

#[allow(dead_code)]
pub fn assert_any_vir_error_msg(err: TestErr, expected_msg: &str) {
    assert!(err.errors.iter().all(|x| x.code.is_none())); // thus likely a VIR error
    assert!(err.errors.iter().any(|x| x.message.contains(expected_msg)));
}

#[allow(dead_code)]
pub fn assert_rust_error_msg(err: TestErr, expected_msg: &str) {
    assert_eq!(err.errors.len(), 1);
    let error_re = regex::Regex::new(r"^E[0-9]{4}$").unwrap();
    assert!(err.errors[0].code.as_ref().map(|x| error_re.is_match(&x.code)) == Some(true)); // thus a Rust error
    assert!(err.errors[0].message.contains(expected_msg));
}

#[allow(dead_code)]
pub fn assert_rust_error_msg_all(err: TestErr, expected_msg: &str) {
    assert!(err.errors.len() >= 1);
    let error_re = regex::Regex::new(r"^E[0-9]{4}$").unwrap();
    for e in &err.errors {
        assert!(e.code.as_ref().map(|x| error_re.is_match(&x.code)) == Some(true)); // thus a Rust error
        assert!(e.message.contains(expected_msg));
    }
}

#[allow(dead_code)]
pub fn assert_spans_contain(err: &Diagnostic, needle: &str) {
    assert!(
        err.spans
            .iter()
            .find(|s| s.label.is_some() && s.label.as_ref().unwrap().contains(needle))
            .is_some()
    );
}

#[allow(dead_code)]
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

#[allow(dead_code)]
pub fn assert_fails_bv_32bit(err: TestErr) {
    assert_fails_bv(err, true, false);
}

#[allow(dead_code)]
pub fn assert_fails_bv_64bit(err: TestErr) {
    assert_fails_bv(err, false, true);
}

#[allow(dead_code)]
pub fn assert_fails_bv_32bit_64bit(err: TestErr) {
    assert_fails_bv(err, true, true);
}

pub fn typ_inv_relevant_error_span(err: &Vec<DiagnosticSpan>) -> &DiagnosticSpan {
    err.iter()
        .filter(|e| e.label != Some("type invariant declared here".to_string()))
        .next()
        .expect("span")
}

#[allow(dead_code)]
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
