extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_span;

use serde::Deserialize;

pub use rust_verify_test_macros::{code, code_str, verus_code, verus_code_str};

#[derive(Debug, Deserialize)]
pub struct DiagnosticText {
    pub text: String,
    pub highlight_start: usize,
    pub highlight_end: usize,
}

#[derive(Debug, Deserialize)]
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

#[derive(Debug, Deserialize)]
pub struct DiagnosticCode {
    pub code: String,
    pub explanation: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct Diagnostic {
    pub code: Option<DiagnosticCode>,
    pub message: String,
    pub level: String,
    pub spans: Vec<DiagnosticSpan>,
    pub rendered: String,
}

#[derive(Debug)]
pub struct TestErr {
    pub errors: Vec<Diagnostic>,
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
    THREAD_LOCAL_TEST_NAME.with(|tn| *tn.borrow_mut() = Some(name.to_string()));

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

    for (file_name, file_contents) in files {
        use std::io::Write;
        let mut f = std::fs::File::create(test_input_dir.join(file_name))
            .expect("failed to create test file");
        f.write_all(file_contents.as_bytes()).expect("failed to write test file contents");
    }

    let run =
        run_verus(options, &test_input_dir, &test_input_dir.join(entry_file), import_vstd, true);
    let rust_output = std::str::from_utf8(&run.stderr[..]).unwrap().trim();

    let mut errors = Vec::new();
    let mut expand_errors_notes = Vec::new();
    let aborting_due_to_re =
        regex::Regex::new(r"^aborting due to( [0-9]+)? previous errors?").unwrap();

    #[cfg(target_os = "windows")]
    let code = run.status.code().expect("unexpected signal in Windows");

    #[cfg(not(target_os = "windows"))]
    let code = match run.status.code() {
        Some(code) => code,
        None => {
            use std::os::unix::process::ExitStatusExt;
            panic!("test terminated by a signal: {:?}", run.status.signal());
        }
    };

    let mut is_failure = code != 0;

    // eprintln!("rust_output: {}", &rust_output);
    if rust_output.len() > 0 {
        for ss in rust_output.split("\n") {
            let diag: Result<Diagnostic, _> = serde_json::from_str(ss);
            if let Ok(diag) = diag {
                eprintln!("{}", diag.rendered);
                if diag.level == "note"
                    && (diag.message == "split assertion failure"
                        || diag.message == "split precondition failure"
                        || diag.message == "split postcondition failure")
                {
                    // TODO(main_new) define in defs
                    expand_errors_notes.push(diag);
                    continue;
                }
                if diag.level == "failure-note" || diag.level == "note" || diag.level == "warning" {
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

    if !is_failure {
        std::fs::remove_dir_all(&test_input_dir).unwrap();
    }

    if is_failure { Err(TestErr { errors, expand_errors_notes }) } else { Ok(()) }
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
    verus_args.push("--internal-test-mode".to_string());

    for option in options.iter() {
        if *option == "--expand-errors" {
            verus_args.push("--expand-errors".to_string());
            verus_args.push("--multiple-errors".to_string());
            verus_args.push("2".to_string());
        } else if *option == "--arch-word-bits 32" {
            verus_args.push("--arch-word-bits".to_string());
            verus_args.push("32".to_string());
        } else if *option == "--arch-word-bits 64" {
            verus_args.push("--arch-word-bits".to_string());
            verus_args.push("64".to_string());
        } else if *option == "--compile" {
            verus_args.push("--compile".to_string());
            verus_args.push("-o".to_string());
            verus_args.push(test_dir.join("libtest.rlib").to_str().expect("valid path").to_owned());
        } else if *option == "vstd" {
            // ignore
        } else {
            panic!("option '{}' not recognized by test harness", option);
        }
    }

    verus_args.extend(
        vec![
            "--edition".to_string(),
            "2018".to_string(),
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

    if import_vstd {
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
    #[cfg(not(target_os = "windows"))]
    let child = child.env("VERUS_Z3_PATH", "../z3");
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
    #![allow(unused_imports)]
    #![allow(unused_macros)]

    use builtin::*;
    use builtin_macros::*;
};

#[allow(dead_code)]
pub fn verify_one_file(name: &str, code: String, options: &[&str]) -> Result<(), TestErr> {
    let vstd = code.contains("vstd::") || code.contains("pervasive::") || options.contains(&"vstd");
    let files = vec![("test.rs".to_string(), format!("{}\n{}", USE_PRELUDE, code.as_str()))];
    verify_files_vstd(name, files, "test.rs".to_string(), vstd, options)
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
            #[allow(irrefutable_let_patterns)]
            if let $result = result {
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

/// Assert that one verification failure happened on source lines containin the string "FAILS".
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
