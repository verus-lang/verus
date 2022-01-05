extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_span;

pub use rust_verify::verifier::ErrorSpan;
pub use rust_verify_test_macros::{code, code_str};

use rust_verify::config::{enable_default_features, parse_args, Args};
use rust_verify::verifier::Verifier;

use rustc_span::source_map::FileLoader;

#[derive(Clone, Default)]
struct TestFileLoader {
    files: std::collections::HashMap<std::path::PathBuf, String>,
}

impl TestFileLoader {
    fn remap_pervasive_path(&self, path: &std::path::Path) -> std::path::PathBuf {
        if path.parent().and_then(|x| x.file_name()) == Some(std::ffi::OsStr::new("pervasive")) {
            if let Some(file_name) = path.file_name() {
                return std::path::Path::new("../pervasive").join(file_name).into();
            }
        }
        return path.into();
    }
}

impl FileLoader for TestFileLoader {
    fn file_exists(&self, path: &std::path::Path) -> bool {
        self.remap_pervasive_path(path).exists() || self.files.contains_key(path)
    }

    fn read_file(&self, path: &std::path::Path) -> Result<String, std::io::Error> {
        let remapped = self.remap_pervasive_path(path);
        if remapped.exists() {
            std::fs::read_to_string(remapped)
        } else {
            match self.files.get(path) {
                Some(content) => Ok(content.clone()),
                None => Err(std::io::Error::new(std::io::ErrorKind::NotFound, "file not found")),
            }
        }
    }
}

#[derive(Debug)]
pub struct TestErr {
    pub errors: Vec<Vec<ErrorSpan>>,
    pub has_vir_error: bool,
}

#[allow(dead_code)]
pub fn verify_files(
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
) -> Result<(), TestErr> {
    verify_files_and_pervasive(files, entry_file, false)
}

#[allow(dead_code)]
pub fn verify_files_and_pervasive(
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
    verify_pervasive: bool,
) -> Result<(), TestErr> {
    let mut rustc_args = vec![
        "../../rust/install/bin/rust_verify".to_string(),
        "--edition".to_string(),
        "2018".to_string(),
        "--crate-name".to_string(),
        "test_crate".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--sysroot".to_string(),
        "../../rust/install".to_string(),
    ];

    #[cfg(target_os = "macos")]
    rustc_args.append(&mut vec![
        "--extern".to_string(),
        "builtin=../../rust/install/bin/libbuiltin.rlib".to_string(),
        "--extern".to_string(),
        "builtin_macros=../../rust/install/bin/libbuiltin_macros.dylib".to_string(),
    ]);

    #[cfg(target_os = "linux")]
    rustc_args.append(&mut vec![
        "--extern".to_string(),
        "builtin=../../rust/install/bin/libbuiltin.rlib".to_string(),
        "--extern".to_string(),
        "builtin_macros=../../rust/install/bin/libbuiltin_macros.so".to_string(),
    ]);

    #[cfg(target_os = "windows")]
    rustc_args.append(&mut vec![
        "--extern".to_string(),
        "builtin=../../rust/install/bin/libbuiltin.rlib".to_string(),
        "--extern".to_string(),
        "builtin_macros=../../rust/install/bin/builtin_macros.dll".to_string(),
    ]);

    enable_default_features(&mut rustc_args);

    rustc_args.push(entry_file);
    let our_args = {
        let mut our_args: Args = if let Ok(extra_args) = std::env::var("VERIFY_EXTRA_ARGS") {
            let (args, rest) = parse_args(
                &"test".to_string(),
                extra_args.split(" ").map(|x| x.to_string()).chain(Some("test".to_string())),
            );
            if rest.len() != 2 {
                eprintln!("warning: unparsed extra arguments from VERIFY_EXTRA_ARGS");
            }
            args
        } else {
            Default::default()
        };
        if let Ok(path) = std::env::var("VERIFY_LOG_IR_PATH") {
            let path = std::path::Path::new(&path);
            if !path.is_dir() {
                panic!(
                    "VERIFY_LOG_IR_PATH is not a directory, std::env::current_dir() is {:?}",
                    std::env::current_dir()
                );
            }
            our_args.log_vir = Some(path.join("log.vir").to_string_lossy().to_string());
            our_args.log_air_initial = Some(path.join("log.air").to_string_lossy().to_string());
            our_args.log_air_final = Some(path.join("log.air-final").to_string_lossy().to_string());
            our_args.log_smt = Some(path.join("log.smt").to_string_lossy().to_string());
        }
        our_args.verify_pervasive |= verify_pervasive;
        our_args
    };
    let files = files.into_iter().map(|(p, f)| (p.into(), f)).collect();
    let captured_output = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let captured_output_1 = captured_output.clone();
    let result = std::panic::catch_unwind(move || {
        let mut verifier = Verifier::new(our_args);
        verifier.test_capture_output = Some(captured_output_1);
        let file_loader: TestFileLoader = TestFileLoader { files };
        let status = rust_verify::driver::run(&mut verifier, &rustc_args, &file_loader);
        status.map(|_| ()).map_err(|_| TestErr {
            errors: verifier.errors,
            has_vir_error: verifier.encountered_vir_error,
        })
    });
    eprintln!(
        "{}",
        std::str::from_utf8(
            &captured_output.lock().expect("internal error: cannot lock captured output")
        )
        .expect("captured output is invalid utf8")
    );
    match result {
        Ok(result) => result,
        Err(_) => {
            panic!(
                "The compiler panicked. This may be due to rustc not being available in the `rust` directory in the project root. Check the README for more information."
            )
        }
    }
}

#[allow(dead_code)]
pub const USE_PRELUDE: &str = crate::common::code_str! {
    #[allow(unused_imports)] use builtin::*;
    #[allow(unused_imports)] use builtin_macros::*;

    mod pervasive; #[allow(unused_imports)] use pervasive::*;
};

#[allow(dead_code)]
pub fn verify_one_file(code: String) -> Result<(), TestErr> {
    let files = vec![("test.rs".to_string(), format!("{}\n\n{}", USE_PRELUDE, code.as_str()))];
    verify_files(files, "test.rs".to_string())
}

#[macro_export]
macro_rules! test_verify_one_file {
    ($(#[$attrs:meta])* $name:ident $body:expr => $result:pat => $assertions:expr ) => {
        $(#[$attrs])*
        fn $name() {
            let result = verify_one_file($body);
            #[allow(irrefutable_let_patterns)]
            if let $result = result {
                $assertions
            } else {
                assert!(false, "{:?} does not match $result", result);
            }
        }
    };
    ($(#[$attrs:meta])* $name:ident $body:expr => $result:pat) => {
        $(#[$attrs])*
        fn $name() {
            let result = verify_one_file($body);
            #[allow(irrefutable_let_patterns)]
            if let $result = result {
            } else {
                assert!(false, "{:?} does not match $result", result);
            }
        }
    };
}

/// Assert that one verification failure happened on source lines containin the string "FAILS".
#[allow(dead_code)]
pub fn assert_one_fails(err: TestErr) {
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].first().expect("span").test_span_line.contains("FAILS"));
}

/// Assert that `count` verification failures happened on source lines containin the string "FAILS".
#[allow(dead_code)]
pub fn assert_fails(err: TestErr, count: usize) {
    assert_eq!(err.errors.len(), count);
    for c in 0..count {
        assert!(err.errors[c].first().expect("span").test_span_line.contains("FAILS"));
    }
}

#[allow(dead_code)]
pub fn assert_vir_error(err: TestErr) {
    assert!(err.has_vir_error);
}
