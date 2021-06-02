extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_span;

mod pervasive;
pub use pervasive::{PERVASIVE, PERVASIVE_IMPORT_PRELUDE};
pub use rust_verify::verifier::ErrorSpan;
pub use rust_verify_test_macros::{code, code_str};

use rust_verify::config::Args;
use rust_verify::verifier::Verifier;

use rustc_span::source_map::FileLoader;

#[derive(Default)]
struct TestFileLoader {
    files: std::collections::HashMap<std::path::PathBuf, String>,
}

impl FileLoader for TestFileLoader {
    fn file_exists(&self, path: &std::path::Path) -> bool {
        self.files.contains_key(path)
    }

    fn read_file(&self, path: &std::path::Path) -> Result<String, std::io::Error> {
        match self.files.get(path) {
            Some(content) => Ok(content.clone()),
            None => Err(std::io::Error::new(std::io::ErrorKind::NotFound, "file not found")),
        }
    }
}

pub fn verify_files(
    files: impl IntoIterator<Item = (String, String)>,
    entry_file: String,
) -> Result<(), Vec<(Option<ErrorSpan>, Option<ErrorSpan>)>> {
    let rustc_args = vec![
        "../../install/bin/rust_verify".to_string(),
        "--edition".to_string(),
        "2018".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--sysroot".to_string(),
        "../../install".to_string(),
        entry_file,
        "-L".to_string(),
        "../../install/bin/".to_string(),
    ];
    let our_args = {
        let mut our_args: Args = Default::default();
        match std::env::var("VERIFY_LOG_IR_PATH") {
            Ok(path) => {
                let path = std::path::Path::new(&path);
                if !path.is_dir() {
                    panic!(
                        "VERIFY_LOG_IR_PATH is not a directory, std::env::current_dir() is {:?}",
                        std::env::current_dir()
                    );
                }
                our_args.log_vir = Some(path.join("log.vir").to_string_lossy().to_string());
                our_args.log_air_initial = Some(path.join("log.air").to_string_lossy().to_string());
                our_args.log_air_final =
                    Some(path.join("log.air-final").to_string_lossy().to_string());
                our_args.log_smt = Some(path.join("log.smt").to_string_lossy().to_string());
            }
            _ => (),
        }
        our_args
    };
    let captured_output = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let mut verifier = Verifier::new(our_args);
    verifier.test_capture_output = Some(captured_output.clone());
    let mut compiler = rustc_driver::RunCompiler::new(&rustc_args, &mut verifier);
    let file_loader: TestFileLoader =
        TestFileLoader { files: files.into_iter().map(|(p, f)| (p.into(), f)).collect() };
    compiler.set_file_loader(Some(Box::new(file_loader)));
    let status = compiler.run();
    eprintln!(
        "{}",
        std::str::from_utf8(
            &captured_output.lock().expect("internal error: cannot lock captured output")
        )
        .expect("captured output is invalid utf8")
    );
    status.map_err(|_| verifier.errors)
}

pub fn verify_with_pervasive(
    code: String,
) -> Result<(), Vec<(Option<ErrorSpan>, Option<ErrorSpan>)>> {
    let files = vec![
        ("pervasive.rs".to_string(), PERVASIVE.to_string()),
        ("test.rs".to_string(), format!("{}\n\n{}", PERVASIVE_IMPORT_PRELUDE, code.as_str())),
    ];
    verify_files(files, "test.rs".to_string())
}

#[macro_export]
macro_rules! test_verify_with_pervasive {
    ($(#[$attrs:meta])* $name:ident $body:expr => $result:pat => $assertions:expr ) => {
        $(#[$attrs])*
        fn $name() {
            let result = verify_with_pervasive($body);
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
            let result = verify_with_pervasive($body);
            if let $result = result {
            } else {
                assert!(false, "{:?} does not match $result", result);
            }
        }
    };
}

pub fn assert_one_fails(err: Vec<(Option<ErrorSpan>, Option<ErrorSpan>)>) {
    assert_eq!(err.len(), 1);
    assert!(err[0].0.as_ref().expect("span").test_span_line.contains("FAILS"));
}
