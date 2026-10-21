#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// https://github.com/verus-lang/verus/issues/469: the same input must produce the same SMT queries.
// These examples each produced different queries across runs before (trigger choice,
// enum `->` accessors, state machines).
const EXAMPLES: &[&str] = &[
    "../../examples/guide/traits.rs",
    "../../examples/datatypes.rs",
    "../../examples/state_machines/arc.rs",
];
const RUNS: usize = 3;

fn smt_logs(dir: &std::path::Path) -> std::collections::BTreeMap<String, Vec<u8>> {
    std::fs::read_dir(dir)
        .expect("read log dir")
        .map(|e| {
            let path = e.expect("log entry").path();
            let name = path.file_name().unwrap().to_str().unwrap().to_string();
            (name, std::fs::read(&path).expect("read log file"))
        })
        .collect()
}

#[test]
fn smt_output_is_deterministic_issue469() {
    for example in EXAMPLES {
        let tempdir = tempfile::TempDir::new().expect("temp dir");
        let entry_file = std::path::PathBuf::from(example);
        let mut first = None;
        for run in 0..RUNS {
            let log_dir = tempdir.path().join(format!("log{run}"));
            let log_dir_opt = format!("--log-dir={}", log_dir.to_str().unwrap());
            let output =
                run_verus(&["--log-smt", &log_dir_opt], tempdir.path(), &entry_file, true, false);
            assert!(
                output.status.success(),
                "{} failed:\n{}",
                example,
                String::from_utf8_lossy(&output.stderr)
            );
            let logs = smt_logs(&log_dir);
            assert!(!logs.is_empty(), "{}: no SMT logs", example);
            match &first {
                None => first = Some(logs),
                Some(first) => {
                    assert_eq!(first.keys().collect::<Vec<_>>(), logs.keys().collect::<Vec<_>>());
                    for (name, bytes) in &logs {
                        assert!(
                            first[name] == *bytes,
                            "{}: {} differs in run {}",
                            example,
                            name,
                            run
                        );
                    }
                }
            }
        }
    }
}
