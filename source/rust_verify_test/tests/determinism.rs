#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// https://github.com/verus-lang/verus/issues/469: the same input must produce the same SMT queries.
// Each of these produced different queries across runs before (trigger choice,
// enum `->` accessors, state machines, exec_spec).
const EXAMPLES: &[&str] = &[
    "../../examples/guide/traits.rs",
    "../../examples/datatypes.rs",
    "../../examples/state_machines/arc.rs",
];
const RUNS: usize = 3;

const EXEC_SPEC: &str = code_str! {
    use vstd::prelude::*;
    use vstd::contrib::exec_spec::*;
    verus! {
        exec_spec_verified! {
            spec fn has_duplicate(a: Seq<u32>) -> bool {
                exists |i: usize| #![trigger a[i as int]] 0 <= i < a.len() &&
                exists |j: usize| #![trigger a[j as int]] 0 <= j < i &&
                    a[i as int] == a[j as int]
            }
        }
    }
};

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
    let exec_spec_dir = tempfile::TempDir::new().expect("temp dir");
    let exec_spec_file = exec_spec_dir.path().join("exec_spec.rs");
    std::fs::write(&exec_spec_file, format!("{}{}{}", FEATURE_PRELUDE, USE_PRELUDE, EXEC_SPEC))
        .expect("write exec_spec.rs");
    let mut inputs: Vec<std::path::PathBuf> =
        EXAMPLES.iter().map(std::path::PathBuf::from).collect();
    inputs.push(exec_spec_file);
    for entry_file in &inputs {
        let example = entry_file.display();
        let tempdir = tempfile::TempDir::new().expect("temp dir");
        let mut first = None;
        for run in 0..RUNS {
            let log_dir = tempdir.path().join(format!("log{run}"));
            let log_dir_opt = format!("--log-dir={}", log_dir.to_str().unwrap());
            let output =
                run_verus(&["--log-smt", &log_dir_opt], tempdir.path(), entry_file, true, false);
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
