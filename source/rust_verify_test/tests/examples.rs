#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use rust_verify_test_macros::examples_in_dir;
use std::path::{Path, PathBuf};

#[derive(Debug)]
enum Mode {
    ExpectSuccess,
    ExpectErrors,
    ExpectFailures,
    ExpectWarnings,
    ExpectErrorMsg(String),
}

examples_in_dir!("../../examples");
examples_in_dir!("../../examples/guide");
examples_in_dir!("../../examples/resource");
examples_in_dir!("../../examples/state_machines");
examples_in_dir!("../../examples/summer_school");
examples_in_dir!("../../examples/state_machines/tutorial");
examples_in_dir!("../../examples/state_machines/reference-examples");
examples_in_dir!("../../examples/std_test");
examples_in_dir!("../../examples/cuckoo_hash_table");
examples_in_dir!("../../examples/iterators");
examples_in_dir!("../../examples/storage_protocol");
// Checked state machines (verified_tokenized_state_machine!-specific tests; run with --no-cheating).
examples_in_dir!("../../examples/verified_tsm");
examples_in_dir!("../../examples/verified_tsm/negative");

#[cfg(feature = "singular")]
examples_in_dir!("../../examples/integer_ring");

fn run_example_for_file(file_path: &str) {
    run_example(file_path, false)
}

/// The run with the checked state-machine macro (`--cfg verus_verified_tsm`) of an example
/// that selects its macro by that cfg. A header line
/// `// verified-tsm: <command> [--- reason]` (one of the first-line commands) overrides the
/// first line's expectation for this run.
fn run_example_for_file_tsm(file_path: &str) {
    run_example(file_path, true)
}

fn run_example(file_path: &str, verified_tsm: bool) {
    let relative_path = Path::new(file_path);

    let mut path = std::path::PathBuf::from("rust_verify");
    path.extend(relative_path);
    let path = path.to_str().expect("invalid example path");

    let text = std::fs::read_to_string(relative_path).expect("cannot open file");
    let first_line = text.lines().next().unwrap_or("").to_string();
    let tsm_line = text
        .lines()
        .take(20)
        .find_map(|l| l.trim().strip_prefix("// verified-tsm: "))
        .map(|rest| format!("// rust_verify/tests/example.rs {}", rest.trim()));
    let first_line = match (verified_tsm, tsm_line) {
        (true, Some(line)) => line,
        _ => first_line,
    };
    let first_line_elements: Vec<_> = first_line.trim().split(" ").collect();

    let mut mode = Mode::ExpectSuccess;

    let mut options = vec![];
    if verified_tsm {
        options.push(TSM_VERIFIED_OPTION);
    }

    if let ["//", "rust_verify/tests/example.rs", command, ..] = &first_line_elements[..] {
        match *command {
            "expect-success" => mode = Mode::ExpectSuccess,
            "expect-errors" => mode = Mode::ExpectErrors,
            "expect-failures" => mode = Mode::ExpectFailures,
            "expect-warnings" => mode = Mode::ExpectWarnings,
            "expand-errors" => {
                mode = Mode::ExpectFailures;
                options.push("--expand-errors");
            }
            "no-report-long-running" => {
                mode = Mode::ExpectSuccess;
                options.push("--no-report-long-running");
            }
            "ignore" => {
                if first_line_elements.len() > 3 {
                    // We require that any comment is separated by a `---` which acts as a good
                    // visual separator.
                    if first_line_elements[3] != "---" {
                        panic!(
                            "Expected '---' to separate the extra comment from the 'ignore' declaration. Found {:?}",
                            first_line_elements[3],
                        );
                    } else if first_line_elements.len() == 4 {
                        panic!(
                            "Expected comment after visual separator '---' but no comment found."
                        );
                    }
                } else {
                    panic!(
                        "{}",
                        "Expected '--- {reason}' after the 'ignore', but none was provided."
                    );
                }
                return;
            }
            _ => panic!(
                "invalid command {:?} for example file test: use one of 'expect-success', 'expect-errors', 'expect-failures', 'expand-errors', 'no-report-long-running', or 'ignore'",
                command
            ),
        }
    }

    // A negative example states a substring of an expected error:
    // `// EXPECTED-ERROR: <substring>` (matched against the errors' rendered text and code).
    if let Some(msg) =
        text.lines().take(20).find_map(|l| l.trim().strip_prefix("// EXPECTED-ERROR: "))
    {
        mode = Mode::ExpectErrorMsg(msg.trim().to_string());
    }

    // The checked state-machine examples (`examples/verified_tsm`) and the runs with the checked
    // macro (`verified_tsm`) use `--no-cheating`, unless the file says otherwise with a header
    // line `// no-cheating: off --- <reason>` (its own source contains an assumption).
    let no_cheating_off =
        text.lines().take(20).any(|l| l.trim().starts_with("// no-cheating: off --- "));
    // A file of `examples/verified_tsm` that selects its macro by `cfg(verus_verified_tsm)` also
    // has a run with the trusted macro, whose generated code is not checked (`external_body`,
    // `assume`): that run never uses `--no-cheating`, as for the other examples.
    let checked_dir = relative_path.starts_with("../../examples/verified_tsm");
    let trusted_run = !verified_tsm && text.contains("cfg(verus_verified_tsm)");
    if ((checked_dir && !trusted_run) || verified_tsm) && !no_cheating_off {
        options.push("--no-cheating");
    }

    let relative_path = PathBuf::from(relative_path);

    // Create a temp directory under target/ for --out-dir output
    let target_dir = std::env::current_exe().unwrap();
    let target_dir = target_dir.parent().unwrap().parent().unwrap();
    let example_out_dir = target_dir.join("test_inputs").join(format!(
        "example-{}{}",
        // the whole path: examples/verified_tsm repeats file names of other directories
        relative_path.with_extension("").to_str().unwrap().replace("../", "").replace('/', "-"),
        if verified_tsm { "-verified-tsm" } else { "" }
    ));
    if example_out_dir.exists() {
        std::fs::remove_dir_all(&example_out_dir).unwrap();
    }
    std::fs::create_dir_all(&example_out_dir).unwrap();

    {
        // same naming scheme as examples_in_dir!
        let dir = relative_path.parent().unwrap().to_str().unwrap();
        let test_name = dir.replace("../../", "").replace("/", "_").replace("-", "_")
            + "_"
            + &relative_path.file_prefix().unwrap().to_str().unwrap().replace("-", "_");
        let file_name = relative_path.file_name().unwrap().to_str().unwrap().to_string();
        let contents = std::fs::read_to_string(&relative_path).expect("cannot read example");
        let files = [(file_name.clone(), contents)];
        prepare_test_log_dir("examples", &test_name, &file_name, &files, &options);
    }
    let output = run_verus(&options, &example_out_dir, &relative_path, true, true);

    // An example whose checked-macro run opts out of `--no-cheating`: with `--no-cheating`, it is
    // rejected only at the example's own assumptions.
    if verified_tsm && no_cheating_off {
        let mut nc_options = options.clone();
        nc_options.push("--no-cheating");
        let nc_out_dir = example_out_dir.with_extension("no-cheating");
        if nc_out_dir.exists() {
            std::fs::remove_dir_all(&nc_out_dir).unwrap();
        }
        std::fs::create_dir_all(&nc_out_dir).unwrap();
        let nc_output = run_verus(&nc_options, &nc_out_dir, &relative_path, true, true);
        let nc_stderr = std::str::from_utf8(&nc_output.stderr).expect("invalid stderr encoding");
        let (mut nc_errors, mut nc_notes, mut nc_failure) = (Vec::new(), Vec::new(), false);
        parse_diags(nc_stderr.trim(), &mut nc_errors, &mut nc_notes, &mut nc_failure);
        assert!(
            !nc_output.status.success(),
            "{}: `no-cheating: off`, but it verifies with --no-cheating: remove the opt-out",
            path
        );
        assert_no_cheating_errors_at_user_sites(&text, &nc_errors);
    }

    use regex::Regex;
    let re = Regex::new(r"verification results:: (\d+) verified, (\d+) errors").unwrap();
    let stdout = std::str::from_utf8(&output.stdout).expect("invalid stdout encoding");
    let stderr = std::str::from_utf8(&output.stderr).expect("invalid stderr encoding").trim();
    let mut errors = Vec::new();
    let mut expand_errors_notes = Vec::new();
    let mut is_failure = false;
    let (warnings, _notes) =
        parse_diags(stderr, &mut errors, &mut expand_errors_notes, &mut is_failure);
    let verifier_output: Option<(u64, u64)> = re.captures_iter(stdout).next().map(|x| {
        (
            x[1].parse().expect("invalid verifier output"),
            x[2].parse().expect("invalid verifier output"),
        )
    });

    let success = match mode {
        Mode::ExpectSuccess => {
            output.status.success()
                && match verifier_output {
                    Some((_, 0)) => true,
                    _ => false,
                }
                && !is_failure
                && warnings.len() == 0
        }
        Mode::ExpectErrors => !output.status.success(),
        Mode::ExpectWarnings => {
            output.status.success()
                && match verifier_output {
                    Some((_, 0)) => true,
                    _ => false,
                }
                && warnings.len() > 0
        }
        Mode::ExpectFailures => {
            !output.status.success()
                && match verifier_output {
                    Some((_, failures)) if failures > 0 => true,
                    _ => false,
                }
        }
        Mode::ExpectErrorMsg(ref msg) => {
            !output.status.success()
                && errors.iter().any(|e| {
                    e.rendered.contains(msg.as_str())
                        || e.message.contains(msg.as_str())
                        || e.code.as_ref().is_some_and(|c| c.code.contains(msg.as_str()))
                })
        }
    };

    if !success {
        eprintln!("- example {} - mode: {:?} - failed -", &path, mode);
        if warnings.len() > 0 {
            for w in warnings {
                eprintln!("- warning - {}", w.rendered);
            }
        }
        eprintln!("- stdout -\n{}\n", stdout);
        panic!();
    }
}
