#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

#[test]
fn harness_zero() {
    assert!(
        verify_one_file(
            "harness_zero",
            verus_code! {
                fn harness1() {
                }
            },
            &[]
        )
        .is_ok()
    );
}

#[test]
fn harness_invalid_rust() {
    let code = verus_code! {
        fn harness1() {
            invalid(true);
        }
    };
    let err = verify_one_file("harness_invalid_rust", code, &[]).unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert_rust_error_msg(err, "cannot find function `invalid` in this scope");
}

#[test]
fn harness_true() {
    assert!(
        verify_one_file(
            "harness_true",
            verus_code! {
                fn harness1() {
                    assert(true);
                }
            },
            &[]
        )
        .is_ok()
    );
}

#[test]
fn harness_false() {
    let err = verify_one_file(
        "harness_false",
        verus_code! {
            fn harness2() {
                assert(false); // FAILS
            }
        },
        &[],
    )
    .unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].spans.first().expect("span").text[0].text.contains("FAILS"));
}

test_verify_one_file! {
    #[test] harness_macro_true verus_code! {
        fn empty() { }

        fn harness1_macro() {
            assert(true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] harness_macro_false verus_code! {
        fn empty() { }

        fn harness2_macro() {
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] cvc5_smtlib_with_z3_verifies ["-V cvc5-smtlib"] => verus_code! {
        use vstd::prelude::*;

        struct Node {
            next: Box<Option<Node>>,
        }

        impl Node {
            spec fn depth(&self) -> nat
                decreases self
            {
                match *self.next {
                    Option::Some(next) => 1 + next.depth(),
                    Option::None => 0,
                }
            }
        }
    } => Ok(())
}

#[test]
fn cvc5_solver_and_smtlib_options_are_mutually_exclusive() {
    let output =
        run_verus_raw(&["--version", "-V", "cvc5", "-V", "cvc5-smtlib"], std::path::Path::new("."));
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("`-V cvc5` and `-V cvc5-smtlib` are mutually exclusive")
    );
}

#[test]
fn cvc5_smtlib_emits_cvc5_encoding_with_z3() {
    let test_dir = tempfile::tempdir().expect("temporary test directory");
    let entry_file = test_dir.path().join("test.rs");
    let log_dir = test_dir.path().join("smt-log");
    std::fs::create_dir(&log_dir).expect("SMT log directory");
    std::fs::write(
        &entry_file,
        format!(
            "{}{}{}",
            FEATURE_PRELUDE,
            USE_PRELUDE,
            verus_code! {
                use vstd::prelude::*;

                struct Node {
                    next: Box<Option<Node>>,
                }

                impl Node {
                    spec fn depth(&self) -> nat
                        decreases self
                    {
                        match *self.next {
                            Option::Some(next) => 1 + next.depth(),
                            Option::None => 0,
                        }
                    }
                }
            }
        ),
    )
    .expect("test source");

    let log_dir_option = format!("--log-dir={}", log_dir.display());
    let output = run_verus(
        &["-V cvc5-smtlib", "--log-smt", &log_dir_option],
        test_dir.path(),
        &entry_file,
        true,
        false,
    );
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));

    let smt_files = std::fs::read_dir(&log_dir)
        .expect("read SMT log directory")
        .map(|entry| entry.expect("SMT log entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "smt2"))
        .collect::<Vec<_>>();
    assert_eq!(smt_files.len(), 1);
    let smt = std::fs::read_to_string(&smt_files[0]).expect("read SMT log file");
    assert!(smt.contains("(set-logic ALL)"));
    assert!(smt.contains("(declare-fun partial-order"));
    assert!(smt.contains("(set-option :auto_config false)"));
    assert!(!smt.contains(":skolemid"));
    assert!(!smt.contains("(set-option :incremental true)"));
}
