#![feature(rustc_private)]
#![feature(internal_output_capture)]

mod common;

#[test]
fn basic1() {
    let status = common::rust_verify_with_pervasive(
        indoc::indoc!(
            r###"
        fn basic1() {
            assert(true);
        }
    "###
        )
        .to_string(),
    );
    assert!(status.is_ok());
}

#[test]
fn basic2() {
    let err = common::rust_verify_with_pervasive(
        indoc::indoc!(
            r###"
        fn basic2() {
            assert(false); // FAILS
        }
    "###
        )
        .to_string(),
    )
    .unwrap_err();
    assert_eq!(err.len(), 1);
    assert!(err[0].0.as_ref().expect("span").test_span_line.contains("FAILS"));
}
