#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;
use verus_trust_audit::MANIFEST_VERSION;

const NO_CHEATING: &[&str] = &["--no-cheating"];

fn entry(crate_attr: &str, items: &str) -> (String, String) {
    let contents = format!(
        "{feature}\n{crate_attr}\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\n{items}\n",
        feature = FEATURE_PRELUDE,
    );
    ("test.rs".to_string(), contents)
}

fn module(name: &str, file_attr: &str, body: &str) -> (String, String) {
    let contents = format!(
        "{file_attr}\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\n\
         verus! {{\n{body}\n}}\n",
    );
    (format!("{name}.rs"), contents)
}

#[test]
fn untrusted_by_default() {
    let files = vec![entry("", "verus! { proof fn cheat() ensures false { assume(false); } }")];
    let err = verify_files("untrusted_by_default", files, "test.rs".to_string(), NO_CHEATING)
        .expect_err("expected an error");
    assert_vir_error_msg(err, "assume/admit not allowed with --no-cheating");
}

#[test]
fn trusted_crate_allows_assumptions() {
    let files = vec![entry(
        "#![verus::trusted]",
        "verus! { proof fn cheat() ensures false { assume(false); } }",
    )];
    assert!(
        verify_files(
            "trusted_crate_allows_assumptions",
            files,
            "test.rs".to_string(),
            NO_CHEATING,
        )
        .is_ok()
    );
}

#[test]
fn trusted_inline_module_inherits() {
    let files = vec![entry(
        "",
        "#[verus::trusted]\nmod trusted {\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\
         verus! { pub proof fn cheat() ensures false { assume(false); } }\n}",
    )];
    assert!(
        verify_files("trusted_inline_module_inherits", files, "test.rs".to_string(), NO_CHEATING,)
            .is_ok()
    );
}

#[test]
fn trusted_function_allows_assumptions() {
    let files = vec![entry(
        "",
        "verus! {\n\
         #[verus::trusted]\n\
         proof fn cheat() ensures false { assume(false); }\n\
         }",
    )];
    assert!(
        verify_files(
            "trusted_function_allows_assumptions",
            files,
            "test.rs".to_string(),
            NO_CHEATING,
        )
        .is_ok()
    );
}

#[test]
fn untrusted_item_overrides_trusted_parent() {
    let files = vec![entry(
        "#![verus::trusted]",
        "verus! {\n\
         #[verus::untrusted]\n\
         proof fn cheat() ensures false { assume(false); }\n\
         }",
    )];
    let err = verify_files(
        "untrusted_item_overrides_trusted_parent",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_vir_error_msg(err, "assume/admit not allowed with --no-cheating");
}

#[test]
fn trusted_child_below_untrusted_is_rejected() {
    let files = vec![entry(
        "",
        "#[verus::untrusted]\nmod locked {\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\
         verus! {\n\
         #[verus::trusted]\n\
         pub proof fn cheat() ensures false { assume(false); }\n\
         }\n}",
    )];
    let err = verify_files(
        "trusted_child_below_untrusted_is_rejected",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "cannot be marked trusted");
}

#[test]
fn trusted_impl_inherits_and_method_can_override() {
    let files = vec![entry(
        "",
        "verus! {\n\
         #[verus::trusted]\n\
         struct S;\n\
         #[verus::trusted]\n\
         impl S {\n\
             proof fn allowed() ensures false { assume(false); }\n\
             #[verus::untrusted]\n\
             proof fn rejected() ensures false { assume(false); }\n\
         }\n\
         }",
    )];
    let err = verify_files(
        "trusted_impl_inherits_and_method_can_override",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_vir_error_msg(err, "assume/admit not allowed with --no-cheating");
}

#[test]
fn conflicting_trust_attributes_are_rejected() {
    let files = vec![entry(
        "",
        "verus! {\n\
         #[verus::trusted]\n\
         #[verus::untrusted]\n\
         proof fn f() {}\n\
         }",
    )];
    let err = verify_files(
        "conflicting_trust_attributes_are_rejected",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "at most one");
}

#[test]
fn trusted_body_reference_to_untrusted_fails() {
    let files = vec![entry(
        "",
        "verus! {\n\
         proof fn helper() {}\n\
         #[verus::trusted]\n\
         proof fn caller() { helper(); }\n\
         }",
    )];
    let err = verify_files(
        "trusted_body_reference_to_untrusted_fails",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "trusted code may not reference an untrusted item");
}

#[test]
fn trusted_type_reference_to_untrusted_fails() {
    let files = vec![entry(
        "",
        "verus! {\n\
         struct U;\n\
         #[verus::trusted]\n\
         struct T { u: U }\n\
         }",
    )];
    let err = verify_files(
        "trusted_type_reference_to_untrusted_fails",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "trusted code may not reference an untrusted item");
}

#[test]
fn trusted_spec_ignores_body_references() {
    let files = vec![entry(
        "",
        "verus! {\n\
         proof fn helper() {}\n\
         #[verus::trusted(spec)]\n\
         proof fn caller() { helper(); }\n\
         }",
    )];
    assert!(
        verify_files(
            "trusted_spec_ignores_body_references",
            files,
            "test.rs".to_string(),
            NO_CHEATING,
        )
        .is_ok()
    );
}

#[test]
fn trusted_spec_body_rejects_assumptions() {
    let files = vec![entry(
        "#![verus::trusted]",
        "verus! {\n\
         #[verus::trusted(spec)]\n\
         proof fn caller() ensures false { assume(false); }\n\
         }",
    )];
    let err = verify_files(
        "trusted_spec_body_rejects_assumptions",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_vir_error_msg(err, "assume/admit not allowed with --no-cheating");
}

#[test]
fn trusted_spec_checks_requires_and_ensures() {
    let files = vec![entry(
        "",
        "verus! {\n\
         spec fn untrusted_spec() -> bool { true }\n\
         #[verus::trusted(spec)]\n\
         proof fn caller()\n\
             requires untrusted_spec(),\n\
             ensures untrusted_spec(),\n\
         {}\n\
         }",
    )];
    let err = verify_files(
        "trusted_spec_checks_requires_and_ensures",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "trusted code may not reference an untrusted item");
}

#[test]
fn trusted_spec_checks_type_signature() {
    let files = vec![entry(
        "",
        "verus! {\n\
         struct U;\n\
         #[verus::trusted(spec)]\n\
         fn caller(_u: U) {}\n\
         }",
    )];
    let err = verify_files(
        "trusted_spec_checks_type_signature",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "trusted code may not reference an untrusted item");
}

#[test]
fn external_body_obeys_item_trust() {
    let trusted_files = vec![entry(
        "",
        "verus! {\n\
         #[verus::trusted]\n\
         #[verifier::external_body]\n\
         fn allowed() {}\n\
         }",
    )];
    assert!(
        verify_files(
            "external_body_obeys_item_trust_allowed",
            trusted_files,
            "test.rs".to_string(),
            NO_CHEATING,
        )
        .is_ok()
    );

    let untrusted_files = vec![entry(
        "",
        "verus! {\n\
         #[verifier::external_body]\n\
         fn rejected() {}\n\
         }",
    )];
    let err = verify_files(
        "external_body_obeys_item_trust_rejected",
        untrusted_files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_vir_error_msg(err, "external_body/assume_specification not allowed with --no-cheating");

    let trusted_spec_files = vec![entry(
        "",
        "verus! {\n\
         #[verus::trusted(spec)]\n\
         #[verifier::external_body]\n\
         fn rejected() {}\n\
         }",
    )];
    let err = verify_files(
        "external_body_obeys_item_trust_trusted_spec_rejected",
        trusted_spec_files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_vir_error_msg(err, "external_body/assume_specification not allowed with --no-cheating");
}

#[test]
fn trust_attributes_are_inert_without_flag() {
    let files = vec![entry(
        "",
        "#[verus::untrusted]\nmod locked {\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\
         verus! {\n\
         #[verus::trusted]\n\
         pub proof fn cheat() ensures false { assume(false); }\n\
         }\n}",
    )];
    assert!(
        verify_files("trust_attributes_are_inert_without_flag", files, "test.rs".to_string(), &[],)
            .is_ok()
    );
}

#[test]
fn emits_trust_manifest() {
    let temp = tempfile::tempdir().unwrap();
    let manifest_path = temp.path().join("tcb.json");
    let manifest_arg = manifest_path.to_string_lossy().into_owned();
    let files = vec![entry(
        "",
        "verus! {\n\
         #[verus::trusted]\n\
         proof fn trusted() { assume(true); }\n\
         proof fn untrusted() {}\n\
         }",
    )];
    verify_files(
        "emits_trust_manifest",
        files,
        "test.rs".to_string(),
        &["--no-cheating", &format!("--emit-trust-manifest={manifest_arg}")],
    )
    .unwrap();
    let manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(manifest_path).unwrap()).unwrap();
    assert_eq!(manifest["format_version"], MANIFEST_VERSION);
    assert!(
        manifest["nodes"].as_array().unwrap().iter().any(|node| node["name"]
            .as_str()
            .unwrap()
            .ends_with("trusted")
            && node["trust"] == "trusted")
    );
}
