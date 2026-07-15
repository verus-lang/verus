#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests the `#[deny/allow(verus::assumptions)]` lints of `--no-cheating`. We use
// `verify_files` (real multi-file crates) so the "file-level module" rule can be exercised

const NO_CHEATING: &[&str] = &["--no-cheating"];

/// The crate-root (entry) file: feature prelude, optional `#![deny(verus::assumptions)]`, items.
fn entry(deny: bool, items: &str) -> (String, String) {
    let deny_attr = if deny { "#![deny(verus::assumptions)]\n" } else { "" };
    let contents = format!(
        "{feature}\n{deny}#[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\n{items}\n",
        feature = FEATURE_PRELUDE,
        deny = deny_attr,
        items = items,
    );
    ("test.rs".to_string(), contents)
}

/// A non-root module file: imports + a `verus! { .. }` block wrapping `body`.
fn module(name: &str, body: &str) -> (String, String) {
    let contents = format!(
        "#[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\n\
         verus! {{\n{body}\n}}\n",
        body = body,
    );
    (format!("{name}.rs"), contents)
}

// Crate-root `#![deny(verus::assumptions)]` requirement

#[test]
fn root_deny_missing() {
    let files = vec![
        entry(
            false, // no `#![deny(verus::assumptions)]`
            "#[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() { assert(true); } }",
        ),
        module("trusted", "pub proof fn ok() {}"),
    ];
    let err = verify_files("root_deny_missing", files, "test.rs".to_string(), NO_CHEATING)
        .expect_err("expected an error");
    assert_vir_error_msg(err, "the crate root must contain `#![deny(verus::assumptions)]`");
}

#[test]
fn root_deny_present_clean_ok() {
    let files = vec![entry(true, "verus! { proof fn honest() { assert(1 + 1 == 2); } }")];
    let result =
        verify_files("root_deny_present_clean_ok", files, "test.rs".to_string(), NO_CHEATING);
    assert!(result.is_ok());
}

#[test]
fn assume_in_deny_module_fails() {
    // `assume` in a deny module is still rejected even when an allow-module exists.
    let files = vec![
        entry(
            true,
            "#[allow(verus::assumptions)]\nmod trusted;\n\n\
             verus! { proof fn dishonest() ensures false { assume(false); } }",
        ),
        module("trusted", "pub proof fn ok() {}"),
    ];
    let err =
        verify_files("assume_in_deny_module_fails", files, "test.rs".to_string(), NO_CHEATING)
            .expect_err("expected an error");
    assert_vir_error_msg(err, "assume/admit not allowed with --no-cheating");
}

// `#[allow(verus::assumptions)]` placement rules

#[test]
fn allow_on_file_module_ok() {
    // `assume` inside a file-level allow-module is accepted.
    let files = vec![
        entry(
            true,
            "#[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() {} }",
        ),
        module("trusted", "pub proof fn cheat() ensures false { assume(false); }"),
    ];
    let result = verify_files("allow_on_file_module_ok", files, "test.rs".to_string(), NO_CHEATING);
    assert!(result.is_ok());
}

#[test]
fn allow_on_inline_module_fails() {
    let files = vec![entry(
        true,
        "#[allow(verus::assumptions)]\nmod inline_mod {\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\
         verus! { pub proof fn c() ensures false { assume(false); } }\n}",
    )];
    let err =
        verify_files("allow_on_inline_module_fails", files, "test.rs".to_string(), NO_CHEATING)
            .expect_err("expected an error");
    assert_vir_error_msg(err, "may only be placed on a file-level module");
}

#[test]
fn allow_on_function_fails() {
    let files = vec![entry(
        true,
        "verus! {\n#[allow(verus::assumptions)]\nproof fn honest() ensures false { assume(false); }\n}",
    )];
    let err = verify_files("allow_on_function_fails", files, "test.rs".to_string(), NO_CHEATING)
        .expect_err("expected an error");
    assert_vir_error_msg(err, "may only be placed on a file-level module");
}

#[test]
fn allow_in_non_root_module_fails() {
    // `allow` written inside a module (not the crate root) is rejected.
    let files = vec![
        entry(
            true,
            "#[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() {} }",
        ),
        module(
            "trusted",
            "#[allow(verus::assumptions)]\npub proof fn inner() ensures false { assume(false); }",
        ),
    ];
    let err =
        verify_files("allow_in_non_root_module_fails", files, "test.rs".to_string(), NO_CHEATING)
            .expect_err("expected an error");
    assert_vir_error_msg(err, "may only be placed on a file-level module");
}

// Transitive-closure (reference) rules

#[test]
fn allow_references_allow_ok() {
    let files = vec![
        entry(
            true,
            "#[allow(verus::assumptions)]\nmod helper;\n\
             #[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() {} }",
        ),
        module("helper", "pub open spec fn val() -> int { 7 }"),
        module(
            "trusted",
            "pub proof fn uses_allow() ensures crate::helper::val() == 7 { assume(false); }",
        ),
    ];
    let result =
        verify_files("allow_references_allow_ok", files, "test.rs".to_string(), NO_CHEATING);
    assert!(result.is_ok());
}

#[test]
fn allow_references_deny_via_path_fails() {
    let files = vec![
        entry(
            true,
            "mod helper;\n#[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() {} }",
        ),
        module("helper", "pub open spec fn val() -> int { 7 }"),
        module("trusted", "pub proof fn uses_deny() ensures crate::helper::val() == 7 {}"),
    ];
    let err = verify_files(
        "allow_references_deny_via_path_fails",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "may not reference items in non-allow modules");
}

#[test]
fn allow_references_deny_via_use_fails() {
    let files = vec![
        entry(
            true,
            "mod helper;\n#[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() {} }",
        ),
        module("helper", "pub open spec fn val() -> int { 7 }"),
        module(
            "trusted",
            "use crate::helper::val;\npub proof fn uses_deny() ensures val() == 7 {}",
        ),
    ];
    let err = verify_files(
        "allow_references_deny_via_use_fails",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "may not reference items in non-allow modules");
}

#[test]
fn deny_references_allow_ok() {
    // Reverse direction is fine: a deny module may freely use an allow-module.
    let files = vec![
        entry(
            true,
            "#[allow(verus::assumptions)]\nmod trusted;\n\n\
             verus! { proof fn honest() ensures crate::trusted::val() == 7 { } }",
        ),
        module(
            "trusted",
            "pub open spec fn val() -> int { 7 }\npub proof fn cheat() ensures false { assume(false); }",
        ),
    ];
    let result =
        verify_files("deny_references_allow_ok", files, "test.rs".to_string(), NO_CHEATING);
    assert!(result.is_ok());
}

#[test]
fn allow_subtree_inherits_ok() {
    // A nested submodule inside a file-level allow-module inherits the allowance.
    let files = vec![
        entry(
            true,
            "#[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() {} }",
        ),
        module(
            "trusted",
            "pub mod sub {\n\
             #[allow(unused_imports)] use verus_builtin::*;\n\
             #[allow(unused_imports)] use verus_builtin_macros::*;\n\
             verus! { pub proof fn deep() ensures false { assume(false); } }\n}",
        ),
    ];
    let result =
        verify_files("allow_subtree_inherits_ok", files, "test.rs".to_string(), NO_CHEATING);
    assert!(result.is_ok());
}

// external_body / assume_specification in allow-modules

#[test]
fn external_body_in_allow_ok() {
    let files = vec![
        entry(
            true,
            "#[allow(verus::assumptions)]\nmod trusted;\n\nverus! { proof fn honest() {} }",
        ),
        module("trusted", "#[verifier::external_body]\npub fn ext() {}"),
    ];
    let result =
        verify_files("external_body_in_allow_ok", files, "test.rs".to_string(), NO_CHEATING);
    assert!(result.is_ok());
}

#[test]
fn external_body_in_deny_fails() {
    let files = vec![entry(true, "verus! {\n#[verifier::external_body]\nfn ext() {}\n}")];
    let err =
        verify_files("external_body_in_deny_fails", files, "test.rs".to_string(), NO_CHEATING)
            .expect_err("expected an error");
    assert_vir_error_msg(err, "external_body/assume_specification not allowed with --no-cheating");
}

// Inert when `--no-cheating` is not passed

#[test]
fn inert_without_flag() {
    // No `--no-cheating`: no `#![deny]` required, and `assume` is permitted everywhere.
    let files = vec![entry(false, "verus! { proof fn cheat() ensures false { assume(false); } }")];
    let result = verify_files("inert_without_flag", files, "test.rs".to_string(), &[]);
    assert!(result.is_ok());
}
