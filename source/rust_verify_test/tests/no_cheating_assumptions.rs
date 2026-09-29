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
    assert_vir_error_msg(err, "`assume`/`admit` not allowed with `--no-cheating`");
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
    assert_vir_error_msg(err, "`assume`/`admit` not allowed with `--no-cheating`");
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
    assert_vir_error_msg(err, "`assume`/`admit` not allowed with `--no-cheating`");
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
    assert_vir_error_msg(err, "`assume`/`admit` not allowed with `--no-cheating`");
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
    assert_vir_error_msg(
        err,
        "`external_body`/`assume_specification` not allowed with `--no-cheating`",
    );

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
    assert_vir_error_msg(
        err,
        "`external_body`/`assume_specification` not allowed with `--no-cheating`",
    );
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

fn expect_ok(name: &str, files: Vec<(String, String)>) {
    let result = verify_files(name, files, "test.rs".to_string(), NO_CHEATING);
    if let Err(err) = result {
        panic!("expected success, got errors: {:#?}", err.errors);
    }
}

#[test]
fn trusted_method_may_use_untrusted_impl_generic_params() {
    let files = vec![entry(
        "",
        "verus! {\n\
         pub struct S<T>(pub T);\n\
         impl<T, const N: usize> S<[T; N]> {\n\
             #[verus::trusted]\n\
             pub proof fn f<'a>(x: &'a T) ensures false { assume(false); }\n\
         }\n\
         }",
    )];
    expect_ok("trusted_method_may_use_untrusted_impl_generic_params", files);
}

#[test]
fn trusted_nested_module_may_use_imports() {
    let files = vec![entry(
        "",
        "verus! { pub proof fn helper() {} }\n\
         #[verus::trusted]\n\
         mod m {\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\
         #[allow(unused_imports)] use super::*;\n\
         #[allow(unused_imports)] use super::helper;\n\
         verus! { proof fn cheat() ensures false { assume(false); } }\n\
         }",
    )];
    expect_ok("trusted_nested_module_may_use_imports", files);
}

#[test]
fn trusted_use_does_not_launder_untrusted_items() {
    let files = vec![entry(
        "",
        "verus! { pub proof fn helper() {} }\n\
         #[verus::trusted]\n\
         mod m {\n\
         #[allow(unused_imports)] use verus_builtin::*;\n\
         #[allow(unused_imports)] use verus_builtin_macros::*;\n\
         use super::helper;\n\
         verus! { proof fn caller() { helper(); } }\n\
         }",
    )];
    let err = verify_files(
        "trusted_use_does_not_launder_untrusted_items",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "trusted code may not reference an untrusted item");
}

#[test]
fn trusted_enum_arrow_and_is_helpers() {
    let files = vec![entry(
        "",
        "verus! {\n\
         #[verus::trusted]\n\
         pub enum E { A(u8), B { x: u8 } }\n\
         #[verus::trusted]\n\
         pub open spec fn f(e: E) -> u8 {\n\
             if e is A { e->A_0 } else { e->x }\n\
         }\n\
         }",
    )];
    expect_ok("trusted_enum_arrow_and_is_helpers", files);
}

#[test]
fn untrusted_enum_arrow_helpers_still_rejected() {
    let files = vec![entry(
        "",
        "verus! {\n\
         pub enum E { A(u8), B }\n\
         #[verus::trusted]\n\
         pub open spec fn f(e: E) -> u8 { e->A_0 }\n\
         }",
    )];
    let err = verify_files(
        "untrusted_enum_arrow_helpers_still_rejected",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "trusted code may not reference an untrusted item");
}

#[test]
fn trusted_global_size_of() {
    let files = vec![entry(
        "",
        "use vstd::prelude::*;\nverus! {\n\
         #[verus::trusted]\n\
         global size_of usize == 8;\n\
         }",
    )];
    let result = verify_files_vstd(
        "trusted_global_size_of",
        files,
        "test.rs".to_string(),
        true,
        NO_CHEATING,
    );
    if let Err(err) = result {
        panic!("expected success, got errors: {:#?}", err.errors);
    }
}

#[test]
fn untrusted_global_size_of_rejected() {
    let files = vec![entry("", "use vstd::prelude::*;\nverus! { global size_of usize == 8; }")];
    let err = verify_files_vstd(
        "untrusted_global_size_of_rejected",
        files,
        "test.rs".to_string(),
        true,
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "not allowed with `--no-cheating`");
}

#[test]
fn untrusted_enum_in_trusted_module_keeps_helpers_untrusted() {
    let files = vec![entry(
        "#![verus::trusted]",
        "verus! {\n\
         #[verus::untrusted]\n\
         pub enum E { A(u8), B }\n\
         pub open spec fn f(e: E) -> u8 { e->A_0 }\n\
         }",
    )];
    let err = verify_files(
        "untrusted_enum_in_trusted_module_keeps_helpers_untrusted",
        files,
        "test.rs".to_string(),
        NO_CHEATING,
    )
    .expect_err("expected an error");
    assert_any_vir_error_msg(err, "trusted code may not reference an untrusted item");
}

/// Verify `items` (inside `verus!`, with vstd) under `--no-cheating`.
/// `expected_err` is `None` for success, or a fragment of the expected error message.
fn check_vstd(name: &str, items: &str, expected_err: Option<&str>) {
    let files = vec![entry("", &format!("use vstd::prelude::*;\nverus! {{\n{items}\n}}"))];
    let result = verify_files_vstd(name, files, "test.rs".to_string(), true, NO_CHEATING);
    match (result, expected_err) {
        (Ok(()), None) => {}
        (Err(err), None) => panic!("expected success, got errors: {:#?}", err.errors),
        (Ok(()), Some(msg)) => panic!("expected an error containing {msg:?}"),
        (Err(err), Some(msg)) => assert_any_vir_error_msg(err, msg),
    }
}

const NOT_CLOSED: &str = "trusted code must be transitively closed";

#[test]
fn trusted_spec_children_cannot_be_trusted() {
    // Otherwise a nested trusted axiom could discharge the trusted(spec) function's ensures.
    check_vstd(
        "trusted_spec_children_cannot_be_trusted",
        "#[verus::trusted(spec)]\n\
         pub fn f() -> (r: u64) ensures r == 1 {\n\
             #[verus::trusted]\n\
             #[verifier::external_body]\n\
             proof fn hidden_axiom() ensures false {}\n\
             proof { hidden_axiom(); }\n\
             0\n\
         }",
        Some("cannot be marked trusted"),
    );
}

#[test]
fn trusted_spec_children_are_untrusted() {
    check_vstd(
        "trusted_spec_children_are_untrusted",
        "#[verus::trusted(spec)]\n\
         pub fn f() -> (r: u64) ensures r == 1 {\n\
             proof fn nested() ensures false { assume(false); }\n\
             proof { nested(); }\n\
             0\n\
         }",
        Some("`assume`/`admit` not allowed with `--no-cheating`"),
    );
}

#[test]
fn trusted_type_relative_path_to_untrusted_item() {
    check_vstd(
        "trusted_type_relative_path_to_untrusted_item",
        "#[verus::trusted]\n\
         pub struct S { pub x: u64 }\n\
         #[verus::trusted]\n\
         pub fn get(s: &S) -> (r: u64) ensures S::meaning(r) { s.x }\n\
         impl S { pub open spec fn meaning(r: u64) -> bool { true } }",
        Some(NOT_CLOSED),
    );
}

#[test]
fn trusted_pattern_path_to_untrusted_const() {
    check_vstd(
        "trusted_pattern_path_to_untrusted_const",
        "#[verus::trusted]\n\
         pub struct S;\n\
         impl S { pub const C: u64 = 3; }\n\
         #[verus::trusted]\n\
         pub fn f(x: u64) -> bool { match x { S::C => true, _ => false } }",
        Some(NOT_CLOSED),
    );
}

const UNTRUSTED_VIEW: &str =
    "impl View for S { type V = u64; open spec fn view(&self) -> u64 { self.x } }";

#[test]
fn trusted_spec_uses_untrusted_trait_impl() {
    check_vstd(
        "trusted_spec_uses_untrusted_trait_impl",
        &format!(
            "#[verus::trusted]\n\
             pub struct S {{ pub x: u64 }}\n\
             #[verus::trusted]\n\
             pub fn get(s: &S) -> (r: u64) ensures r == s@ {{ s.x }}\n\
             {UNTRUSTED_VIEW}"
        ),
        Some("untrusted impl `<S as vstd::string::View>`"),
    );
}

#[test]
fn trusted_spec_signature_uses_untrusted_trait_impl() {
    check_vstd(
        "trusted_spec_signature_uses_untrusted_trait_impl",
        &format!(
            "#[verus::trusted]\n\
             pub struct S {{ pub x: u64 }}\n\
             #[verus::trusted(spec)]\n\
             pub fn get(s: &S) -> (r: u64) ensures r == s@ {{ s.x }}\n\
             {UNTRUSTED_VIEW}"
        ),
        Some("untrusted impl"),
    );
}

#[test]
fn trusted_impl_with_untrusted_item() {
    check_vstd(
        "trusted_impl_with_untrusted_item",
        "#[verus::trusted]\n\
         pub struct S { pub x: u64 }\n\
         #[verus::trusted]\n\
         pub fn get(s: &S) -> (r: u64) ensures r == s@ { s.x }\n\
         #[verus::trusted]\n\
         impl View for S {\n\
             type V = u64;\n\
             #[verus::untrusted] open spec fn view(&self) -> u64 { self.x }\n\
         }",
        Some("untrusted impl item"),
    );
}

#[test]
fn trusted_generic_instantiation_uses_untrusted_impl() {
    check_vstd(
        "trusted_generic_instantiation_uses_untrusted_impl",
        "#[verus::trusted]\n\
         pub trait Tr { spec fn m(&self) -> bool; }\n\
         #[verus::trusted]\n\
         pub struct S;\n\
         #[verus::trusted]\n\
         pub open spec fn holds<T: Tr>(t: T) -> bool { t.m() }\n\
         #[verus::trusted]\n\
         #[verifier::external_body]\n\
         pub proof fn ax() ensures holds(S) {}\n\
         impl Tr for S { open spec fn m(&self) -> bool { true } }",
        Some("untrusted impl `<S as Tr>`"),
    );
}

#[test]
fn trusted_operator_uses_untrusted_impl() {
    check_vstd(
        "trusted_operator_uses_untrusted_impl",
        "#[verus::trusted]\n\
         #[derive(Clone, Copy)]\n\
         pub struct S { pub x: u64 }\n\
         #[verus::trusted]\n\
         pub fn add(a: S, b: S) -> S { a + b }\n\
         impl core::ops::Add for S {\n\
             type Output = S;\n\
             fn add(self, o: S) -> S { S { x: 0 } }\n\
         }",
        Some("untrusted impl `<S as std::ops::Add>`"),
    );
}

#[test]
fn trusted_projection_uses_untrusted_impl() {
    check_vstd(
        "trusted_projection_uses_untrusted_impl",
        "#[verus::trusted]\n\
         pub trait Tr { type Out; }\n\
         #[verus::trusted]\n\
         pub struct S;\n\
         #[verus::trusted]\n\
         pub open spec fn f(x: <S as Tr>::Out) -> bool { true }\n\
         impl Tr for S { type Out = u8; }",
        Some("untrusted impl `<S as Tr>`"),
    );
}

#[test]
fn trusted_drop_uses_untrusted_destructor() {
    check_vstd(
        "trusted_drop_uses_untrusted_destructor",
        "#[verus::trusted]\n\
         pub struct S { pub x: u64 }\n\
         #[verus::trusted]\n\
         pub fn make() { let s = S { x: 0 }; }\n\
         impl Drop for S { fn drop(&mut self) opens_invariants none no_unwind {} }",
        Some("untrusted destructor"),
    );
}

#[test]
fn trusted_uses_trusted_impl() {
    check_vstd(
        "trusted_uses_trusted_impl",
        "#[verus::trusted]\n\
         pub struct S { pub x: u64 }\n\
         #[verus::trusted]\n\
         pub fn get(s: &S) -> (r: u64) ensures r == s@ { s.x }\n\
         #[verus::trusted]\n\
         impl View for S { type V = u64; open spec fn view(&self) -> u64 { self.x } }",
        None,
    );
}

#[test]
fn trusted_uses_derived_impls_of_trusted_type() {
    check_vstd(
        "trusted_uses_derived_impls_of_trusted_type",
        "#[verus::trusted]\n\
         #[derive(Clone, Copy, PartialEq, Eq)]\n\
         pub struct S { pub x: u64 }\n\
         #[verus::trusted]\n\
         pub fn dup(s: &S) -> (r: (S, S)) { (*s, s.clone()) }",
        None,
    );
}

#[test]
fn trusted_generic_bound_is_not_resolved() {
    check_vstd(
        "trusted_generic_bound_is_not_resolved",
        "#[verus::trusted]\n\
         pub fn get<T: View>(t: &T) -> (r: bool) ensures r == (t@ == t@) { true }",
        None,
    );
}

#[test]
fn untrusted_code_may_instantiate_trusted_code_with_untrusted_impls() {
    check_vstd(
        "untrusted_code_may_instantiate_trusted_code_with_untrusted_impls",
        "#[verus::trusted]\n\
         pub trait Tr { spec fn m(&self) -> bool; }\n\
         #[verus::trusted]\n\
         pub open spec fn holds<T: Tr>(t: T) -> bool { t.m() }\n\
         pub struct U;\n\
         impl Tr for U { open spec fn m(&self) -> bool { true } }\n\
         pub proof fn uses() { assert(holds(U)); }",
        None,
    );
}

#[test]
fn trusted_spec_body_may_use_untrusted_impls() {
    check_vstd(
        "trusted_spec_body_may_use_untrusted_impls",
        "pub struct U { pub x: u64 }\n\
         impl View for U { type V = u64; open spec fn view(&self) -> u64 { self.x } }\n\
         #[verus::trusted(spec)]\n\
         pub fn get(x: u64) -> (r: u64) ensures r == x {\n\
             let u = U { x };\n\
             assert(u@ == x);\n\
             u.x\n\
         }",
        None,
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
