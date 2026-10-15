// Branch-condition (MC/DC) coverage tests for command-line options that the test macros do not pass
// (logging, profiling, module and function filters, SMT options, timing). Each test runs the verifier
// binary on a program with those options; its comment names the decisions (file:line) and conditions
// (atoms, numbered from 0 in source order) for which it supplies an evaluation no other test supplies.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use tempfile::TempDir;

/// Runs the verifier binary on `code` with `args` ("LOG_DIR" stands for a fresh directory) and checks the
/// exit status, the "verification results" line (when given) and the sorted list of error lines.
fn check_cli(code: &str, args: &[&str], success: bool, results: Option<&str>, errors: &[&str]) {
    let tempdir = TempDir::new().expect("temp dir");
    let entry = tempdir.path().join("test.rs");
    std::fs::write(&entry, code).expect("write source file");
    let log_dir = tempdir.path().join("log");
    let log_dir = log_dir.to_str().unwrap();
    let mut a: Vec<&str> =
        args.iter().map(|x| if *x == "LOG_DIR" { log_dir } else { *x }).collect();
    a.push(entry.to_str().unwrap());
    let output = run_verus_raw(&a, tempdir.path());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.success(), success, "stdout:\n{}\nstderr:\n{}", stdout, stderr);
    if let Some(r) = results {
        assert!(stdout.lines().any(|l| l.contains(r)), "missing {:?} in stdout:\n{}", r, stdout);
    }
    let mut found: Vec<&str> = stderr
        .lines()
        .filter(|l| l.starts_with("error") && !l.starts_with("error: aborting due to"))
        .filter(|l| l.starts_with("error: ") || l.starts_with("error["))
        .collect();
    found.sort();
    assert_eq!(found, errors.to_vec(), "stderr:\n{}", stderr);
}

// Independence pair for air/src/printer.rs:442 atom 0 `spans.len() == 0`, atom 1 `filter.is_none()`
#[test]
fn air_printer_nolabel_filters() {
    let code = r#"use vstd::prelude::*;
verus! {
proof fn t(x: int, b: bool) {
    inline_air_stmt("(assert (location () () true))");
    inline_air_stmt("(assert (location () (f) true))");
    inline_air_stmt("(assert () () true)");
    inline_air_stmt("(assert () (f) true)");
    inline_air_stmt("(assume (axiom_location () () true))");
    inline_air_stmt("(assume (axiom_location () (f) true))");
}
}
"#;
    check_cli(
        code,
        &["-V", "allow-inline-air", "--crate-type=lib", "--log", "air", "--log-dir", "LOG_DIR"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/driver.rs:36 atom 1; rust_verify/src/user_filter.rs:76 atom 0; vir/src/ast_util.rs:64 atoms 0, 1
#[test]
fn ast_util_verify_module_prefix() {
    let code = r#"use vstd::prelude::*;
verus! {
mod a {
    use vstd::prelude::*;
    pub proof fn ok_a() { assert(1 + 1 == 2); }
    pub mod b {
        use vstd::prelude::*;
        pub proof fn ok_b() { assert(2 + 2 == 4); }
    }
}
mod c {
    use vstd::prelude::*;
    pub proof fn not_selected() { assert(1 + 1 == 3); }
}
proof fn root_not_selected() { assert(false); }
fn main() {}
}
"#;
    check_cli(
        code,
        &["--verify-module", "a"],
        true,
        Some("verification results:: 2 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:1537 atom 2 `self.args.capture_profiles`
#[test]
fn capture_profiles_spinoff() {
    let code = r#"use vstd::prelude::*;
verus! {
proof fn nl(x: int, y: int) requires 0 <= x, 0 <= y ensures x * y >= 0 {
    assert(x * y >= 0) by (nonlinear_arith) requires 0 <= x, 0 <= y;
}
proof fn bv(x: u8) { assert(x & 0 == 0) by (bit_vector); }
proof fn empty() {}
fn main() {}
}
"#;
    check_cli(
        code,
        &["-V", "capture-profiles"],
        true,
        Some("verification results:: 6 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/config.rs:701 atom 0 `matches.opt_present(OPT_TIME)`
#[test]
fn cli_time() {
    let code = r#"use vstd::prelude::*;
verus! {
fn f(x: u8) ensures x <= 255 {}
fn main() {}
}
"#;
    check_cli(code, &["--time"], true, Some("verification results:: 2 verified, 0 errors"), &[]);
}

// Independence pair for rust_verify/src/config.rs:701 atom 1 `matches.opt_present(OPT_TIME_EXPA...`
#[test]
fn cli_time_expanded() {
    let code = r#"use vstd::prelude::*;
verus! {
fn f(x: u8) ensures x <= 255 {}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--time-expanded"],
        true,
        Some("verification results:: 2 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/user_filter.rs:76 atom 1 `args.verify_only_module.is_empty()`
#[test]
fn cli_verify_only_module() {
    let code = r#"use vstd::prelude::*;
verus! {
mod m {
    use vstd::prelude::*;
    pub fn f(x: u8) ensures x <= 255 {}
    pub mod n {
    use vstd::prelude::*;
        pub fn bad(x: u8) ensures x < 255 {} // would fail
    }
}
fn h(x: u8) ensures x < 255 {} // would fail
fn main() {}
}
"#;
    check_cli(
        code,
        &["--verify-only-module", "m"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/user_filter.rs:276 atom 0 `left_wildcard`
#[test]
fn cli_vfn_left_wild() {
    let code = r#"use vstd::prelude::*;
verus! {
mod m {
    use vstd::prelude::*;
    pub fn pre_ok_suf(x: u8) ensures x <= 255 {}
    pub fn pre_ok(x: u8) ensures x <= 255 {}
    pub fn ok_suf(x: u8) ensures x <= 255 {}
    pub fn bad_one(x: u8) ensures x < 255 {} // would fail
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--verify-only-module", "m", "--verify-function", "*_suf"],
        true,
        Some("verification results:: 2 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/user_filter.rs:278 atom 1 `right_wildcard`
#[test]
fn cli_vfn_right_wild() {
    let code = r#"use vstd::prelude::*;
verus! {
mod m {
    use vstd::prelude::*;
    pub fn pre_ok_suf(x: u8) ensures x <= 255 {}
    pub fn pre_ok(x: u8) ensures x <= 255 {}
    pub fn ok_suf(x: u8) ensures x <= 255 {}
    pub fn bad_one(x: u8) ensures x < 255 {} // would fail
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--verify-only-module", "m", "--verify-function", "pre_*"],
        true,
        Some("verification results:: 2 verified, 0 errors"),
        &[],
    );
}

// Independence pair for air/src/context.rs:368 atom 0 `option == "rlimit"`, atom 1 `write_to_logs`, atom 2 `matches!(self.solver, SmtSolver::Z3)`
#[test]
fn context_003_smt_option_kinds_probe() {
    let code = r#"use vstd::prelude::*;
verus! {
proof fn t(x: int) { assert(x + 1 > x + 1); }
}
"#;
    check_cli(
        code,
        &[
            "--smt-option",
            "rlimit=1000000",
            "--smt-option",
            "encoding=unicode",
            "--smt-option",
            "smt.delay_units=false",
            "--smt-option",
            "smt.qi.eager_threshold=99.5",
            "--crate-type=lib",
        ],
        false,
        Some("verification results:: 0 verified, 1 errors"),
        &["error: assertion failed"],
    );
}

// Independence pair for vir/src/context.rs:387 atom 1 `!candidate.x.external_trait_blanket`
#[test]
fn context_extension_blanket_candidate() {
    let code = r#"use vstd::prelude::*;
verus! {
#[verifier::external]
trait T<A> {
    fn f(&self, a: A) -> usize;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(TSpec via TSpecImpl)]
trait Ex<A> {
    type ExternalTraitSpecificationFor: T<A>;
    fn f(&self, a: A) -> (r: usize)
        requires self.s(a)
        ensures r > 7;
    spec fn s(&self, a: A) -> bool;
}

#[verus::internal(external_trait_blanket)]
impl T<u8> for u32 {
    fn f(&self, a: u8) -> (r: usize) { 10 }
}

impl TSpecImpl<u8> for u32 {
    spec fn s(&self, a: u8) -> bool { a == 6 }
}

proof fn test(u: u32) {
    assert(TSpec::s(&u, 6));
}
} // verus!
fn main() {}
"#;
    check_cli(
        code,
        &["--no-trait-conflicts"],
        false,
        None,
        &[
            "error: impl for test::TSpec must have a matching impl for test::T, with the same type parameter names and trait arguments",
        ],
    );
}

// Independence pair for rust_verify/src/driver.rs:132 atom 1 `!has_stable_attr(&map, owner_id)`
#[test]
fn core_mode_stable_attr() {
    let code = r#"#![feature(staged_api)]
#![stable(feature = "rust1", since = "1.0.0")]
#![allow(unused_attributes, unused_imports, dead_code, internal_features)]
#![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]
#![cfg_attr(verus_keep_ghost, feature(fn_traits))]

#[verifier::external]
#[path="BUILTIN_PATH"]
mod verus_builtin;

use verus_builtin_macros::*;

verus! {
#[stable(feature = "rust1", since = "1.0.0")]
pub fn f(x: u8) -> (r: u8) ensures r == x { x }
}

#[stable(feature = "rust1", since = "1.0.0")]
pub fn g(x: u8) -> u8 { x }

fn main() {}
"#;
    let builtin = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../builtin/src/lib.rs");
    let code = code.replace("BUILTIN_PATH", builtin.to_str().unwrap());
    check_cli(
        &code,
        &["--is-core"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for air/src/context.rs:368 atom 2 `matches!(self.solver, SmtSolver::Z3)`
#[test]
fn cvc5_rlimit_noquery() {
    let code = r#"use vstd::prelude::*;
verus! {
pub open spec fn f() -> int { 1 }
}
"#;
    check_cli(
        code,
        &["--crate-type=lib", "-V", "cvc5", "--smt-option", "rlimit=5"],
        true,
        Some("verification results:: 0 verified, 0 errors"),
        &[],
    );
}

// Independence pair for air/src/smt_verify.rs:257 atom 0 `line == "unknown"`
#[test]
fn dump_models_ignore() {
    let code = r#"use vstd::prelude::*;
verus! {
pub proof fn f(x: u8) {
    assert(x == 1u8) by (bit_vector);
}
}
"#;
    check_cli(
        code,
        &["--crate-type=lib", "--smt-option", "dump_models=true", "-V", "ignore-unexpected-smt"],
        false,
        Some("verification results:: 1 verified, 1 errors"),
        &["error: bitvector assertion not satisfied"],
    );
}

// Independence pair for rust_verify/src/expand_errors_driver.rs:566 atom 0 `in_fancy_note`, atom 1 `in_msg`
#[test]
fn expand_errors_format_short() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn p(x: int) -> bool { x > 0 && x < 10 }
proof fn f(x: int) requires x > 0 {
    assert(p(x));
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--expand-errors", "--error-format=short"],
        false,
        Some("verification results:: 1 verified, 1 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:1786 atom 1 `!self.args.no_auto_recommends_check`; rust_verify/src/verifier.rs:1818 atom 1 `!self.args.no_auto_recommends_check`
#[test]
fn fail_no_auto_recommends() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn g(x: int) -> bool recommends x > 0 { x > 1 }
fn e(x: u8) {
    assert(g(x as int));
}
spec fn h(x: int) -> int decreases x { if x == 0 { 0 } else { h(x - 1) } }
fn main() {}
}
"#;
    check_cli(
        code,
        &["--no-auto-recommends-check"],
        false,
        Some("verification results:: 1 verified, 2 errors"),
        &["error: assertion failed", "error: could not prove termination"],
    );
}

// Independence pair for rust_verify/src/verifier.rs:2517 atom 0 `self.args.log_all`
#[test]
fn log_all_single_thread() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn sq(x: nat) -> nat { x * x }
proof fn p() { assert(sq(7) == 49) by (compute_only); }
fn f(x: u8) ensures x <= 255 {}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--num-threads", "1", "--log-all", "--log-dir", "LOG_DIR"],
        true,
        Some("verification results:: 3 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:1180 atom 1; rust_verify/src/verifier.rs:1194 atom 1; rust_verify/src/verifier.rs:1208 atom 1; rust_verify/src/verifier.rs:1963 atom 1; rust_verify/src/verifier.rs:1975 atom 1; rust_verify/src/verifier.rs:2026 atom 1; rust_verify/src/verifier.rs:2057 atom 1; rust_verify/src/verifier.rs:2123 atom 1; rust_verify/src/verifier.rs:2547 atom 1; rust_verify/src/verifier.rs:2781 atom 1; rust_verify/src/verifier.rs:3229 atom 1
#[test]
fn log_each() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn f(x: int) -> int { x + 1 }
proof fn p(x: int) ensures f(x) > x { assert(f(x) > x); assert(1 + 1 == 2) by (compute); }
fn main() {}
}
"#;
    check_cli(
        code,
        &[
            "--log",
            "vir",
            "--log",
            "vir-simple",
            "--log",
            "vir-poly",
            "--log",
            "vir-sst",
            "--log",
            "trait-conflits",
            "--log",
            "interpreter",
            "--log",
            "air",
            "--log",
            "air-final",
            "--log",
            "smt",
            "--log",
            "smt-transcript",
            "--log",
            "triggers",
            "--log",
            "impl-names",
            "--log",
            "call-graph",
            "--log-dir",
            "LOG_DIR",
        ],
        true,
        Some("verification results:: 2 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:2517 atom 1 `self.args.log_args.log_interpreter`
#[test]
fn log_interp_single_thread() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn sq(x: nat) -> nat { x * x }
proof fn p() { assert(sq(7) == 49) by (compute_only); }
fn f(x: u8) ensures x <= 255 {}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--num-threads", "1", "--log", "interpreter", "--log-dir", "LOG_DIR"],
        true,
        Some("verification results:: 3 verified, 0 errors"),
        &[],
    );
}

// Independence pair for air/src/context.rs:337 atom 1 `value`; air/src/context.rs:355 atom 1 `value`
#[test]
fn opt_false_noquery() {
    let code = r#"use vstd::prelude::*;
verus! {
pub open spec fn f() -> int { 1 }
}
"#;
    check_cli(
        code,
        &[
            "--crate-type=lib",
            "--smt-option",
            "air_recommended_options=false",
            "--smt-option",
            "single_check_query=false",
        ],
        true,
        Some("verification results:: 0 verified, 0 errors"),
        &[],
    );
}

// Independence pair for air/src/context.rs:355 atom 0 `option == "single_check_query"`, atom 1 `value`
#[test]
fn opt_scq_true() {
    let code = r#"use vstd::prelude::*;
verus! {
proof fn t(x: int) ensures x + 1 > x {}
}
"#;
    check_cli(
        code,
        &["--crate-type=lib", "--smt-option", "single_check_query=true"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:2618 atom 1 `self.args.build_sst`
#[test]
fn opts_no_verify_build_sst() {
    let code = r#"use vstd::prelude::*;
verus! {
fn good(x: u8) -> (r: u8) requires x < 10 ensures r == x + 1 { x + 1 }
fn bad(x: u8) { assert(x == 0); }
fn main() {}
}
"#;
    check_cli(code, &["--no-verify", "--build-sst"], true, None, &[]);
}

// Independence pair for rust_verify/src/verifier.rs:2539 atom 0 `self.args.profile`, atom 1 `self.count_errors == 0`
#[test]
fn opts_profile_no_errors() {
    let code = r#"use vstd::prelude::*;
verus! {
fn good(x: u8) -> (r: u8) requires x < 10 ensures r == x + 1 { x + 1 }
fn bad(x: u8) { assert(x == 0); }
fn main() {}
}
"#;
    check_cli(
        code,
        &["--profile", "--verify-function", "good", "--verify-root"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:1921 atom 0 `self.args.trace`
#[test]
fn opts_verify_function_trace() {
    let code = r#"use vstd::prelude::*;
verus! {
fn good(x: u8) -> (r: u8) requires x < 10 ensures r == x + 1 { x + 1 }
fn bad(x: u8) { assert(x == 0); }
fn main() {}
}
"#;
    check_cli(
        code,
        &["--verify-function", "good", "--trace", "--verify-root"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for vir/src/printer.rs:258 atom 0 `opts.no_span`, atom 1 `opts.no_type`
#[test]
fn printer_vir_log_compact() {
    let code = r#"use vstd::prelude::*;
verus! {
fn f(x: u8) -> (r: u8) requires x < 255 ensures r > x { x + 1 }
} // verus!
fn main() {}
"#;
    check_cli(
        code,
        &["--log", "vir", "--log", "vir-option=compact", "--log-dir", "LOG_DIR"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for vir/src/printer.rs:258 atom 1 `opts.no_type`
#[test]
fn printer_vir_log_no_span() {
    let code = r#"use vstd::prelude::*;
verus! {
fn f(x: u8) -> (r: u8) requires x < 255 ensures r > x { x + 1 }
} // verus!
fn main() {}
"#;
    check_cli(
        code,
        &["--log", "vir", "--log", "vir-option=no_span", "--log-dir", "LOG_DIR"],
        true,
        Some("verification results:: 1 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:1537 atom 1 `self.args.profile_all`; rust_verify/src/verifier.rs:1702 atom 0 `command_not_skipped`
#[test]
fn profile_all_filtered_spinoff() {
    let code = r#"use vstd::prelude::*;
verus! {
mod m {
    use vstd::prelude::*;
    pub proof fn f(x: int, y: int) {
        assert(x * y == y * x) by (nonlinear_arith);
    }
    pub proof fn g(x: int, y: int) {
        assert(x * y == x * x) by (nonlinear_arith); // false
    }
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--profile-all", "--verify-only-module", "m", "--verify-function", "f"],
        true,
        Some("verification results:: 2 verified, 0 errors"),
        &[],
    );
}

// Independence pair for rust_verify/src/verifier.rs:860 atom 1; rust_verify/src/verifier.rs:869 atom 0; rust_verify/src/verifier.rs:882 atom 1; rust_verify/src/verifier.rs:1531 atom 2; rust_verify/src/verifier.rs:1537 atom 0; rust_verify/src/verifier.rs:1754 atoms 0, 1; rust_verify/src/verifier.rs:2539 atom 1
#[test]
fn profile_rerun_bitvector_fail() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn f(x: int) -> int;
#[verifier::rlimit(0.001)]
proof fn p(a: int, b: int, c: int, u: u8)
    requires forall|x: int| #[trigger] f(x) == f(x + 1) + 1,
{
    assert(u & 1u8 == 0u8) by (bit_vector);
    assert(f(a) == f(a + 30) + 30 && f(b) == f(b + 20) + 20);
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--profile"],
        false,
        Some("verification results:: 1 verified, 2 errors"),
        &[
            "error: bitvector assertion not satisfied",
            "error: function body check: Resource limit (rlimit) exceeded",
        ],
    );
}

// Independence pair for rust_verify/src/verifier.rs:869 atom 2 `!self.args.capture_profiles`
#[test]
fn rlimit_timeout_capture_profiles() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn f(x: int) -> int;
#[verifier::rlimit(0.0001)]
proof fn p(a: int, b: int, c: int)
    requires forall|x: int| #[trigger] f(x) == f(x + 1) + 1,
    ensures f(a) == f(a + 3) + 3, f(b) == f(b + 2) + 2, f(c) != f(c + 1)
{
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["-V", "capture-profiles"],
        false,
        Some("verification results:: 1 verified, 1 errors"),
        &["error: function body check: Resource limit (rlimit) exceeded"],
    );
}

// Independence pair for rust_verify/src/driver.rs:36 atom 2 `!verifier.args.verify_root`; rust_verify/src/user_filter.rs:76 atom 2 `!args.verify_root`; rust_verify/src/verifier.rs:869 atom 1 `!self.args.profile_all`
#[test]
fn rlimit_timeout_profile_all() {
    let code = r#"use vstd::prelude::*;
verus! {
spec fn f(x: int) -> int;
#[verifier::rlimit(0.0001)]
proof fn p(a: int, b: int, c: int)
    requires forall|x: int| #[trigger] f(x) == f(x + 1) + 1,
    ensures f(a) == f(a + 3) + 3, f(b) == f(b + 2) + 2, f(c) != f(c + 1)
{
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--profile-all", "--verify-root"],
        false,
        Some("verification results:: 1 verified, 1 errors"),
        &["error: function body check: Resource limit (rlimit) exceeded"],
    );
}
// Independence pair for rust_verify/src/config.rs:630 atom 0 `is_vstd`, atom 1 `is_core`
#[test]
fn contradictory_is_vstd_is_core() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry = tempdir.path().join("test.rs");
    std::fs::write(&entry, "fn main() {}\n").expect("write source file");
    let output =
        run_verus_raw(&["--is-vstd", "--is-core", entry.to_str().unwrap()], tempdir.path());
    assert!(!output.status.success());
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(all.contains("contradictory options --is-core and --is-vstd"), "{}", all);
}

/// Runs the verifier binary on a trivial file named `file_name` with `args` and checks that it fails
/// with `message` (an option error is printed before any verification).
fn check_cli_option_error(args: &[&str], message: &str) {
    let tempdir = TempDir::new().expect("temp dir");
    let entry = tempdir.path().join("test.rs");
    std::fs::write(&entry, "fn main() {}\n").expect("write source file");
    let mut a: Vec<&str> = args.to_vec();
    a.push(entry.to_str().unwrap());
    let output = run_verus_raw(&a, tempdir.path());
    assert!(!output.status.success());
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(all.contains(message), "{}", all);
}

// Independence pair for rust_verify/src/config.rs:844 atom 0 `args.compile`, atom 1 `args.no_erasure_check`
#[test]
fn compile_with_no_erasure_check() {
    check_cli_option_error(
        &["--compile", "--no-erasure-check"],
        "--compile and --no-erasure-check are mutually exclusive",
    );
}

// Independence pair for rust_verify/src/config.rs:676 atoms 0, 1 (--profile-all without a module or root)
#[test]
fn profile_all_without_module() {
    check_cli_option_error(
        &["--profile-all"],
        "Must pass --verify-only-module or --verify-root when using profile-all",
    );
}

// Independence pair for rust_verify/src/config.rs:798 atoms 0, 1 (--verify-function without a module or root)
#[test]
fn verify_function_without_module() {
    check_cli_option_error(
        &["--verify-function", "f"],
        "--verify-function option requires --verify-only-module or --verify-root",
    );
}

// Independence pair for vir/src/def.rs:322 atom 1 `krate.bytes().next().unwrap().is_ascii...` (crate name starting with a digit)
#[test]
fn crate_name_starting_with_digit() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry = tempdir.path().join("1test.rs");
    let code =
        "use vstd::prelude::*;\nverus! {\nproof fn p() { assert(1 + 1 == 2); }\nfn main() {}\n}\n";
    std::fs::write(&entry, code).expect("write source file");
    let output = run_verus_raw(&["--crate-name", "1test", entry.to_str().unwrap()], tempdir.path());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "stdout:\n{}\nstderr:\n{}", stdout, stderr);
    assert!(stdout.contains("verification results:: 2 verified, 0 errors"), "{}", stdout);
}

// Independence pair for rust_verify/src/user_filter.rs:276 atom 1, :278 atom 0, :280 atom 0 (a pattern with a wildcard on both sides)
#[test]
fn verify_function_both_wildcards() {
    let code = r#"use vstd::prelude::*;
verus! {
mod m {
    use vstd::prelude::*;
    pub fn pre_ok_suf(x: u8) ensures x <= 255 {}
    pub fn pre_ok(x: u8) ensures x <= 255 {}
    pub fn ok_suf(x: u8) ensures x <= 255 {}
    pub fn bad_one(x: u8) ensures x < 255 {}
}
fn main() {}
}
"#;
    check_cli(
        code,
        &["--verify-only-module", "m", "--verify-function", "*ok*"],
        true,
        Some("verification results:: 3 verified, 0 errors"),
        &[],
    );
}
