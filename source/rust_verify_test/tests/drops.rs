#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests for the placement of `Drop` nodes, which rust_to_vir emits according to rustc's
// rules for scopes (see rust_verify/src/drop_scopes.rs).
//
// We check the placement of the drops by examining the control flow graphs built by
// resolution_inference (`--log resolution-cfg`), in which the drops appear as `ScopeDrop`
// instructions. Each expected CFG was compared to the MIR built by rustc
// (`-Zdump-mir=<fn>`, the `built` phase, before drop elaboration) for the same code,
// with `D` implementing `Drop`. Note the following differences, which are expected:
//  - VIR uses temporaries in some places where MIR doesn't (e.g., for `let` initializers),
//    and MIR uses temporaries in some places where VIR doesn't (e.g., for reborrows).
//  - Like MIR, we only drop values whose types need dropping, so `D` implements `Drop`
//    (whereas integers, references, and `Option<u64>` don't need dropping).
//  - MIR drops the temporaries of an `if` condition after branching (in both branches),
//    whereas we drop them before branching.
//  - MIR's drops of moved-from values are later removed by drop elaboration;
//    we leave them in (they should be treated as no-ops when the value has been moved out).

const DEFS: &str = verus_code_str! {
    struct D { x: u64 }
    impl Drop for D {
        fn drop(&mut self)
            opens_invariants none
            no_unwind
        {
        }
    }
    fn mk() -> D no_unwind { D { x: 0 } }
    fn use_ref(d: &D) -> u64 no_unwind { d.x }
    fn opt(d: &D) -> Option<u64> no_unwind { None }
    fn cond() -> bool no_unwind { true }
};

/// Run Verus on the code and check that the CFG for the function `fn_name`
/// (as logged by resolution_inference) is the expected one.
fn check_cfg(code: String, fn_name: &str, options: &[&str], expected: &str) {
    let test_dir = tempfile::tempdir().expect("temporary test directory");
    let entry_file = test_dir.path().join("test.rs");
    let log_dir = test_dir.path().join("log");
    std::fs::write(&entry_file, format!("{}{}{}{}", FEATURE_PRELUDE, USE_PRELUDE, DEFS, code))
        .expect("test source");

    let log_dir_option = format!("--log-dir={}", log_dir.display());
    let mut options = options.to_vec();
    options.extend(["--no-verify", "--log-resolution-cfg", &log_dir_option]);
    let output = run_verus(&options, test_dir.path(), &entry_file, true, false);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));

    let log = std::fs::read_to_string(log_dir.join("crate-resolution-cfg.txt"))
        .expect("read resolution-cfg log");
    let header = format!("fn test_crate::{}\n", fn_name);
    let start = log.find(&header).expect("function not found in log") + header.len();
    let end = log[start..].find("\nfn ").map(|i| start + i).unwrap_or(log.len());
    let actual = log[start..end].trim();
    let expected = expected.trim();
    if actual != expected {
        panic!("CFG mismatch\n--- expected:\n{}\n--- actual:\n{}\n", expected, actual);
    }
}

/// Locals are dropped in reverse order of declaration at the end of their block,
/// and parameters are dropped after all the locals of the body.
#[test]
fn test_locals_reverse_order() {
    let code = verus_code! {
        fn test(a: D, b: D) {
            let x = mk();
            let y = mk();
            {
                let z = mk();
            }
            let w = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(a)
    Overwrite(b)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(y)
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(z)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(z)
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(w)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(w)
    ScopeDrop(y)
    ScopeDrop(x)
    ScopeDrop(b)
    ScopeDrop(a)
"#,
    );
}

/// Temporaries in a statement are dropped at the end of the statement,
/// in reverse order of creation (so the statement's result is dropped first).
#[test]
fn test_statement_temporaries() {
    let code = verus_code! {
        fn test() {
            use_ref(&mk());
            mk();
            let n = use_ref(&mk()) + use_ref(&mk());
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // use_ref(&&mk())
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_3)        // mk()
    ScopeDrop(Temp_3)        // mk()
    Overwrite(Temp_4)        // mk()
    Overwrite(Temp_5)        // &mk()
    Overwrite(Temp_6)        // mk()
    Overwrite(Temp_7)        // &mk()
    Overwrite(Temp_8)        // use_ref(&&mk()) + use_ref(&&mk())
    Overwrite(n)
    ScopeDrop(Temp_6)        // mk()
    ScopeDrop(Temp_4)        // mk()
"#,
    );
}

/// Temporaries in nested call arguments are all dropped at the end of the statement.
#[test]
fn test_nested_call_args() {
    let code = verus_code! {
        fn two(a: u64, b: u64) -> u64 no_unwind { 0 }
        fn test() {
            let n = two(use_ref(&mk()), use_ref(&mk()));
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // mk()
    Overwrite(Temp_3)        // &mk()
    Overwrite(Temp_4)        // two(use_ref(&&mk()), use_ref(&&mk()))
    Overwrite(n)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(k)
"#,
    );
}

/// `let _ = e;` drops the value of `e` at the end of the statement,
/// but `let _ = x;` doesn't move or drop `x`.
#[test]
fn test_let_wildcard() {
    let code = verus_code! {
        fn test() {
            let _ = mk();
            let x = mk();
            let _ = x;
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(x)
"#,
    );
}

/// In edition 2021, temporaries in the tail expression of the function body
/// are dropped after the locals of the body.
#[test]
fn test_fn_tail_expr_2021() {
    let code = verus_code! {
        fn test() -> u64 {
            let a = mk();
            use_ref(&mk())
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2021"],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    ScopeDrop(a)
    ScopeDrop(Temp_1)        // mk()
"#,
    );
}

/// In edition 2024, temporaries in the tail expression of the function body
/// are dropped before the locals of the body.
#[test]
fn test_fn_tail_expr_2024() {
    let code = verus_code! {
        fn test() -> u64 {
            let a = mk();
            use_ref(&mk())
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2024"],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(a)
"#,
    );
}

/// In edition 2021, temporaries in a block's tail expression live until the end
/// of the enclosing statement.
#[test]
fn test_block_tail_expr_2021() {
    let code = verus_code! {
        fn test() {
            let n = { let a = mk(); use_ref(&mk()) };
            let m = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2021"],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    ScopeDrop(a)
    Overwrite(Temp_3)        // {...}
    Overwrite(n)
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(m)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(m)
"#,
    );
}

/// In edition 2024, temporaries in a block's tail expression are dropped at the end of the block.
#[test]
fn test_block_tail_expr_2024() {
    let code = verus_code! {
        fn test() {
            let n = { let a = mk(); use_ref(&mk()) };
            let m = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2024"],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(a)
    Overwrite(Temp_3)        // {...}
    Overwrite(n)
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(m)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(m)
"#,
    );
}

/// Temporary lifetime extension: `let r = &temp;` extends the temporary to the end of the block.
/// The extended temporary is dropped after the variable.
#[test]
fn test_extend_borrow() {
    let code = verus_code! {
        fn test() {
            let r = &mk();
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(r)
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// Temporary lifetime extension through tuple expressions (but not through function arguments).
#[test]
fn test_extend_tuple() {
    let code = verus_code! {
        fn test() {
            let t = (&mk(), use_ref(&mk()), &mk());
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    Overwrite(Temp_3)        // mk()
    Overwrite(Temp_4)        // (&mk(), use_ref(&&mk()), &mk())
    Overwrite(t)
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// Temporary lifetime extension through a block's tail expression.
#[test]
fn test_extend_block_tail() {
    let code = verus_code! {
        fn test() {
            let r = { let a = mk(); &mk() };
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    ScopeDrop(a)
    Overwrite(Temp_2)        // {...}
    Overwrite(r)
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_1)        // mk()
"#,
    );
}

/// Temporary lifetime extension through both branches of an if-else.
#[test]
fn test_extend_if_else() {
    let code = verus_code! {
        fn test(c: bool) {
            let r = if c { &mk() } else { &mk() };
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(c)
    -> bb1, bb2
bb1:
    Overwrite(Temp_0)        // mk()
    -> bb3
bb2:
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // { &mk() }
    -> bb3
bb3 (exit):
    Overwrite(Temp_3)        // if c {...}
    Overwrite(r)
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// Temporary lifetime extension of the base of a field expression: `let r = &temp.f;`
#[test]
fn test_extend_field() {
    let code = verus_code! {
        fn test() {
            let r = &mk().x;
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk().x
    Overwrite(r)
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// Temporary lifetime extension through the arguments of a tuple-struct constructor.
#[test]
fn test_extend_tuple_struct_ctor() {
    let code = verus_code! {
        fn test() {
            let r = Some(&mk());
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // Some(&mk())
    Overwrite(r)
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// Temporary lifetime extension through match arms.
#[test]
fn test_extend_match_arms() {
    let code = verus_code! {
        fn test(c: bool) {
            let r = match c { true => &mk(), false => &mk() };
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(c)
    -> bb1, bb2
bb1:
    Overwrite(Temp_0)        // mk()
    -> bb3
bb2:
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    -> bb3
bb3 (exit):
    Overwrite(Temp_3)        // match c {...}
    Overwrite(r)
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// The condition of an `if` is a terminating scope, so its temporaries are dropped
/// before entering either branch.
#[test]
fn test_if_condition() {
    let code = verus_code! {
        fn test() {
            if use_ref(&mk()) == 0 {
                let a = mk();
            } else {
                let b = mk();
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    ScopeDrop(Temp_0)        // mk()
    -> bb1, bb2
bb1:
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(a)
    -> bb3
bb2:
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(b)
    -> bb3
bb3 (exit):
"#,
    );
}

/// In edition 2021, temporaries in the scrutinee of an `if let` live until the end of
/// the enclosing statement. The bindings are dropped at the end of the then-branch.
#[test]
fn test_if_let_2021() {
    let code = verus_code! {
        fn test() {
            let k = mk();
            if let Some(v) = opt(&mk()) {
                let a = mk();
            } else {
                let b = mk();
            }
            let j = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2021"],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    Overwrite(Temp_3)        // opt(&&mk())
    -> bb1, bb2
bb1:
    Overwrite(v)
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(a)
    -> bb3
bb2:
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(b)
    -> bb3
bb3 (exit):
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_6)        // mk()
    MoveFrom(Temp_6)         // mk()
    Overwrite(j)
    ScopeDrop(Temp_6)        // mk()
    ScopeDrop(j)
    ScopeDrop(k)
"#,
    );
}

/// In edition 2024, temporaries in the scrutinee of an `if let` are dropped at the end
/// of the then-branch, or before the else-branch.
#[test]
fn test_if_let_2024() {
    let code = verus_code! {
        fn test() {
            let k = mk();
            if let Some(v) = opt(&mk()) {
                let a = mk();
            } else {
                let b = mk();
            }
            let j = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2024"],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    Overwrite(Temp_3)        // opt(&&mk())
    -> bb1, bb2
bb1:
    Overwrite(v)
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(a)
    ScopeDrop(Temp_1)        // mk()
    -> bb3
bb2:
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(b)
    -> bb3
bb3 (exit):
    Overwrite(Temp_6)        // mk()
    MoveFrom(Temp_6)         // mk()
    Overwrite(j)
    ScopeDrop(Temp_6)        // mk()
    ScopeDrop(j)
    ScopeDrop(k)
"#,
    );
}

/// In edition 2021, for an `else if let` chain, the scrutinee temporaries of the inner `if let`
/// are dropped before those of the outer one (at the end of the enclosing statement).
#[test]
fn test_else_if_let_2021() {
    let code = verus_code! {
        fn test() {
            if let Some(v) = opt(&mk()) {
                let a = mk();
            } else if let Some(w) = opt(&mk()) {
                let b = mk();
            }
            let j = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2021"],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // opt(&&mk())
    -> bb1, bb2
bb1:
    Overwrite(v)
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(a)
    -> bb6
bb2:
    Overwrite(Temp_4)        // mk()
    Overwrite(Temp_5)        // &mk()
    Overwrite(Temp_6)        // opt(&&mk())
    -> bb3, bb4
bb3:
    Overwrite(w)
    Overwrite(Temp_7)        // mk()
    MoveFrom(Temp_7)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_7)        // mk()
    ScopeDrop(b)
    -> bb5
bb4:
    -> bb5
bb5:
    ScopeDrop(Temp_4)        // mk()
    -> bb6
bb6 (exit):
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_8)        // mk()
    MoveFrom(Temp_8)         // mk()
    Overwrite(j)
    ScopeDrop(Temp_8)        // mk()
    ScopeDrop(j)
"#,
    );
}

/// In edition 2024, the scrutinee temporaries of each `if let` are dropped
/// before the corresponding else-branch.
#[test]
fn test_else_if_let_2024() {
    let code = verus_code! {
        fn test() {
            if let Some(v) = opt(&mk()) {
                let a = mk();
            } else if let Some(w) = opt(&mk()) {
                let b = mk();
            }
            let j = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2024"],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // opt(&&mk())
    -> bb1, bb2
bb1:
    Overwrite(v)
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(a)
    ScopeDrop(Temp_0)        // mk()
    -> bb6
bb2:
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_4)        // mk()
    Overwrite(Temp_5)        // &mk()
    Overwrite(Temp_6)        // opt(&&mk())
    -> bb3, bb4
bb3:
    Overwrite(w)
    Overwrite(Temp_7)        // mk()
    MoveFrom(Temp_7)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_7)        // mk()
    ScopeDrop(b)
    ScopeDrop(Temp_4)        // mk()
    -> bb5
bb4:
    ScopeDrop(Temp_4)        // mk()
    -> bb5
bb5:
    -> bb6
bb6 (exit):
    Overwrite(Temp_8)        // mk()
    MoveFrom(Temp_8)         // mk()
    Overwrite(j)
    ScopeDrop(Temp_8)        // mk()
    ScopeDrop(j)
"#,
    );
}

/// The operands of `&&` and `||` are terminating scopes.
#[test]
fn test_and_or() {
    let code = verus_code! {
        fn test() {
            if use_ref(&mk()) == 0 && use_ref(&mk()) == 1 {
                let a = mk();
            }
            let b = use_ref(&mk()) == 0 || use_ref(&mk()) == 1;
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    ScopeDrop(Temp_0)        // mk()
    -> bb1, bb2
bb1:
    Overwrite(Temp_2)        // mk()
    Overwrite(Temp_3)        // &mk()
    ScopeDrop(Temp_2)        // mk()
    -> bb2
bb2:
    -> bb3, bb4
bb3:
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(a)
    -> bb5
bb4:
    -> bb5
bb5:
    Overwrite(Temp_5)        // mk()
    Overwrite(Temp_6)        // &mk()
    ScopeDrop(Temp_5)        // mk()
    -> bb6, bb7
bb6:
    Overwrite(Temp_7)        // mk()
    Overwrite(Temp_8)        // &mk()
    ScopeDrop(Temp_7)        // mk()
    -> bb7
bb7 (exit):
    Overwrite(Temp_9)        // Left(... == 0, drop) || Left(... == 1, drop)
    Overwrite(b)
"#,
    );
}

/// The temporaries of a match scrutinee live until the end of the enclosing statement;
/// the bindings of a match arm are dropped at the end of the arm.
#[test]
fn test_match_arms() {
    let code = verus_code! {
        fn test() {
            match opt(&mk()) {
                Some(v) => { let a = mk(); }
                None => { let b = mk(); }
            }
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // opt(&&mk())
    -> bb1, bb2
bb1:
    Overwrite(v)
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(a)
    -> bb3
bb2:
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(b)
    -> bb3
bb3 (exit):
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(k)
"#,
    );
}

/// Matching a place by value moves out of it into the binding.
#[test]
fn test_match_move_binding() {
    let code = verus_code! {
        fn test(o: Option<D>) {
            match o {
                Some(d) => { let a = mk(); }
                None => { }
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(o)
    -> bb1, bb2
bb1:
    MoveFrom(o.Some_0)
    Overwrite(d)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    ScopeDrop(a)
    ScopeDrop(d)
    -> bb3
bb2:
    -> bb3
bb3 (exit):
    ScopeDrop(o)
"#,
    );
}

/// Matching an rvalue: the scrutinee is stored in a temporary.
#[test]
fn test_match_rvalue_scrutinee() {
    let code = verus_code! {
        fn test() {
            match mk() {
                d => { let a = mk(); }
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    -> bb1
bb1:
    MoveFrom(Temp_0)         // mk()
    Overwrite(d)
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(a)
    ScopeDrop(d)
    -> bb2
bb2 (exit):
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// A match guard is a terminating scope.
#[test]
fn test_match_guard() {
    let code = verus_code! {
        fn test(n: u64) {
            match n {
                0 => {}
                m if use_ref(&mk()) == m => { let a = mk(); }
                _ => {}
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(n)
    -> bb1, bb2, bb5
bb1:
    -> bb7
bb2:
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    ScopeDrop(Temp_0)        // mk()
    -> bb3, bb4
bb3:
    -> bb5
bb4:
    Overwrite(m)
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(a)
    -> bb7
bb5:
    -> bb6
bb6:
    -> bb7
bb7 (exit):
"#,
    );
}

/// Temporaries in a match arm's body (when it's not a block) are dropped at the end of the arm.
#[test]
fn test_match_arm_body_temps() {
    let code = verus_code! {
        fn test(n: u64) -> u64 {
            match n {
                0 => use_ref(&mk()),
                _ => 1,
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(n)
    -> bb1, bb2
bb1:
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    ScopeDrop(Temp_0)        // mk()
    -> bb3
bb2:
    -> bb3
bb3 (exit):
"#,
    );
}

/// `break` and `continue` drop everything in the scopes being exited;
/// the `break` value is evaluated first.
#[test]
fn test_loop_break_continue() {
    let code = verus_code! {
        fn test() {
            let k = mk();
            let v = loop {
                let a = mk();
                if cond() { break use_ref(&mk()); }
                let b = mk();
                if cond() { continue; }
                let c = mk();
            };
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_0)        // mk()
    -> bb1
bb1:
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_1)        // mk()
    -> bb3, bb4
bb2 (exit):
    Overwrite(Temp_6)        // loop {...}
    Overwrite(v)
    ScopeDrop(k)
bb3:
    Overwrite(Temp_2)        // mk()
    Overwrite(Temp_3)        // &mk()
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(a)
    -> bb2
bb4:
    -> bb5
bb5:
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_4)        // mk()
    -> bb6, bb7
bb6:
    ScopeDrop(b)
    ScopeDrop(a)
    -> bb1
bb7:
    -> bb8
bb8:
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(c)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(c)
    ScopeDrop(b)
    ScopeDrop(a)
    -> bb1
"#,
    );
}

/// `break` and `continue` to an outer loop drop everything in both loops' bodies.
#[test]
fn test_labeled_break_continue() {
    let code = verus_code! {
        fn test() {
            'outer: loop {
                let a = mk();
                loop {
                    let b = mk();
                    if cond() { break 'outer; }
                    if cond() { continue 'outer; }
                    break;
                }
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    -> bb1
bb1:
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    -> bb3
bb2 (exit):
bb3:
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_1)        // mk()
    -> bb5, bb6
bb4:
    ScopeDrop(a)
    -> bb1
bb5:
    ScopeDrop(b)
    ScopeDrop(a)
    -> bb2
bb6:
    -> bb7
bb7:
    -> bb8, bb9
bb8:
    ScopeDrop(b)
    ScopeDrop(a)
    -> bb1
bb9:
    -> bb10
bb10:
    ScopeDrop(b)
    -> bb4
"#,
    );
}

/// The condition of a `while` loop is a terminating scope.
#[test]
fn test_while_cond() {
    let code = verus_code! {
        fn test() {
            let k = mk();
            while use_ref(&mk()) == 0 {
                let a = mk();
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_0)        // mk()
    -> bb1
bb1:
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    ScopeDrop(Temp_1)        // mk()
    -> bb3, bb4
bb2 (exit):
    ScopeDrop(k)
bb3:
    -> bb2
bb4:
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(a)
    -> bb1
"#,
    );
}

/// In edition 2021, the scrutinee temporaries of a `while let` are dropped at the end
/// of each iteration (and when exiting the loop).
#[test]
fn test_while_let_2021() {
    let code = verus_code! {
        fn test() {
            while let Some(v) = opt(&mk()) {
                let a = mk();
            }
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2021"],
        r#"
bb0 (entry):
    -> bb1
bb1:
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // opt(&&mk())
    -> bb3, bb4
bb2 (exit):
bb3:
    Overwrite(v)
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(a)
    -> bb5
bb4:
    ScopeDrop(Temp_0)        // mk()
    -> bb2
bb5:
    ScopeDrop(Temp_0)        // mk()
    -> bb1
"#,
    );
}

/// In edition 2024, the scrutinee temporaries of a `while let` are dropped at the end
/// of the body, or before exiting the loop.
#[test]
fn test_while_let_2024() {
    let code = verus_code! {
        fn test() {
            while let Some(v) = opt(&mk()) {
                let a = mk();
            }
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2024"],
        r#"
bb0 (entry):
    -> bb1
bb1:
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // opt(&&mk())
    -> bb3, bb4
bb2 (exit):
bb3:
    Overwrite(v)
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(a)
    ScopeDrop(Temp_0)        // mk()
    -> bb5
bb4:
    ScopeDrop(Temp_0)        // mk()
    -> bb2
bb5:
    -> bb1
"#,
    );
}

/// `return` drops everything in scope, including the parameters, after evaluating
/// the return value.
#[test]
fn test_return_early() {
    let code = verus_code! {
        fn test(p: D) -> u64 {
            let a = mk();
            if cond() {
                let b = mk();
                return use_ref(&mk());
            }
            let c = mk();
            0
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(p)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    -> bb1, bb2
bb1 (exit):
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_2)        // mk()
    Overwrite(Temp_3)        // &mk()
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(b)
    ScopeDrop(a)
    ScopeDrop(p)
bb2:
    -> bb3
bb3 (exit):
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(c)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(c)
    ScopeDrop(a)
    ScopeDrop(p)
"#,
    );
}

/// `return` from inside a loop.
#[test]
fn test_return_in_loop() {
    let code = verus_code! {
        fn test(p: D) {
            let a = mk();
            loop {
                let b = mk();
                if cond() {
                    return;
                }
            }
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(p)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    -> bb1
bb1:
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_1)        // mk()
    -> bb3, bb4
bb2:
bb3 (exit):
    ScopeDrop(b)
    ScopeDrop(a)
    ScopeDrop(p)
bb4:
    -> bb5
bb5:
    ScopeDrop(b)
    -> bb1
"#,
    );
}

/// If the pattern of a let-else fails to match, the temporaries in the initializer are dropped
/// before running the else-block.
#[test]
fn test_let_else() {
    let code = verus_code! {
        fn test() {
            let k = mk();
            let Some(v) = opt(&mk()) else {
                let e = mk();
                return;
            };
            let j = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    Overwrite(Temp_3)        // opt(&&mk())
    -> bb1, bb2
bb1 (exit):
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(e)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(e)
    ScopeDrop(k)
bb2 (exit):
    Overwrite(v)
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(j)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(j)
    ScopeDrop(k)
"#,
    );
}

/// If the pattern of a let-else fails to match, the extended temporaries in the initializer
/// are also dropped before running the else-block.
#[test]
fn test_let_else_extended() {
    let code = verus_code! {
        fn test() {
            let Some(r) = Some(&mk()) else {
                return;
            };
            let j = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // Some(&mk())
    -> bb1, bb2
bb1 (exit):
    ScopeDrop(Temp_0)        // mk()
bb2 (exit):
    Overwrite(r)
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(j)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(j)
    ScopeDrop(Temp_0)        // mk()
"#,
    );
}

/// Bindings in a pattern are dropped in reverse order; parts of the initializer that aren't
/// moved into bindings are dropped at the end of the statement. Shadowing doesn't drop anything.
#[test]
fn test_patterns_and_shadowing() {
    let code = verus_code! {
        fn test() {
            let (a, b) = (mk(), mk());
            let (c, _) = (mk(), mk());
            let x = mk();
            let x = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // (mk(), mk())
    MoveFrom(Temp_0.0)       // (mk(), mk())
    MoveFrom(Temp_0.1)       // (mk(), mk())
    Overwrite(a)
    Overwrite(b)
    ScopeDrop(Temp_0)        // (mk(), mk())
    Overwrite(Temp_1)        // (mk(), mk())
    MoveFrom(Temp_1.0)       // (mk(), mk())
    Overwrite(c)
    ScopeDrop(Temp_1)        // (mk(), mk())
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_2)        // mk()
    Overwrite(Temp_3)        // mk()
    MoveFrom(Temp_3)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(x)
    ScopeDrop(x)
    ScopeDrop(c)
    ScopeDrop(b)
    ScopeDrop(a)
"#,
    );
}

/// A variable declared without an initializer is dropped at the end of its scope.
#[test]
fn test_uninit_let() {
    let code = verus_code! {
        fn test() {
            let x: D;
            let y = mk();
            x = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(y)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(x)
    ScopeDrop(y)
    ScopeDrop(x)
"#,
    );
}

/// Temporaries of an assignment are dropped at the end of the statement.
#[test]
fn test_assign() {
    let code = verus_code! {
        fn test() {
            let mut x = mk();
            x = mk();
            let mut t = (mk(), 0u64);
            t.1 = use_ref(&mk());
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(x)
    Overwrite(Temp_1)        // (mk(), 0)
    MoveFrom(Temp_1)         // (mk(), 0)
    Overwrite(t)
    ScopeDrop(Temp_1)        // (mk(), 0)
    Overwrite(Temp_2)        // mk()
    Overwrite(Temp_3)        // &mk()
    Overwrite(t.1)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(t)
    ScopeDrop(x)
"#,
    );
}

/// Method calls with `&self` and `&mut self` create temporaries for the receiver.
#[test]
fn test_method_autoref() {
    let code = verus_code! {
        impl D {
            fn m(&self) -> u64 no_unwind { self.x }
            fn mm(&mut self) no_unwind {}
        }
        fn test() {
            let n = mk().m();
            mk().mm();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // m(&mk())
    Overwrite(n)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_2)        // mk()
    Mutate(Temp_2)           // mk()
    ScopeDrop(Temp_2)        // mk()
"#,
    );
}

/// Closures have their own scopes; closure params are dropped after the closure body.
#[test]
fn test_closure() {
    let code = verus_code! {
        fn test() {
            let k = mk();
            let f = |a: D| { let b = mk(); use_ref(&mk()) };
            let j = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_4)        // { |...| ... }
    Overwrite(f)
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(j)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(j)
    ScopeDrop(k)
bb1 (entry):
    Overwrite(a)
    -> bb2
bb2 (exit):
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_2)        // mk()
    Overwrite(Temp_3)        // &mk()
    ScopeDrop(b)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(a)
"#,
    );
}

/// `return` inside a closure only drops the closure's locals and params.
#[test]
fn test_closure_return() {
    let code = verus_code! {
        fn test(p: D) {
            let f = |a: D| -> u64 { let b = mk(); if cond() { return 0; } 1 };
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(p)
    Overwrite(Temp_1)        // { |...| ... }
    Overwrite(f)
    ScopeDrop(p)
bb1 (entry):
    Overwrite(a)
    -> bb2
bb2:
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_0)        // mk()
    -> bb3, bb4
bb3 (exit):
    ScopeDrop(b)
    ScopeDrop(a)
bb4:
    -> bb5
bb5 (exit):
    ScopeDrop(b)
    ScopeDrop(a)
"#,
    );
}

/// Indexing into an rvalue creates a temporary for the base,
/// which can be lifetime-extended.
#[test]
fn test_vec_index() {
    let code = verus_code! {
        use vstd::prelude::*;
        fn mk_vec() -> (v: Vec<D>)
            ensures v.len() == 1,
            no_unwind
        {
            let mut v = Vec::new();
            v.push(mk());
            v
        }
        fn test() {
            let n = mk_vec()[0].x;
            let r = &mk_vec()[0];
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk_vec()
    Overwrite(Temp_1)        // vec_index(&mk_vec(), 0)
    Overwrite(n)
    ScopeDrop(Temp_0)        // mk_vec()
    Overwrite(Temp_2)        // mk_vec()
    Overwrite(Temp_3)        // vec_index(&mk_vec(), 0)
    Overwrite(Temp_4)        // &vec_index(&mk_vec(), 0)
    Overwrite(r)
    Overwrite(Temp_5)        // mk()
    MoveFrom(Temp_5)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_5)        // mk()
    ScopeDrop(k)
    ScopeDrop(Temp_2)        // mk_vec()
"#,
    );
}

/// No drops are emitted for ghost code.
#[test]
fn test_ghost_code_no_drops() {
    let code = verus_code! {
        proof fn mk_tracked() -> (tracked d: D) {
            D { x: 0 }
        }
        fn test(a: D) {
            proof {
                let tracked t = mk_tracked();
            }
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(a)
    Overwrite(Temp_0)        // mk_tracked()
    MoveFrom(Temp_0)         // mk_tracked()
    Overwrite(t)
    Overwrite(Temp_1)        // mk()
    MoveFrom(Temp_1)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(k)
    ScopeDrop(a)
"#,
    );
}

/// The fields of a struct expression are evaluated before the struct update tail.
#[test]
fn test_struct_update() {
    let code = verus_code! {
        struct S { a: D, b: D }
        fn mk_s() -> S no_unwind { S { a: mk(), b: mk() } }
        fn test() {
            let s = S { a: mk(), ..mk_s() };
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_0)        // mk_s()
    MoveFrom(Temp_0.b)       // mk_s()
    Overwrite(Temp_1)        // S { a: mk(), ..mk_s() }
    MoveFrom(Temp_1)         // S { a: mk(), ..mk_s() }
    Overwrite(s)
    ScopeDrop(Temp_1)        // S { a: mk(), ..mk_s() }
    ScopeDrop(Temp_0)        // mk_s()
    ScopeDrop(s)
"#,
    );
}
