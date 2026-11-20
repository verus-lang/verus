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
// with `D` implementing `Drop`. This means that a `Drop` node indicates the value
// going out of scope, but not necessarily that a drop call occurs, since the value
// might have been moved-out-of already.
//
// Like MIR, we only drop values whose types need dropping, so `D` implements `Drop`
// (whereas integers, references, and `Option<u64>` don't need dropping).
//
// Note the following differences between VIR and MIR, which are expected:
//  - VIR uses temporaries for all let initializers, whereas MIR writes a simple
//    by-value binding (let x = e;) directly into the local. This doesn't impact drops.
//  - MIR uses temporaries in some places where VIR doesn't (e.g., for reborrows).
//    This doesn't impact drops, since references have no drop glue.

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
    Overwrite(Temp_2)        // use_ref(&mk())
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_3)        // mk()
    ScopeDrop(Temp_3)        // mk()
    Overwrite(Temp_4)        // mk()
    Overwrite(Temp_5)        // &mk()
    Overwrite(Temp_6)        // mk()
    Overwrite(Temp_7)        // &mk()
    Overwrite(Temp_8)        // use_ref(&mk()) + use_ref(&mk())
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
    Overwrite(Temp_4)        // two(use_ref(&mk()), use_ref(&mk()))
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
    Overwrite(Temp_4)        // (&mk(), use_ref(&mk()), &mk())
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

/// The condition of an `if` is a terminating scope. Like MIR, we drop its temporaries
/// after branching, at the start of each branch.
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
    -> bb1, bb2
bb1:
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(a)
    -> bb3
bb2:
    ScopeDrop(Temp_0)        // mk()
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

/// Without an `else`, the condition's temporaries are still dropped on the false path.
#[test]
fn test_if_condition_no_else() {
    let code = verus_code! {
        fn test() {
            if use_ref(&mk()) == 0 {
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
    Overwrite(Temp_1)        // &mk()
    -> bb1, bb2
bb1:
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_2)        // mk()
    MoveFrom(Temp_2)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(a)
    -> bb3
bb2:
    ScopeDrop(Temp_0)        // mk()
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
    Overwrite(Temp_3)        // opt(&mk())
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
    Overwrite(Temp_3)        // opt(&mk())
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
    Overwrite(Temp_2)        // opt(&mk())
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
    Overwrite(Temp_6)        // opt(&mk())
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
    Overwrite(Temp_2)        // opt(&mk())
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
    Overwrite(Temp_6)        // opt(&mk())
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
    Overwrite(Temp_2)        // opt(&mk())
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
/// (Unlike MIR, which drops the condition's temporaries after branching, on both edges,
/// we drop them before branching, since VIR has no place for drops on the false exit.)
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
    Overwrite(Temp_2)        // opt(&mk())
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
    Overwrite(Temp_2)        // opt(&mk())
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
    Overwrite(Temp_3)        // opt(&mk())
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

/// The variables bound by a parameter's pattern are dropped just before the parameter
#[test]
fn test_param_patterns() {
    let code = verus_code! {
        fn test((a, b): (D, D), c: D, (e, f): (D, D)) {
            let x = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(%param3)
    Overwrite(c)
    Overwrite(%param10)
    MoveFrom(%param3.0)
    MoveFrom(%param3.1)
    Overwrite(a)
    Overwrite(b)
    MoveFrom(%param10.0)
    MoveFrom(%param10.1)
    Overwrite(e)
    Overwrite(f)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_0)        // mk()
    ScopeDrop(x)
    ScopeDrop(f)
    ScopeDrop(e)
    ScopeDrop(%param10)
    ScopeDrop(c)
    ScopeDrop(b)
    ScopeDrop(a)
    ScopeDrop(%param3)
"#,
    );
}

/// Only exec variables are dropped; ghost and tracked variables (and parameters) aren't
#[test]
fn test_no_drops_for_ghost_or_tracked() {
    let code = verus_code! {
        tracked struct T { }
        impl Drop for T {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }
        proof fn mk_t() -> (tracked t: T) { T { } }
        fn test(d: D, tracked t: T, Tracked(u): Tracked<T>, Ghost(g): Ghost<D>) {
            let tracked t2 = mk_t();
            let ghost g2 = D { x: 1 };
            let x = mk();
            let (y, Tracked(v)) = (mk(), Tracked(mk_t()));
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(d)
    Overwrite(t)
    Overwrite(u)
    Overwrite(g)
    Overwrite(verus_tmp)
    MoveFrom(verus_tmp)
    Overwrite(verus_tmp_t2)
    MoveFrom(verus_tmp_t2)
    Overwrite(t2)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // (mk(), mk_t())
    MoveFrom(Temp_1.0)       // (mk(), mk_t())
    MoveFrom(Temp_1.1)       // (mk(), mk_t())
    Overwrite(y)
    Overwrite(verus_tmp_v)
    ScopeDrop(Temp_1)        // (mk(), mk_t())
    MoveFrom(verus_tmp_v)
    Overwrite(v)
    ScopeDrop(y)
    ScopeDrop(x)
    ScopeDrop(d)
"#,
    );
}

/// The temporaries in the arguments of `open_atomic_invariant!` are dropped
/// before the body executes
#[test]
fn test_open_atomic_invariant_arg_temps() {
    let code = verus_code! {
        use vstd::invariant::*;
        #[verifier::external_body]
        proof fn mk_box() -> (tracked b: Option<Box<u8>>) { unimplemented!() }
        proof fn pick<'a, T>(tracked v: &Option<Box<u8>>, tracked x: &'a T) -> (tracked r: &'a T) {
            x
        }
        fn test<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) {
            open_atomic_invariant!(pick(&mk_box(), i.borrow()) => inner => {
                let a = D { x: 0 };
            });
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(i)
    Overwrite(Temp_0)        // mk_box()
    Overwrite(Temp_1)        // &mk_box()
    Overwrite(Temp_2)        // &i
    Overwrite(Temp_3)        // pick(&mk_box(), &i)
    Overwrite(inner)
    ScopeDrop(Temp_0)        // mk_box()
    Overwrite(Temp_4)        // D { x: 0 }
    MoveFrom(Temp_4)         // D { x: 0 }
    Overwrite(a)
    ScopeDrop(Temp_4)        // D { x: 0 }
    ScopeDrop(a)
    MoveFrom(inner)
"#,
    );
}

/// The temporaries in the argument of `try_open_atomic_update!` are dropped
/// before the body executes
#[test]
fn test_open_atomic_update_arg_temps() {
    let code = verus_code! {
        use vstd::atomic::*;
        use vstd::prelude::*;
        pub tracked struct Token { state: u16 }
        #[verifier::external_body]
        proof fn mk_box() -> (tracked b: Option<Box<u8>>) { unimplemented!() }
        proof fn pick<T>(tracked v: &Option<Box<u8>>, tracked x: T) -> (tracked r: T)
            ensures r == x
        {
            x
        }
        fn test<F>(_callback: F)
            atomically (atomic_update) {
                (old: Token) -> (new: Commit<Token>),
                ensures new@ == old,
            },
        {
            try_open_atomic_update!(pick(&mk_box(), atomic_update), token => {
                let a = D { x: 0 };
                Tracked(Commit(token))
            });
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(_callback)
    Overwrite(atomic_update)
    Overwrite(Temp_0)        // mk_box()
    Overwrite(Temp_1)        // &mk_box()
    MoveFrom(atomic_update)
    Overwrite(token)
    ScopeDrop(Temp_0)        // mk_box()
    Overwrite(Temp_2)        // D { x: 0 }
    MoveFrom(Temp_2)         // D { x: 0 }
    Overwrite(a)
    ScopeDrop(Temp_2)        // D { x: 0 }
    MoveFrom(token)
    ScopeDrop(a)
    MoveFrom(token)
    Overwrite(Temp_3)        // { ... }
    ScopeDrop(_callback)
"#,
    );
}

/// `for` loops (which are wrapped in a loop isolation boundary), in both editions
#[test]
fn test_for_loop() {
    for edition in ["--edition 2021", "--edition 2024"] {
        let code = verus_code! {
            fn test() {
                for i in 0..use_ref(&mk()) {
                    let a = mk();
                }
                let k = mk();
            }
        };
        check_cfg(code, "test", &[edition], FOR_LOOP_CFG);
    }
}

const FOR_LOOP_CFG: &str = r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // Range { start: 0, end: use_ref(&mk()) }
    MoveFrom(Temp_2)         // Range { start: 0, end: use_ref(&mk()) }
    Overwrite(VERUS_iter_init)
    ScopeDrop(Temp_0)        // mk()
    MoveFrom(VERUS_iter_init)
    -> bb2
bb2 (may_unwind):
    Overwrite(Temp_3)        // into_iter({ VERUS_iter_init })
    MoveFrom(Temp_3)         // into_iter({ VERUS_iter_init })
    Overwrite(VERUS_exec_iter)
    MoveFrom(VERUS_exec_iter)
    -> bb4
bb4:
    Overwrite(Temp_4)        // new({ VERUS_exec_iter })
    MoveFrom(Temp_4)         // new({ VERUS_exec_iter })
    Overwrite(VERUS_iter)
    -> bb5
bb5:
    MoveFrom(VERUS_iter)
    Overwrite(VERUS_ghost_iter)
    -> bb6
bb6 (may_unwind):
    Uninitialize(VERUS_loop_next)
    Mutate(VERUS_ghost_iter)
    -> bb9
bb7:
    -> bb13
bb9:
    Overwrite(Temp_5)        // next({ &mut VERUS_ghost_iter })
    -> bb10, bb11
bb10:
    Overwrite(VERUS_loop_val)
    Overwrite(VERUS_loop_next)
    -> bb12
bb11:
    -> bb7
bb12:
    Overwrite(i)
    Overwrite(Temp_6)        // mk()
    MoveFrom(Temp_6)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_6)        // mk()
    ScopeDrop(a)
    Overwrite(Temp_7)        // {...}
    -> bb6
bb13 (exit):
    Overwrite(Temp_8)        // match VERUS_iter {...}
    Overwrite(VERUS_loop_result)
    Overwrite(Temp_9)        // mk()
    MoveFrom(Temp_9)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_9)        // mk()
    ScopeDrop(k)
"#;

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
    Overwrite(Temp_4)        // vec_index(&mk_vec(), 0)
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

/// Run Verus on the code and return the VIR log
fn vir_log(code: String) -> String {
    let test_dir = tempfile::tempdir().expect("temporary test directory");
    let entry_file = test_dir.path().join("test.rs");
    let log_dir = test_dir.path().join("log");
    std::fs::write(&entry_file, format!("{}{}{}{}", FEATURE_PRELUDE, USE_PRELUDE, DEFS, code))
        .expect("test source");

    let log_dir_option = format!("--log-dir={}", log_dir.display());
    let options = ["--no-verify", "--log-vir", &log_dir_option];
    let output = run_verus(&options, test_dir.path(), &entry_file, true, false);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));

    std::fs::read_to_string(log_dir.join("crate.vir")).expect("read vir log")
}

/// Run Verus on the code and return the `Drop(CallArg(id, idx))` and `Drop(AssignRhs(id))`
/// nodes in the VIR, in order, as a space-separated list of `<node><idx>` (with `idx` = `r`
/// for `AssignRhs`), where each distinct node id is replaced by a letter (`A`, `B`, ...)
/// in order of first appearance.
/// To show where the drops are, the list also includes the early exits
/// (`return`, `break`, `continue`), which the drops should immediately precede.
/// (resolution_inference doesn't track the operand temporaries of calls, constructors,
/// and assignments, so these drops don't appear in the CFG.)
fn operand_drops(code: String) -> String {
    let log = vir_log(code);
    let re = regex::Regex::new(
        r"Drop\s+\(LocalOrTemp\s+(?:CallArg\s+(\d+)\s+(\d+)|AssignRhs\s+(\d+))\)|> (Return)\s|> BreakOrContinue\s+:label\s+\(Label[^)]*\)\s+:is_break\s+(true|false)",
    )
    .unwrap();
    let mut ids: Vec<String> = vec![];
    let mut drops: Vec<String> = vec![];
    for cap in re.captures_iter(&log) {
        if cap.get(4).is_some() {
            drops.push("return".to_string());
            continue;
        }
        if let Some(is_break) = cap.get(5) {
            drops.push(if is_break.as_str() == "true" { "break" } else { "continue" }.to_string());
            continue;
        }
        let (id, idx) = match cap.get(1) {
            Some(id) => (id.as_str().to_string(), cap[2].to_string()),
            None => (cap[3].to_string(), "r".to_string()),
        };
        let n = match ids.iter().position(|i| *i == id) {
            Some(n) => n,
            None => {
                ids.push(id);
                ids.len() - 1
            }
        };
        drops.push(format!("{}{}", (b'A' + n as u8) as char, idx));
    }
    drops.join(" ")
}

/// The arguments of a call live in temporaries until the call moves them;
/// on an early exit from a later argument, the earlier arguments are dropped
/// in reverse order. Arguments whose types don't need dropping aren't dropped.
#[test]
fn test_operand_drops() {
    let code = verus_code! {
        fn three(a: D, b: D, c: D) no_unwind {}
        fn num(a: u64, b: D) no_unwind {}
        fn test(c: bool) {
            three(mk(), mk(), if c { return; } else { mk() });
            num(5, if c { return; } else { mk() });
            three(mk(), mk(), mk());
        }
    };
    assert_eq!(operand_drops(code), "A1 A0 return return");
}

/// For nested calls, the inner call's arguments are dropped first
#[test]
fn test_call_arg_drops_nested() {
    let code = verus_code! {
        fn two(a: D, b: D) -> D no_unwind { a }
        fn test(c: bool) {
            two(mk(), two(mk(), if c { return; } else { mk() }));
        }
    };
    assert_eq!(operand_drops(code), "A0 B0 return");
}

/// Method receivers are call arguments; `break` drops them too
#[test]
fn test_call_arg_drops_method_break() {
    let code = verus_code! {
        impl D { fn consume(self, b: D) no_unwind {} }
        fn test() {
            loop {
                mk().consume(if cond() { break; } else { mk() });
            }
        }
    };
    assert_eq!(operand_drops(code), "A0 break");
}

/// The fields of constructors (tuples, tuple structs, and structs) and the elements
/// of array literals are operands like call arguments
#[test]
fn test_ctor_arg_drops() {
    let code = verus_code! {
        struct T(D, D);
        struct S { a: D, b: D }
        fn test(c: bool) {
            let t = (mk(), if c { return; } else { mk() });
            let t = T(mk(), if c { return; } else { mk() });
            let s = S { a: mk(), b: if c { return; } else { mk() } };
            let a = [mk(), mk(), if c { return; } else { mk() }];
        }
    };
    assert_eq!(operand_drops(code), "A0 return B0 return C0 return D1 D0 return");
}

/// The operands of overloaded operators, and the arguments of closure calls
/// (which are fields of a tuple), are operands too
#[test]
fn test_call_arg_drops_operator_closure() {
    let code = verus_code! {
        impl std::ops::Add for D { type Output = D; fn add(self, o: D) -> D { o } }
        fn test(c: bool) {
            let d = mk() + (if c { return; } else { mk() });
            let f = |a: D, b: D| {};
            f(mk(), if c { return; } else { mk() });
        }
    };
    assert_eq!(operand_drops(code), "A0 return B0 return");
}

/// The right-hand side of an assignment is evaluated before the place,
/// and is dropped if the evaluation of the place exits early
#[test]
fn test_assign_rhs_drops() {
    let code = verus_code! {
        fn pick(a: &mut D, i: u64) -> &mut D no_unwind { a }
        fn test(c: bool, a: &mut D, v: &mut Vec<D>) {
            *pick(a, if c { return; } else { 0 }) = mk();
            v[if c { return; } else { 0 }] = mk();
            let mut x = mk();
            x = mk();
        }
    };
    assert_eq!(operand_drops(code), "Ar return Br return");
}

/// The awaited future is moved into a binding (`__awaitee`) in the desugaring of `.await`,
/// which is dropped after the await completes
#[test]
fn test_await_drops() {
    let code = verus_code! {
        async fn f() -> u64 { 0 }
        async fn test() -> u64 {
            let d = mk();
            let r = f().await;
            r
        }
    };
    let log = vir_log(code);
    let re = regex::Regex::new(r#"> (Await)|Drop\s+\(LocalOrTemp\s+Local\s+\(VarIdent\s+"(\w+)""#)
        .unwrap();
    let events: Vec<String> = re
        .captures_iter(&log)
        .map(|cap| match cap.get(1) {
            Some(_) => "await".to_string(),
            None => cap[2].to_string(),
        })
        .collect();
    assert_eq!(events.join(" "), "await __awaitee d");
}

// The body of a dual-mode const is mode-checked as spec code, so it doesn't get drops
// (but the body of an exec const does)
test_verify_one_file! {
    #[test] test_dual_mode_const_no_drops verus_code! {
        use vstd::prelude::*;
        #[allow(path_statements)]
        pub const C: u64 = { None::<Vec<u8>>; 0 };
        struct T;
        impl T {
            #[allow(path_statements)]
            pub const AC: u64 = { None::<Vec<u8>>; 0 };
        }
        #[allow(path_statements)]
        pub exec const E: u64 = { None::<Vec<u8>>; 0 };
        trait Tr {
            const TC: u64;
            #[allow(path_statements)]
            const TD: u64 = { None::<Vec<u8>>; 0 };
        }
        impl Tr for T {
            #[allow(path_statements)]
            const TC: u64 = { None::<Vec<u8>>; 0 };
        }
    } => Ok(())
}

/// An expression statement `p;`, where `p` is a place, moves the value into a temporary
/// that is dropped at the end of the statement
#[test]
fn test_unused_place_drops() {
    let code = verus_code! {
        #[allow(path_statements)]
        fn test() {
            let x = mk();
            x;
            let y = mk();
            let p = (mk(), mk());
            p.0;
        }
    };
    let log = vir_log(code);
    let re =
        regex::Regex::new(r#"Drop\s+\(LocalOrTemp\s+(?:Local\s+\(VarIdent\s+"(\w+)"|(Unused))"#)
            .unwrap();
    let events: Vec<String> = re
        .captures_iter(&log)
        .map(|cap| match cap.get(1) {
            Some(x) => x.as_str().to_string(),
            None => "unused".to_string(),
        })
        .collect();
    assert_eq!(events.join(" "), "unused unused p y x");
}

/// The temporaries in the arguments of a `proof_with!` call with ghost outputs (`=>`)
/// are dropped where they would be dropped for the plain call `f(&mk())`
/// (in edition 2021, at the end of the statement; in edition 2024, at the end of the block)
#[test]
fn test_proof_with_outputs() {
    let code = || {
        code! {
            verus! {
                fn g(a: u64, b: &D) -> u64 { a }
            }

            #[verus_spec(ret =>
                with Ghost(w): Ghost<u32>, -> z: Ghost<u32>
            )]
            fn f(x: &D) -> u64 {
                proof_with!{|= Ghost(0u32)}
                x.x
            }

            #[verus_spec]
            fn test() {
                proof_decl!{ let ghost mut z = 0u32; }
                let r = g({ proof_with!{Ghost(0) => Ghost(z)} f(&mk()) }, &mk());
            }
        }
    };
    check_cfg(
        code(),
        "test",
        &["--edition 2021"],
        r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_f(&mk(), 0)
    -> bb3
bb3:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb4
bb4 (may_unwind):
    Overwrite(Temp_3)        // mk()
    Overwrite(Temp_4)        // &mk()
    -> bb6
bb6 (exit):
    Overwrite(Temp_5)        // g({ match _VERUS_VERIFIED_f(&..., 0) {...} }, &mk())
    Overwrite(r)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(Temp_0)        // mk()
"#,
    );
    check_cfg(
        code(),
        "test",
        &["--edition 2024"],
        r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_f(&mk(), 0)
    -> bb3
bb3:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb4
bb4 (may_unwind):
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_3)        // mk()
    Overwrite(Temp_4)        // &mk()
    -> bb6
bb6 (exit):
    Overwrite(Temp_5)        // g({ Left(match ... {...}, drop) }, &mk())
    Overwrite(r)
    ScopeDrop(Temp_3)        // mk()
"#,
    );
}

/// `?` returns early with the residual, dropping the locals and parameters
#[test]
fn test_question_mark() {
    let code = verus_code! {
        fn test(o: Option<D>, p: D) -> Option<u64> {
            let a = mk();
            let d = o?;
            Some(use_ref(&d))
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, may_unwind):
    Overwrite(o)
    Overwrite(p)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    MoveFrom(o)
    -> bb2
bb2:
    Overwrite(Temp_1)        // branch(o)
    -> bb3, bb6
bb3 (may_unwind):
    Overwrite(residual)
    -> bb5
bb5 (exit):
    ScopeDrop(Temp_1)        // branch(o)
    ScopeDrop(a)
    ScopeDrop(p)
    ScopeDrop(o)
bb6:
    MoveFrom(Temp_1.Continue_0) // branch(o)
    Overwrite(val)
    MoveFrom(val)
    ScopeDrop(val)
    -> bb7
bb7 (exit):
    Overwrite(Temp_2)        // match branch(o) {...}
    MoveFrom(Temp_2)         // match branch(o) {...}
    Overwrite(d)
    ScopeDrop(Temp_2)        // match branch(o) {...}
    ScopeDrop(Temp_1)        // branch(o)
    Overwrite(Temp_3)        // &d
    ScopeDrop(d)
    ScopeDrop(a)
    ScopeDrop(p)
    ScopeDrop(o)
"#,
    );
}

/// The parameters of an async fn are dropped after the locals of its body
#[test]
fn test_async_params() {
    let code = verus_code! {
        async fn test(a: D, b: D) -> u64 {
            let x = mk();
            if use_ref(&x) == 0 {
                return 1;
            }
            use_ref(&a)
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry):
    Overwrite(a)
    Overwrite(b)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(x)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // &x
    -> bb1, bb2
bb1 (exit):
    ScopeDrop(x)
    ScopeDrop(b)
    ScopeDrop(a)
bb2:
    -> bb3
bb3 (exit):
    Overwrite(Temp_2)        // &a
    ScopeDrop(x)
    ScopeDrop(b)
    ScopeDrop(a)
"#,
    );
}

/// A closure with a specification, whose parameter is dropped after its body
#[test]
fn test_closure_with_spec() {
    let code = verus_code! {
        fn test() {
            let f = |a: D| -> (r: u64)
                requires a.x == 0
                ensures r == 0
            {
                let b = mk();
                0
            };
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(Temp_1)        // { |...| ... }
    Overwrite(f)
bb1 (entry):
    Overwrite(a)
    -> bb2
bb2 (exit):
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_0)        // mk()
    ScopeDrop(b)
    ScopeDrop(a)
"#,
    );
}

/// In edition 2021, the temporaries of the tail expression of a `while` body
/// are dropped at the end of each iteration
#[test]
fn test_while_body_tail_2021() {
    let code = verus_code! {
        fn unit_ref(d: &D) no_unwind {}
        fn test() {
            let mut i: u64 = 0;
            while i < 10
                invariant i <= 10,
                decreases 10 - i,
            {
                i = i + 1;
                unit_ref(&mk())
            }
        }
    };
    check_cfg(
        code,
        "test",
        &["--edition 2021"],
        r#"
bb0 (entry):
    Overwrite(Temp_0)        // 0
    Overwrite(i)
    -> bb1
bb1:
    -> bb3, bb4
bb2 (exit):
bb3:
    -> bb2
bb4:
    Overwrite(i)
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    ScopeDrop(Temp_1)        // mk()
    -> bb1
"#,
    );
}

/// If the pattern of a let-else fails to match, the temporaries of the initializer are
/// dropped before the else block, which can `break` or `continue` out of an enclosing loop
#[test]
fn test_let_else_break_continue() {
    let code = verus_code! {
        fn test() {
            loop {
                let a = mk();
                let Some(v) = opt(&mk()) else { break };
                let Some(w) = opt(&mk()) else { continue };
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
    -> bb1
bb1:
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    Overwrite(Temp_3)        // opt(&mk())
    -> bb3, bb4
bb2 (exit):
bb3:
    ScopeDrop(Temp_1)        // mk()
    ScopeDrop(a)
    -> bb2
bb4:
    Overwrite(v)
    ScopeDrop(Temp_1)        // mk()
    Overwrite(Temp_4)        // mk()
    Overwrite(Temp_5)        // &mk()
    Overwrite(Temp_6)        // opt(&mk())
    -> bb5, bb6
bb5:
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(a)
    -> bb1
bb6:
    Overwrite(w)
    ScopeDrop(Temp_4)        // mk()
    Overwrite(Temp_7)        // mk()
    MoveFrom(Temp_7)         // mk()
    Overwrite(b)
    ScopeDrop(Temp_7)        // mk()
    ScopeDrop(b)
    ScopeDrop(a)
    -> bb1
"#,
    );
}

// The result of a `proof_with!` call with ghost outputs (`=>`) isn't a temporary
// that lives until the end of the statement (which would extend the borrow in it)
test_verify_one_file_with_options! {
    #[test] test_proof_with_outputs_borrow_2021 ["--edition 2021"] => code! {
        verus! {
            pub struct G<'a> { pub r: &'a mut u64 }
            impl<'a> Drop for G<'a> {
                fn drop(&mut self)
                    opens_invariants none
                    no_unwind
                {}
            }
            pub fn consume(g: G) -> (r: u64) ensures r == 0 { 0 }
            pub fn use_mut(x: &mut u64) -> (r: u64) ensures r == 0 { 0 }
        }

        #[verus_spec(ret => with Ghost(w): Ghost<u32> -> z: Ghost<u32>)]
        fn g(x: &mut u64) -> G<'_> {
            proof_with!{|= Ghost(0u32)}
            G { r: x }
        }

        #[verus_spec]
        fn test(mut x: u64) -> u64 {
            proof_decl!{ let ghost mut z = 0u32; }
            let a = consume({ proof_with!{Ghost(0) => Ghost(z)} g(&mut x) }) + use_mut(&mut x);
            a
        }
    } => Ok(())
}

// The result of a `proof_with!` call with ghost outputs (`=>`) isn't a temporary
// that lives until the end of the statement (which would extend the borrow in it)
test_verify_one_file_with_options! {
    #[test] test_proof_with_outputs_borrow_2024 ["--edition 2024"] => code! {
        verus! {
            pub struct G<'a> { pub r: &'a mut u64 }
            impl<'a> Drop for G<'a> {
                fn drop(&mut self)
                    opens_invariants none
                    no_unwind
                {}
            }
            pub fn consume(g: G) -> (r: u64) ensures r == 0 { 0 }
            pub fn use_mut(x: &mut u64) -> (r: u64) ensures r == 0 { 0 }
        }

        #[verus_spec(ret => with Ghost(w): Ghost<u32> -> z: Ghost<u32>)]
        fn g(x: &mut u64) -> G<'_> {
            proof_with!{|= Ghost(0u32)}
            G { r: x }
        }

        #[verus_spec]
        fn test(mut x: u64) -> u64 {
            proof_decl!{ let ghost mut z = 0u32; }
            let a = consume({ proof_with!{Ghost(0) => Ghost(z)} g(&mut x) }) + use_mut(&mut x);
            a
        }
    } => Ok(())
}

/// Other forms of `proof_with!` with ghost outputs (method calls, `?`, nested `proof_with!`,
/// and `#[verus_spec(with ..)] let`): the temporaries in the call are dropped where they
/// would be dropped without `proof_with!`
#[test]
fn test_proof_with_outputs_forms() {
    let code = || {
        code! {
            #[verus_spec(ret => with Ghost(w): Ghost<u32> -> z: Ghost<u32>)]
            fn f(x: &D) -> u64 { proof_with!{|= Ghost(0u32)} 0 }

            #[verus_spec(ret => with Ghost(w): Ghost<u32> -> z: Ghost<u32>)]
            fn fr(x: &D) -> Option<u64> { proof_with!{|= Ghost(0u32)} Some(0) }

            #[verifier::verify]
            struct S;
            impl S {
                #[verus_spec(ret => with Ghost(w): Ghost<u32> -> z: Ghost<u32>)]
                fn m(&self, x: &D) -> u64 { proof_with!{|= Ghost(0u32)} 0 }
            }

            #[verus_spec(ret => with Ghost(w): Ghost<u32>)]
            fn h(x: u64, y: &D) -> u64 { x }

            #[verus_spec]
            fn t_method(s: S) -> (u64, u64) {
                proof_decl!{ let ghost mut z = 0u32; }
                let b = (use_ref(&mk()), { proof_with!{Ghost(0) => Ghost(z)} s.m(&mk()) });
                b
            }

            #[verus_spec]
            fn t_try() -> Option<u64> {
                proof_decl!{ let ghost mut z = 0u32; }
                let a = { proof_with!{Ghost(0) => Ghost(z)} fr(&mk())? };
                Some(a)
            }

            #[verus_spec]
            fn t_nested() -> u64 {
                proof_decl!{ let ghost mut z = 0u32; }
                let c = { proof_with!{Ghost(1)} h({ proof_with!{Ghost(0) => Ghost(z)} f(&mk()) }, &mk()) };
                c
            }

            #[verus_spec]
            fn t_let() -> u64 {
                proof_decl!{ let ghost mut z = 0u32; }
                #[verus_spec(with Ghost(0) => Ghost(z))]
                let d = f(&mk());
                let k = mk();
                d
            }
        }
    };
    check_cfg(
        code(),
        "t_method",
        &["--edition 2021"],
        r#"
bb0 (entry, may_unwind):
    Overwrite(s)
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Overwrite(Temp_2)        // mk()
    Overwrite(Temp_3)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_4)        // _VERUS_VERIFIED_m(&s, &mk(), 0)
    -> bb3
bb3:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb4
bb4 (exit):
    Overwrite(Temp_5)        // (use_ref(&mk()), { match ... {...} })
    Overwrite(b)
    ScopeDrop(Temp_2)        // mk()
    ScopeDrop(Temp_0)        // mk()
"#,
    );
    check_cfg(
        code(),
        "t_try",
        &["--edition 2021"],
        r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_fr(&mk(), 0)
    -> bb3
bb3:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb4
bb4 (may_unwind):
    -> bb6
bb6:
    Overwrite(Temp_3)        // branch(match _VERUS_VERIFIED_fr(&mk(), 0) {...})
    -> bb7, bb10
bb7 (may_unwind):
    Overwrite(residual)
    -> bb9
bb9 (exit):
    ScopeDrop(Temp_0)        // mk()
bb10:
    Overwrite(val)
    -> bb11
bb11 (exit):
    Overwrite(Temp_4)        // { match branch(match ... {...}) {...} }
    Overwrite(a)
    ScopeDrop(Temp_0)        // mk()
"#,
    );
    check_cfg(
        code(),
        "t_nested",
        &["--edition 2021"],
        r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_f(&mk(), 0)
    -> bb3
bb3:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb4
bb4 (may_unwind):
    Overwrite(Temp_3)        // mk()
    Overwrite(Temp_4)        // &mk()
    -> bb6
bb6 (exit):
    Overwrite(Temp_5)        // { _VERUS_VERIFIED_h({ match ... {...} }, &mk(), 1) }
    Overwrite(c)
    ScopeDrop(Temp_3)        // mk()
    ScopeDrop(Temp_0)        // mk()
"#,
    );
    check_cfg(
        code(),
        "t_let",
        &["--edition 2021"],
        r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_f(&mk(), 0)
    -> bb3
bb3:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb4
bb4 (exit):
    Overwrite(Temp_3)        // match _VERUS_VERIFIED_f(&mk(), 0) {...}
    Overwrite(d)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_4)        // mk()
    MoveFrom(Temp_4)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_4)        // mk()
    ScopeDrop(k)
"#,
    );
}

/// A `proof_fn` closure created in exec code is proof code, so it doesn't get drops
/// (and its tracked parameter isn't dropped)
#[test]
fn test_proof_fn_closure() {
    let code = verus_code! {
        fn test() {
            let tracked f = proof_fn|tracked d: D| -> (r: u64) { 0 };
            let k = mk();
        }
    };
    check_cfg(
        code,
        "test",
        &[],
        r#"
bb0 (entry, exit):
    Overwrite(verus_tmp)
    MoveFrom(verus_tmp)
    Overwrite(verus_tmp_f)
    MoveFrom(verus_tmp_f)
    Overwrite(f)
    Overwrite(Temp_0)        // mk()
    MoveFrom(Temp_0)         // mk()
    Overwrite(k)
    ScopeDrop(Temp_0)        // mk()
    ScopeDrop(k)
bb1 (entry):
    Overwrite(d)
    -> bb2
bb2 (exit):
"#,
    );
}

/// `proof_with!` with ghost outputs (`=>`) on a call whose result needs dropping
/// (and with a tracked output), and in a condition or scrutinee
#[test]
fn test_proof_with_outputs_positions() {
    let code = || {
        code! {
            #[verus_spec(ret => with Tracked(w): Tracked<&mut u32> -> z: Tracked<u32>)]
            fn f(x: &D) -> D {
                proof_with!{|= Tracked(0u32)}
                mk()
            }

            #[verus_spec(ret => with Ghost(w): Ghost<u32> -> z: Ghost<u32>)]
            fn g(x: &D) -> D {
                proof_with!{|= Ghost(0u32)}
                mk()
            }

            #[verus_spec(ret => with Ghost(w): Ghost<u32> -> z: Ghost<u32>)]
            fn gb(x: &D) -> bool {
                proof_with!{|= Ghost(0u32)}
                true
            }

            #[verus_spec]
            fn t_drop_result() -> u64 {
                proof_decl!{ let tracked mut t = 0u32; let tracked mut z = 0u32; }
                let a = { proof_with!{Tracked(&mut t) => Tracked(z)} f(&mk()) };
                let k = use_ref(&a);
                k
            }

            #[verus_spec]
            fn t_if() -> u64 {
                proof_decl!{ let ghost mut z = 0u32; }
                if { proof_with!{Ghost(0) => Ghost(z)} gb(&mk()) } { 1 } else { 2 }
            }

            #[verus_spec]
            fn t_while() -> u64 {
                proof_decl!{ let ghost mut z = 0u32; }
                let mut i = 0;
                #[verus_spec(invariant i <= 10, decreases 10 - i)]
                while { proof_with!{Ghost(0) => Ghost(z)} gb(&mk()) } && i < 10
                { i += 1; }
                i
            }

            #[verus_spec]
            fn t_match() -> u64 {
                proof_decl!{ let ghost mut z = 0u32; }
                let x = match { proof_with!{Ghost(0) => Ghost(z)} g(&mk()) } { d => use_ref(&d) };
                x
            }
        }
    };
    for f in ["t_drop_result", "t_if", "t_while", "t_match"] {
        let expected = match f {
            "t_drop_result" => {
                r#"
bb0 (entry, may_unwind):
    Overwrite(verus_tmp)
    Overwrite(verus_tmp_t)
    Overwrite(t)
    Overwrite(verus_tmp)
    Overwrite(verus_tmp_z)
    Overwrite(z)
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    Mutate(t)
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_f(&mk(), &mut t)
    -> bb3
bb3:
    MoveFrom(Temp_2)         // _VERUS_VERIFIED_f(&mk(), &mut t)
    Overwrite(__verus_tmp_tuple_var__)
    MoveFrom(__verus_tmp_tuple_var__.0)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    Overwrite(z)
    MoveFrom(__verus_tmp_expr_var__)
    ScopeDrop(__verus_tmp_expr_var__)
    ScopeDrop(__verus_tmp_tuple_var__)
    -> bb4
bb4 (exit):
    Overwrite(Temp_3)        // { match _VERUS_VERIFIED_f(&mk(), &mut t) {...} }
    MoveFrom(Temp_3)         // { match _VERUS_VERIFIED_f(&mk(), &mut t) {...} }
    Overwrite(a)
    ScopeDrop(Temp_3)        // { match _VERUS_VERIFIED_f(&mk(), &mut t) {...} }
    ScopeDrop(Temp_2)        // _VERUS_VERIFIED_f(&mk(), &mut t)
    ScopeDrop(Temp_0)        // mk()
    Overwrite(Temp_4)        // &a
    Overwrite(Temp_5)        // use_ref(&a)
    Overwrite(k)
    ScopeDrop(a)
"#
            }
            "t_if" => {
                r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_gb(&mk(), 0)
    -> bb3
bb3:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb4
bb4:
    -> bb5, bb6
bb5:
    ScopeDrop(Temp_0)        // mk()
    -> bb7
bb6:
    ScopeDrop(Temp_0)        // mk()
    -> bb7
bb7 (exit):
"#
            }
            "t_while" => {
                r#"
bb0 (entry):
    Overwrite(Temp_0)        // 0
    Overwrite(i)
    -> bb1
bb1 (may_unwind):
    Overwrite(Temp_1)        // mk()
    Overwrite(Temp_2)        // &mk()
    -> bb4
bb2 (exit):
bb4:
    Overwrite(Temp_3)        // _VERUS_VERIFIED_gb(&mk(), 0)
    -> bb5
bb5:
    Overwrite(__verus_tmp_tuple_var__)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    -> bb6
bb6:
    ScopeDrop(Temp_1)        // mk()
    -> bb7, bb8
bb7:
    -> bb8
bb8:
    -> bb9, bb10
bb9:
    -> bb2
bb10:
    Mutate(i)
    -> bb1
"#
            }
            "t_match" => {
                r#"
bb0 (entry, may_unwind):
    Overwrite(Temp_0)        // mk()
    Overwrite(Temp_1)        // &mk()
    -> bb2
bb2:
    Overwrite(Temp_2)        // _VERUS_VERIFIED_g(&mk(), 0)
    -> bb3
bb3:
    MoveFrom(Temp_2)         // _VERUS_VERIFIED_g(&mk(), 0)
    Overwrite(__verus_tmp_tuple_var__)
    MoveFrom(__verus_tmp_tuple_var__.0)
    Overwrite(__verus_tmp_expr_var__)
    Overwrite(verus_tmp_z)
    MoveFrom(__verus_tmp_expr_var__)
    ScopeDrop(__verus_tmp_expr_var__)
    ScopeDrop(__verus_tmp_tuple_var__)
    -> bb4
bb4:
    Overwrite(Temp_3)        // { match _VERUS_VERIFIED_g(&mk(), 0) {...} }
    -> bb5
bb5:
    MoveFrom(Temp_3)         // { match _VERUS_VERIFIED_g(&mk(), 0) {...} }
    Overwrite(d)
    Overwrite(Temp_4)        // &d
    ScopeDrop(d)
    -> bb6
bb6 (exit):
    Overwrite(Temp_5)        // match { match _VERUS_VERIFIED_g(&..., 0) {...} } {...}
    Overwrite(x)
    ScopeDrop(Temp_3)        // { match _VERUS_VERIFIED_g(&mk(), 0) {...} }
    ScopeDrop(Temp_2)        // _VERUS_VERIFIED_g(&mk(), 0)
    ScopeDrop(Temp_0)        // mk()
"#
            }
            _ => unreachable!(),
        };
        check_cfg(code(), f, &["--edition 2021"], expected);
    }
}
