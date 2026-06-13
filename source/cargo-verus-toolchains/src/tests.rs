use crate::{Crate, Indent, Toolchain, ToolchainList};
use pretty_assertions::assert_eq;
use std::fs;

fn make_release_manifest() -> Toolchain {
    Toolchain {
        verus: "0.2026.06.07.cd03505".into(),
        vstd: Crate::Version("0.0.0-2026-05-31-0205".into()),
        z3: "4.12.5".into(),
    }
}

fn make_rolling_release_manifest() -> Toolchain {
    Toolchain {
        verus: "0.2026.06.10.e6a6d4f".into(),
        vstd: Crate::GitCommit {
            git: "https://github.com/verus-lang/verus.git".into(),
            rev: "e6a6d4f".into(),
        },
        z3: "4.12.5".into(),
    }
}

#[test]
fn parse_print_toolchain_release() {
    let toml_str = r#"
        verus = "0.2026.06.07.cd03505"
        vstd = "0.0.0-2026-05-31-0205"
        z3 = "4.12.5"
    "#;

    let expected = make_release_manifest();

    let observed: Toolchain = toml::from_str(toml_str).expect("parse toolchain info");

    assert_eq!(observed, expected);

    let expected_code = r#"Toolchain {
    verus: "0.2026.06.07.cd03505",
    vstd: Crate::Registry { version: "0.0.0-2026-05-31-0205" },
    z3: "4.12.5",
}"#;

    let mut observed_code = String::new();
    observed.format_code(Indent::default(), &mut observed_code).expect("format code");

    assert_eq!(observed_code, expected_code);
}

#[test]
fn parse_print_toolchain_rolling_release() {
    let toml_str = r#"
        verus = "0.2026.06.10.e6a6d4f"
        vstd = { git = "https://github.com/verus-lang/verus.git", rev = "e6a6d4f" }
        z3 = "4.12.5"
    "#;

    let expected = make_rolling_release_manifest();

    let observed: Toolchain = toml::from_str(toml_str).expect("parse toolchain info");

    assert_eq!(observed, expected);

    let expected_code = r#"Toolchain {
    verus: "0.2026.06.10.e6a6d4f",
    vstd: Crate::GitCommit { git: "https://github.com/verus-lang/verus.git", rev: "e6a6d4f" },
    z3: "4.12.5",
}"#;

    let mut observed_code = String::new();
    observed.format_code(Indent::default(), &mut observed_code).expect("format code");

    assert_eq!(observed_code, expected_code);
}

#[test]
fn print_toolchains_code() {
    let toolchains =
        ToolchainList { items: vec![make_rolling_release_manifest(), make_release_manifest()] };

    let expected_code = r#"pub const TOOLCHAINS: [Toolchain; 2] = [
    Toolchain {
        verus: "0.2026.06.10.e6a6d4f",
        vstd: Crate::GitCommit { git: "https://github.com/verus-lang/verus.git", rev: "e6a6d4f" },
        z3: "4.12.5",
    },
    Toolchain {
        verus: "0.2026.06.07.cd03505",
        vstd: Crate::Registry { version: "0.0.0-2026-05-31-0205" },
        z3: "4.12.5",
    },
];
"#;

    let mut observed_code = String::new();
    toolchains.format_code(Indent::default(), &mut observed_code).expect("format code");

    assert_eq!(observed_code, expected_code);
}

#[test]
fn parse_toolchains_from_dir() {
    let toolchains =
        ToolchainList { items: vec![make_rolling_release_manifest(), make_release_manifest()] };

    let dir = tempfile::tempdir().expect("create temp dir");
    for toolchain in &toolchains.items {
        let toml = toml::to_string_pretty(toolchain).expect("serialize manifest");
        let path = dir.path().join(format!("{}.toml", toolchain.verus));
        fs::write(path, toml).expect("write manifest");
    }

    fs::write(dir.path().join("README.md"), "Not a toolchain manifest.")
        .expect("write non-toml file");

    let observed = ToolchainList::parse_from_dir(dir);

    assert_eq!(observed, toolchains);
}
