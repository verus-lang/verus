use crate::{Crate, Toolchain};

#[test]
fn parse_toolchain_release() {
    let toml_str = r#"
        verus = "0.2026.06.07.cd03505"
        vstd = "0.0.0-2026-05-31-0205"
        z3 = "4.12.5"
    "#;

    let expected = Toolchain {
        verus: "0.2026.06.07.cd03505".into(),
        vstd: Crate::Version("0.0.0-2026-05-31-0205".into()),
        z3: "4.12.5".into(),
    };

    let observed: Toolchain = toml::from_str(toml_str).expect("parse toolchain info");

    assert_eq!(observed, expected);
}

#[test]
fn parse_toolchain_rolling_release() {
    let toml_str = r#"
        verus = "0.2026.06.10.e6a6d4f"
        vstd = { git = "https://github.com/verus-lang/verus.git", rev = "e6a6d4f" }
        z3 = "4.12.5"
    "#;

    let expected = Toolchain {
        verus: "0.2026.06.10.e6a6d4f".into(),
        vstd: Crate::GitCommit {
            git: "https://github.com/verus-lang/verus.git".into(),
            rev: "e6a6d4f".into(),
        },
        z3: "4.12.5".into(),
    };

    let observed: Toolchain = toml::from_str(toml_str).expect("parse toolchain info");

    assert_eq!(observed, expected);
}
