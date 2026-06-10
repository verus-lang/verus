use crate::{Crate, Toolchain};

#[test]
fn parse_toolchain_toml() {
    let toml_str = r#"
        verus = "0.2026.06.03.abcdef1"
        vstd = "0.0.0-2026-05-31-0205"
        z3 = "4.12.5"
    "#;

    let expected = Toolchain {
        verus: "0.2026.06.03.abcdef1".into(),
        vstd: Crate::Simple("0.0.0-2026-05-31-0205".into()),
        z3: "4.12.5".into(),
    };

    let observed: Toolchain = toml::from_str(toml_str).expect("parse toolchain info");

    assert_eq!(observed, expected);
}
