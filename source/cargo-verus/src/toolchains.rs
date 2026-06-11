/// A toolchain is a set of Verus components meant to be used together.
pub struct Toolchain<Str> {
    pub verus: Str,
    pub vstd: Crate<Str>,
    pub z3: Str,
}

pub enum Crate<Str> {
    Registry { version: Str },
    GitCommit { git: Str, rev: Str },
}

/// An entry for each file in the `toolchain-manifests` directory.
pub const TOOLCHAINS: [Toolchain<&str>; 2] = [
    Toolchain {
        verus: "0.2026.06.07.cd03505",
        vstd: Crate::Registry { version: "0.0.0-2026-05-31-0205" },
        z3: "4.12.5",
    },
    Toolchain {
        verus: "0.2026.06.10.e6a6d4f",
        vstd: Crate::GitCommit { git: "https://github.com/verus-lang/verus.git", rev: "e6a6d4f" },
        z3: "4.12.5",
    },
];
