/// A set of Verus components meant to be used together.
pub struct Toolchain<Str = &'static str> {
    /// The Verus version; the primary key to identify a toolchain.
    pub verus: Str,
    /// The vstd version.
    pub vstd: Crate<Str>,
    /// The Z3 version.
    pub z3: Str,
}

/// Identifies a crate in a registry (i.e. crates.io) or git.
pub enum Crate<Str> {
    /// A version published in a registry.
    Registry { version: Str },
    /// A commit in a git repository (e.g. GitHub).
    GitCommit { git: Str, rev: Str },
}

/// An entry for each file in the `toolchain-manifests` directory.
pub const TOOLCHAINS: [Toolchain; 2] = [
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
