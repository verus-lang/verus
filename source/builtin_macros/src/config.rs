use std::sync::OnceLock;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum EraseGhost {
    /// keep all ghost code
    Keep,
    /// erase ghost code, but leave ghost stubs
    Erase,
    /// erase all ghost code
    EraseAll,
}

impl EraseGhost {
    pub(crate) fn keep(&self) -> bool {
        match self {
            EraseGhost::Keep => true,
            EraseGhost::Erase | EraseGhost::EraseAll => false,
        }
    }

    pub(crate) fn erase(&self) -> bool {
        match self {
            EraseGhost::Keep => false,
            EraseGhost::Erase | EraseGhost::EraseAll => true,
        }
    }

    pub(crate) fn erase_all(&self) -> bool {
        match self {
            EraseGhost::Keep | EraseGhost::Erase => false,
            EraseGhost::EraseAll => true,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum VstdKind {
    /// The current crate is vstd.
    IsVstd,
    /// There is no vstd (only verus_builtin). Really only used for testing.
    NoVstd,
    /// Imports the vstd crate like usual.
    Imported,
    /// Embed vstd and verus_builtin as modules, necessary for verifying the `core` library.
    IsCore,
    /// For other crates in stdlib verification that import core
    ImportedViaCore,
}

pub(crate) fn vstd_kind() -> VstdKind {
    static VSTD_KIND: OnceLock<VstdKind> = OnceLock::new();
    *VSTD_KIND.get_or_init(|| {
        match std::env::var("VSTD_KIND") {
            Ok(s) => {
                if &s == "IsVstd" {
                    return VstdKind::IsVstd;
                } else if &s == "NoVstd" {
                    return VstdKind::NoVstd;
                } else if &s == "Imported" {
                    return VstdKind::Imported;
                } else if &s == "IsCore" {
                    return VstdKind::IsCore;
                } else if &s == "ImportedViaCore" {
                    return VstdKind::ImportedViaCore;
                } else {
                    panic!("The environment variable VSTD_KIND was set but its value ('{:}') is invalid. Allowed values are 'IsVstd', 'NoVstd', 'Imported', 'IsCore', and 'ImportedViaCore'", s);
                }
            }
            _ => { }
        }

        // When building vstd normally through cargo, we won't get a VSTD_KIND env var,
        // but we can use CARGO_PGK_NAME instead.
        let is_vstd = std::env::var("CARGO_PKG_NAME").map_or(false, |s| s == "vstd");
        if is_vstd {
            return VstdKind::IsVstd;
        }

        // For tests, which don't go through the verus binary, we infer the mode from
        // these cfg options
        if cfg_verify_core() {
            return VstdKind::IsCore;
        }
        if cfg_no_vstd() {
            return VstdKind::NoVstd;
        }

        // If none of the above, we assume a normal build
        return VstdKind::Imported;
    })
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_verify_core() -> bool {
    static CFG_VERIFY_CORE: OnceLock<bool> = OnceLock::new();
    *CFG_VERIFY_CORE.get_or_init(|| {
        let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_verify_core) }.into();
        let bool_ts = match ts.expand_expr() {
            Ok(name) => name.to_string(),
            _ => {
                panic!("cfg_verify_core call failed")
            }
        };
        match bool_ts.as_str() {
            "true" => true,
            "false" => false,
            _ => {
                panic!("cfg_verify_core call failed")
            }
        }
    })
}

// Because 'expand_expr' is unstable, we need a different impl when `not(verus_keep_ghost)`.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_verify_core() -> bool {
    false
}

#[cfg(verus_keep_ghost)]
fn cfg_no_vstd() -> bool {
    static CFG_VERIFY_CORE: OnceLock<bool> = OnceLock::new();
    *CFG_VERIFY_CORE.get_or_init(|| {
        let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_no_vstd) }.into();
        let bool_ts = match ts.expand_expr() {
            Ok(name) => name.to_string(),
            _ => {
                panic!("cfg_no_vstd call failed")
            }
        };
        match bool_ts.as_str() {
            "true" => true,
            "false" => false,
            _ => {
                panic!("cfg_no_vstd call failed")
            }
        }
    })
}

// Because 'expand_expr' is unstable, we need a different impl when `not(verus_keep_ghost)`.
#[cfg(not(verus_keep_ghost))]
fn cfg_no_vstd() -> bool {
    false
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_erase() -> EraseGhost {
    let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_keep_ghost_body) }.into();
    let ts_stubs: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_keep_ghost) }.into();
    let (bool_ts, bool_ts_stubs) = match (ts.expand_expr(), ts_stubs.expand_expr()) {
        (Ok(name), Ok(name_stubs)) => (name.to_string(), name_stubs.to_string()),
        _ => {
            panic!("cfg_erase call failed")
        }
    };
    match (bool_ts.as_str(), bool_ts_stubs.as_str()) {
        ("true", "true" | "false") => EraseGhost::Keep,
        ("false", "true") => EraseGhost::Erase,
        ("false", "false") => EraseGhost::EraseAll,
        _ => {
            panic!("cfg_erase call failed")
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_erase() -> EraseGhost {
    EraseGhost::EraseAll
}
