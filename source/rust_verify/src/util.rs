use std::fmt::Display;

use rustc_span::Span;
use vir::ast::VirErr;
use vir::ast_util::error as vir_error;

pub(crate) fn err_span<A, S: Into<String>>(span: Span, msg: S) -> Result<A, VirErr> {
    vir_error(&crate::spans::err_air_span(span), msg)
}

pub(crate) fn vir_err_span_str(span: Span, msg: &str) -> VirErr {
    vir_err_span_string(span, msg.to_string())
}

pub(crate) fn vir_err_span_string(span: Span, msg: String) -> VirErr {
    air::messages::error(msg, &crate::spans::err_air_span(span))
}

pub(crate) fn unsupported_err_span<A>(span: Span, msg: String) -> Result<A, VirErr> {
    err_span(span, format!("The verifier does not yet support the following Rust feature: {}", msg))
}

#[macro_export]
macro_rules! unsupported_err {
    ($span: expr, $msg: expr) => {{
        dbg!();
        unsupported_err_span($span, $msg.to_string())?
    }};
    ($span: expr, $msg: expr, $info: expr) => {{
        dbg!($info);
        unsupported_err_span($span, $msg.to_string())?
    }};
}

#[macro_export]
macro_rules! unsupported_err_unless {
    ($assertion: expr, $span: expr, $msg: expr) => {
        if (!$assertion) {
            dbg!();
            unsupported_err_span($span, $msg.to_string())?;
        }
    };
    ($assertion: expr, $span: expr, $msg: expr, $info: expr) => {
        if (!$assertion) {
            dbg!($info);
            unsupported_err_span($span, $msg.to_string())?;
        }
    };
}

#[macro_export]
macro_rules! err_unless {
    ($assertion: expr, $span: expr, $msg: expr) => {
        if (!$assertion) {
            dbg!();
            crate::util::err_span($span, $msg)?;
        }
    };
    ($assertion: expr, $span: expr, $msg: expr, $info: expr) => {
        if (!$assertion) {
            dbg!($info);
            crate::util::err_span($span, $msg)?;
        }
    };
}

/// Basic error, with just a message
pub fn error<S: Into<String>>(msg: S) -> VirErr {
    air::messages::error_bare(msg)
}

#[allow(dead_code)]
pub(crate) fn vec_map<A, B, F: FnMut(&A) -> B>(v: &Vec<A>, f: F) -> Vec<B> {
    v.iter().map(f).collect()
}

#[allow(dead_code)]
pub(crate) fn vec_map_result<A, B, E, F>(v: &Vec<A>, f: F) -> Result<Vec<B>, E>
where
    F: Fn(&A) -> Result<B, E>,
{
    v.iter().map(f).collect()
}

#[allow(dead_code)]
pub(crate) fn slice_vec_map_result<A, B, E, F: Fn(&A) -> Result<B, E>>(
    slice: &[A],
    f: F,
) -> Result<Vec<B>, E> {
    slice.iter().map(f).collect()
}

pub enum VerusBuildProfile {
    Debug,
    Release,
    Unknown,
}

impl std::fmt::Display for VerusBuildProfile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            VerusBuildProfile::Debug => "debug",
            VerusBuildProfile::Release => "release",
            VerusBuildProfile::Unknown => "unknown",
        };
        f.write_str(s)
    }
}

const fn verus_build_profile() -> VerusBuildProfile {
    let profile = option_env!("VARGO_BUILD_PROFILE");
    match profile {
        Some(p) => {
            if const_str_equal(p, "release") {
                VerusBuildProfile::Release
            } else if const_str_equal(p, "debug") {
                VerusBuildProfile::Debug
            } else {
                panic!("unexpected VARGO_BUILD_PROFILE");
            }
        }
        None => VerusBuildProfile::Unknown,
    }
}

pub struct VerusBuildInfo {
    pub profile: VerusBuildProfile,
    pub version: &'static str,
    pub platform_os: &'static str,
    pub platform_arch: &'static str,
    pub toolchain: &'static str,
    pub sha: &'static str,
}

const VARGO_TOOLCHAIN: Option<&'static str> = option_env!("VARGO_TOOLCHAIN");

pub const fn verus_build_info() -> VerusBuildInfo {
    let profile = verus_build_profile();
    let version = match option_env!("VARGO_BUILD_VERSION") {
        Some(v) => v,
        None => "Unknown",
    };
    let platform_os = std::env::consts::OS;
    let platform_arch = std::env::consts::ARCH;
    let toolchain = match VARGO_TOOLCHAIN {
        Some(toolchain) => toolchain,
        None => "unkown",
    };
    let sha = match option_env!("VARGO_BUILD_SHA") {
        Some(v) => v,
        None => "Unknown",
    };
    VerusBuildInfo { profile, version, platform_os, platform_arch, toolchain, sha }
}

impl Display for VerusBuildInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Verus")?;
        writeln!(f, "  Version: {}", self.version)?;
        writeln!(f, "  Profile: {}", self.profile)?;
        writeln!(f, "  Platform: {}_{}", self.platform_os, self.platform_arch)?;
        writeln!(f, "  Toolchain: {}", self.toolchain)?;
        Ok(())
    }
}

impl VerusBuildInfo {
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "verus": {
                "profile": self.profile.to_string(),
                "version": self.version.to_string(),
                "platform": {
                    "os": self.platform_os.to_string(),
                    "arch": self.platform_arch.to_string(),
                },
                "toolchain": self.toolchain.to_string(),
                "commit": self.sha,
            }
        })
    }
}

// ==================================================================================================
// this function was copied from https://github.com/Nugine/const-str/blob/main/const-str/src/bytes.rs
// const-str is MIT licensed
pub const fn const_str_equal(lhs: &str, rhs: &str) -> bool {
    let lhs = lhs.as_bytes();
    let rhs = rhs.as_bytes();
    if lhs.len() != rhs.len() {
        return false;
    }
    let mut i = 0;
    while i < lhs.len() {
        if lhs[i] != rhs[i] {
            return false;
        }
        i += 1;
    }
    true
}
// ==================================================================================================
