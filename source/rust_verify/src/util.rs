use std::fmt::Display;

use rustc_span::Span;
use vir::ast::VirErr;

pub(crate) fn err_span<A, S: Into<String>>(span: Span, msg: S) -> Result<A, VirErr> {
    Err(vir::messages::error(&crate::spans::err_air_span(span), msg))
}

pub(crate) fn err_span_bare<S: Into<String>>(span: Span, msg: S) -> VirErr {
    vir::messages::error(&crate::spans::err_air_span(span), msg)
}

pub(crate) fn vir_err_span_str(span: Span, msg: &str) -> VirErr {
    vir_err_span_string(span, msg.to_string())
}

pub(crate) fn vir_err_span_string(span: Span, msg: String) -> VirErr {
    vir::messages::error(&crate::spans::err_air_span(span), msg)
}

pub(crate) fn unsupported_err_span<A>(span: Span, msg: String) -> Result<A, VirErr> {
    err_span(span, format!("The verifier does not yet support the following Rust feature: {}", msg))
}

#[macro_export]
macro_rules! unsupported_err {
    ($span: expr, $msg: expr) => {{
        unsupported_err_span($span, $msg.to_string())?;
        unreachable!()
    }};
    ($span: expr, $msg: expr, $info: expr) => {{
        dbg!($info);
        unsupported_err_span($span, $msg.to_string())?;
        unreachable!()
    }};
}

#[macro_export]
macro_rules! unsupported_err_unless {
    ($assertion: expr, $span: expr, $msg: expr) => {
        if (!$assertion) {
            crate::util::unsupported_err_span($span, $msg.to_string())?;
        }
    };
    ($assertion: expr, $span: expr, $msg: expr, $info: expr) => {
        if (!$assertion) {
            dbg!($info);
            crate::util::unsupported_err_span($span, $msg.to_string())?;
        }
    };
}

#[macro_export]
macro_rules! err_unless {
    ($assertion: expr, $span: expr, $msg: expr) => {
        if (!$assertion) {
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
    vir::messages::error_bare(msg)
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

// this is unfortunate, but when processing a reveal we cannot get the type of the
// corresponding node in HIR because the body of the reveal closure cannot be
// successfully typechecked, and I did not find a public interface to this in rustc
// NOTE: do not use this if you have a body context with `types` or can otherwise obtain TypeckResults
pub fn hir_prim_ty_to_mir_ty<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    prim_ty: &rustc_hir::PrimTy,
) -> rustc_middle::ty::Ty<'tcx> {
    match prim_ty {
        rustc_hir::PrimTy::Int(int_ty) => match int_ty {
            rustc_ast::IntTy::Isize => tcx.types.isize,
            rustc_ast::IntTy::I8 => tcx.types.i8,
            rustc_ast::IntTy::I16 => tcx.types.i16,
            rustc_ast::IntTy::I32 => tcx.types.i32,
            rustc_ast::IntTy::I64 => tcx.types.i64,
            rustc_ast::IntTy::I128 => tcx.types.i128,
        },
        rustc_hir::PrimTy::Uint(uint_ty) => match uint_ty {
            rustc_ast::UintTy::Usize => tcx.types.usize,
            rustc_ast::UintTy::U8 => tcx.types.u8,
            rustc_ast::UintTy::U16 => tcx.types.u16,
            rustc_ast::UintTy::U32 => tcx.types.u32,
            rustc_ast::UintTy::U64 => tcx.types.u64,
            rustc_ast::UintTy::U128 => tcx.types.u128,
        },
        rustc_hir::PrimTy::Float(float_ty) => match float_ty {
            rustc_ast::FloatTy::F32 => tcx.types.f32,
            rustc_ast::FloatTy::F64 => tcx.types.f64,
        },
        rustc_hir::PrimTy::Str => tcx.types.str_,
        rustc_hir::PrimTy::Bool => tcx.types.bool,
        rustc_hir::PrimTy::Char => tcx.types.char,
    }
}
