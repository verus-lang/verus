use rustc_span::{FileName, Span};
use rustc_span::source_map::SourceMap;
use std::rc::Rc;
use crate::unsupported;
use vir::ast::{VirErr, VirErrX};
use vir::def::Spanned;
use crate::context::Context;

pub(crate) fn spanned_new<X>(ctxt: &Context, span: Span, x: X) -> Rc<Spanned<X>> {
    let raw_span = Rc::new(span);
    let as_string = format!("{:?}", span);
    let filename: String = match map.span_to_filename(span) {
        FileName::Real(rfn) => rfn
            .local_path()
            .to_str()
            .expect("internal error: path is not a valid string")
            .to_string(),
        _ => unsupported!("non real filenames in verifier errors", span),
    };
    let (start, end) = map.is_valid_span(span).expect("internal error: invalid Span");
    Spanned::new(air::ast::Span { description: None, raw_span, as_string, filename, start_row:start.line, start_col:start.col.to_u32(), end_row:end.line, end_col:end.col.to_u32() }, x)
}

pub(crate) fn err_span_str<A>(ctxt: &Context, span: Span, msg: &str) -> Result<A, VirErr> {
    Err(spanned_new(ctxt, span, VirErrX::Str(msg.to_string())))
}

pub(crate) fn err_span_string<A>(ctxt: &Context, span: Span, msg: String) -> Result<A, VirErr> {
    Err(spanned_new(ctxt, span, VirErrX::Str(msg)))
}

pub(crate) fn unsupported_err_span<A>(ctxt: &Context, span: Span, msg: String) -> Result<A, VirErr> {
    err_span_string(
        ctxt,
        span,
        format!("The verifier does not yet support the following Rust feature: {}", msg),
    )
}

#[macro_export]
macro_rules! unsupported_err {
    ($ctxt: expr, $span: expr, $msg: expr) => {{
        dbg!();
        unsupported_err_span($ctxt, $span, $msg.to_string())?
    }};
    ($ctxt: expr, $span: expr, $msg: expr, $info: expr) => {{
        dbg!($info);
        unsupported_err_span($ctxt, $span, $msg.to_string())?
    }};
}

#[macro_export]
macro_rules! unsupported_err_unless {
    ($ctxt: expr, $assertion: expr, $span: expr, $msg: expr) => {
        if (!$assertion) {
            dbg!();
            unsupported_err_span($ctxt, $span, $msg.to_string())?;
        }
    };
    ($ctxt: expr, $assertion: expr, $span: expr, $msg: expr, $info: expr) => {
        if (!$assertion) {
            dbg!($info);
            unsupported_err_span($ctxt, $span, $msg.to_string())?;
        }
    };
}

#[macro_export]
macro_rules! err_unless {
    ($ctxt: expr, $assertion: expr, $span: expr, $msg: expr) => {
        if (!$assertion) {
            dbg!();
            crate::util::err_span_string($ctxt, $span, $msg)?;
        }
    };
    ($ctxt: expr, $assertion: expr, $span: expr, $msg: expr, $info: expr) => {
        if (!$assertion) {
            dbg!($info);
            crate::util::err_span_string($ctxt, $span, $msg)?;
        }
    };
}

#[macro_export]
macro_rules! unsupported {
    ($msg: expr) => {{ panic!("The verifier does not yet support the following Rust feature: {}", $msg) }};
    ($msg: expr, $info: expr) => {{
        dbg!($info);
        panic!("The verifier does not yet support the following Rust feature: {}", $msg)
    }};
}

#[macro_export]
macro_rules! unsupported_unless {
    ($assertion: expr, $msg: expr) => {
        if (!$assertion) {
            panic!("The verifier does not yet support the following Rust feature: {}", $msg)
        }
    };
    ($assertion: expr, $msg: expr, $info: expr) => {
        if (!$assertion) {
            dbg!($info);
            panic!("The verifier does not yet support the following Rust feature: {}", $msg)
        }
    };
}

#[allow(dead_code)]
pub(crate) fn vec_map<A, B, F: Fn(&A) -> B>(v: &Vec<A>, f: F) -> Vec<B> {
    v.iter().map(f).collect()
}

pub(crate) fn vec_map_result<A, B, E, F>(v: &Vec<A>, f: F) -> Result<Vec<B>, E>
where
    F: Fn(&A) -> Result<B, E>,
{
    v.iter().map(f).collect()
}

pub(crate) fn slice_vec_map_result<A, B, E, F: Fn(&A) -> Result<B, E>>(
    slice: &[A],
    f: F,
) -> Result<Vec<B>, E> {
    slice.iter().map(f).collect()
}
