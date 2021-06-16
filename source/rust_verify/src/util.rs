use rustc_span::Span;
use std::rc::Rc;
use vir::ast::{VirErr, VirErrX};
use vir::def::Spanned;

pub(crate) fn spanned_new<X>(span: Span, x: X) -> Rc<Spanned<X>> {
    let raw_span = Rc::new(span);
    let as_string = format!("{:?}", span);
    Spanned::new(air::ast::Span { description: None, raw_span, as_string }, x)
}

pub(crate) fn err_span_str<A>(span: Span, msg: &str) -> Result<A, VirErr> {
    Err(spanned_new(span, VirErrX::Str(msg.to_string())))
}

pub(crate) fn err_span_string<A>(span: Span, msg: String) -> Result<A, VirErr> {
    Err(spanned_new(span, VirErrX::Str(msg)))
}

pub(crate) fn unsupported_err_span<A>(span: Span, msg: String) -> Result<A, VirErr> {
    err_span_string(
        span,
        format!("The verifier does not yet support the following Rust feature: {}", msg),
    )
}

// TODO remove if unused
pub(crate) fn warning_span(span: Span, msg: String) -> () {
    eprintln!("warning: {}", msg);
    eprintln!("   --> {:?}", span);
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
            crate::util::err_span_string($span, $msg)?;
        }
    };
    ($assertion: expr, $span: expr, $msg: expr, $info: expr) => {
        if (!$assertion) {
            dbg!($info);
            crate::util::err_span_string($span, $msg)?;
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
