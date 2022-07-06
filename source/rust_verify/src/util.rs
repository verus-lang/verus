use rustc_span::{Span, SpanData};
use std::sync::Arc;
use vir::ast::{SpannedTyped, Typ, VirErr};
use vir::ast_util::err_string;
use vir::def::Spanned;

pub(crate) fn to_raw_span(span: Span) -> air::ast::RawSpan {
    Arc::new(span.data())
}

pub(crate) fn from_raw_span(raw_span: &air::ast::RawSpan) -> Span {
    (**raw_span).downcast_ref::<SpanData>().expect("internal error: failed to cast to Span").span()
}

pub(crate) fn spanned_new<X>(span: Span, x: X) -> Arc<Spanned<X>> {
    let raw_span = to_raw_span(span);
    let as_string = format!("{:?}", span);
    Spanned::new(air::ast::Span { raw_span, as_string }, x)
}

pub(crate) fn spanned_typed_new<X>(span: Span, typ: &Typ, x: X) -> Arc<SpannedTyped<X>> {
    let raw_span = to_raw_span(span);
    let as_string = format!("{:?}", span);
    SpannedTyped::new(&air::ast::Span { raw_span, as_string }, typ, x)
}

pub(crate) fn err_span_str<A>(span: Span, msg: &str) -> Result<A, VirErr> {
    err_span_string(span, msg.to_string())
}

pub(crate) fn err_span_string<A>(span: Span, msg: String) -> Result<A, VirErr> {
    let raw_span = to_raw_span(span);
    let as_string = format!("{:?}", span);
    let air_span = air::ast::Span { raw_span, as_string };
    err_string(&air_span, msg)
}

pub(crate) fn unsupported_err_span<A>(span: Span, msg: String) -> Result<A, VirErr> {
    err_span_string(
        span,
        format!("The verifier does not yet support the following Rust feature: {}", msg),
    )
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
macro_rules! err {
    ($span: expr, $msg: expr) => {
        return match crate::util::err_span_string::<()>($span, $msg) {
            Ok(()) => panic!("unreachable"), 
            Err(e) => Err(e)
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

/// Basic error, with just a message
pub fn error<S: Into<String>>(msg: S) -> VirErr {
    Arc::new(air::errors::ErrorX { msg: msg.into(), spans: vec![], labels: Vec::new() })
}

#[allow(dead_code)]
pub(crate) fn vec_map<A, B, F: FnMut(&A) -> B>(v: &Vec<A>, f: F) -> Vec<B> {
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

pub mod signalling {
    use std::sync::{Arc, Condvar, Mutex};

    #[derive(Clone)]
    pub struct Signaller<T: Copy> {
        coord: Arc<(Mutex<Option<T>>, Condvar)>,
    }

    impl<T: Copy> Signaller<T> {
        pub fn signal(&self, t: T) {
            let (value, cvar) = &*self.coord;
            *value.lock().expect("Signaller mutex") = Some(t);
            cvar.notify_one();
        }
    }

    pub struct Signalled<T: Copy> {
        coord: Arc<(Mutex<Option<T>>, Condvar)>,
    }

    impl<T: Copy> Signalled<T> {
        pub fn wait(&self) -> T {
            let (lock, cvar) = &*self.coord;
            let mut value = lock.lock().expect("value mutex");
            while value.is_none() {
                value = cvar.wait(value).expect("cvar wait");
            }
            value.unwrap()
        }
    }

    pub fn signal<T: Copy>() -> (Signaller<T>, Signalled<T>) {
        let coord = Arc::new((Mutex::new(None), Condvar::new()));
        (Signaller { coord: coord.clone() }, Signalled { coord: coord.clone() })
    }
}
