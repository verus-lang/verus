use rustc_span::Span;
use vir::ast::VirErr;
use vir::ast_util::err_string;

pub(crate) fn err_span_str<A>(span: Span, msg: &str) -> Result<A, VirErr> {
    err_span_string(span, msg.to_string())
}

pub(crate) fn err_span_string<A>(span: Span, msg: String) -> Result<A, VirErr> {
    err_string(&crate::spans::err_air_span(span), msg)
}

pub(crate) fn vir_err_span_str(span: Span, msg: &str) -> VirErr {
    vir_err_span_string(span, msg.to_string())
}

pub(crate) fn vir_err_span_string(span: Span, msg: String) -> VirErr {
    air::messages::error(msg, &crate::spans::err_air_span(span))
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
