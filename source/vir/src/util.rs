pub(crate) fn vec_map<A, B, F: Fn(&A) -> B>(v: &Vec<A>, f: F) -> Vec<B> {
    v.iter().map(f).collect::<Vec<B>>()
}

pub(crate) fn vec_map_result<A, B, C, F>(v: &Vec<A>, f: F) -> Result<Vec<B>, C>
where
    F: FnMut(&A) -> Result<B, C>,
{
    v.iter().map(f).collect::<Result<Vec<B>, C>>()
}

static VERUS_GITHUB_BUG_REPORT_URL: std::sync::RwLock<Option<std::sync::Arc<String>>> =
    std::sync::RwLock::new(None);

pub fn set_verus_github_bug_report_url(s: String) {
    *VERUS_GITHUB_BUG_REPORT_URL.write().unwrap() = Some(std::sync::Arc::new(s));
}

#[inline(always)]
pub fn get_verus_github_bug_report_url() -> Option<std::sync::Arc<String>> {
    VERUS_GITHUB_BUG_REPORT_URL.read().unwrap().clone()
}

pub(crate) fn err_span<A, S: Into<String>>(
    span: crate::messages::Span,
    msg: S,
) -> Result<A, crate::ast::VirErr> {
    Err(crate::messages::error(&span, msg))
}

pub fn internal_err_span<A>(
    span: crate::messages::Span,
    msg: String,
) -> Result<A, crate::ast::VirErr> {
    let mut e = err_span(span, format!("verus internal error: {}", msg));
    if let Some(verus_github_bug_report_url) = get_verus_github_bug_report_url() {
        e = e.map_err(|e| {
            e.help(format!(
                "This is a bug in the verifier. Please report it at {}.",
                verus_github_bug_report_url
            ))
        });
    }
    e
}

#[macro_export]
macro_rules! internal_err {
    ($span: expr, $msg: expr) => {{
        $crate::util::internal_err_span($span, $msg.to_string())?;
        unreachable!()
    }};
    ($span: expr, $msg: expr, $info: expr) => {{
        dbg!($info);
        $crate::util::internal_err_span($span, $msg.to_string())?;
        unreachable!()
    }};
}

#[allow(unused_macros)]
macro_rules! dbg_backtrace {
    ($val: expr) => {
        match $val {
            tmp => {
                std::eprintln!(
                    "[{}:{}:{}] {} = {:#?}",
                    std::file!(),
                    std::line!(),
                    std::column!(),
                    std::stringify!($val),
                    &tmp
                );
                eprintln!(
                    "[{}:{}:{}]\n{}",
                    std::file!(),
                    std::line!(),
                    std::column!(),
                    std::backtrace::Backtrace::force_capture()
                );
                tmp
            }
        }
    };
}

#[allow(unused_imports)]
pub(crate) use dbg_backtrace;

#[allow(unused_macros)]
macro_rules! backtrace {
    () => {
        eprintln!(
            "[{}:{}:{}]\n{}",
            std::file!(),
            std::line!(),
            std::column!(),
            std::backtrace::Backtrace::force_capture()
        );
    };
}

#[allow(unused_imports)]
pub(crate) use backtrace;
