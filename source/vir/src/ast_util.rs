use crate::ast::{Mode, Path, Typ, TypX, VirErr, VirErrX};
use crate::def::Spanned;
use air::ast::Span;
pub use air::ast_util::{ident_binder, str_ident};
use std::fmt;

pub fn err_str<A>(span: &Span, msg: &str) -> Result<A, VirErr> {
    Err(Spanned::new(span.clone(), VirErrX::Str(msg.to_string())))
}

pub fn err_string<A>(span: &Span, msg: String) -> Result<A, VirErr> {
    Err(Spanned::new(span.clone(), VirErrX::Str(msg)))
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mode::Spec => write!(f, "spec"),
            Mode::Proof => write!(f, "proof"),
            Mode::Exec => write!(f, "exec"),
        }
    }
}

pub fn types_equal(typ1: &Typ, typ2: &Typ) -> bool {
    match (&**typ1, &**typ2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(range1), TypX::Int(range2)) => range1 == range2,
        (TypX::Path(p1), TypX::Path(p2)) => p1 == p2,
        (TypX::TypParam(x1), TypX::TypParam(x2)) => x1 == x2,
        _ => false,
    }
}

pub fn path_to_string(path: &Path) -> String {
    let sep = crate::def::TYPE_PATH_SEPARATOR;
    path.iter().map(|x| (**x).as_str()).collect::<Vec<_>>().join(sep)
}
