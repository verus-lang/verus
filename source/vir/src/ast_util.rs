use crate::ast::{FunctionX, Mode, Path, SpannedTyped, Typ, TypX, VirErr, VirErrX, Visibility};
use crate::def::Spanned;
use air::ast::Span;
pub use air::ast_util::{ident_binder, str_ident};
use std::fmt;
use std::sync::Arc;

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
        (TypX::Tuple(typs1), TypX::Tuple(typs2)) => {
            typs1.len() == typs2.len()
                && typs1
                    .iter()
                    .zip(typs2.iter())
                    .all(|((t1, m1), (t2, m2))| m1 == m2 && types_equal(t1, t2))
        }
        (TypX::Datatype(p1, typs1), TypX::Datatype(p2, typs2)) => {
            p1 == p2
                && typs1.len() == typs2.len()
                && typs1.iter().zip(typs2.iter()).all(|(t1, t2)| types_equal(t1, t2))
        }
        (TypX::Boxed(t1), TypX::Boxed(t2)) => types_equal(t1, t2),
        (TypX::TypParam(x1), TypX::TypParam(x2)) => x1 == x2,
        _ => false,
    }
}

pub fn path_as_rust_name(path: &Path) -> String {
    let krate = match &path.krate {
        None => "crate".to_string(),
        Some(krate) => krate.to_string(),
    };
    let mut strings: Vec<String> = vec![krate];
    for segment in path.segments.iter() {
        strings.push(segment.to_string());
    }
    strings.join("::")
}

// Can source_module see an item owned by owning_module?
pub fn is_visible_to_of_owner(owning_module: &Option<Path>, source_module: &Path) -> bool {
    let sources = &source_module.segments;
    match owning_module {
        None => true,
        Some(target) if target.segments.len() > sources.len() => false,
        Some(target) => {
            // Child can access private item in parent, so check if target is parent:
            let targets = &target.segments;
            target.krate == source_module.krate && targets[..] == sources[..targets.len()]
        }
    }
}

// Can source_module see an item with target_visibility?
pub fn is_visible_to(target_visibility: &Visibility, source_module: &Path) -> bool {
    let Visibility { owning_module, is_private } = target_visibility;
    !is_private || is_visible_to_of_owner(owning_module, source_module)
}

impl<X> SpannedTyped<X> {
    pub fn new(span: &Span, typ: &Typ, x: X) -> Arc<Self> {
        Arc::new(SpannedTyped { span: span.clone(), typ: typ.clone(), x })
    }

    pub fn new_x(&self, x: X) -> Arc<Self> {
        Arc::new(SpannedTyped { span: self.span.clone(), typ: self.typ.clone(), x })
    }
}

impl FunctionX {
    // unit return values are treated as no return value
    pub fn has_return(&self) -> bool {
        match &*self.ret.x.typ {
            TypX::Tuple(ts) if ts.len() == 0 => false,
            TypX::Datatype(path, _) if path == &crate::def::prefix_tuple_type(0) => false,
            _ => true,
        }
    }
}
