use crate::ast::Typ;
pub use air::ast_util::{ident_binder, str_ident};

pub fn types_equal(typ1: &Typ, typ2: &Typ) -> bool {
    match (typ1, typ2) {
        (Typ::Bool, Typ::Bool) => true,
        (Typ::Int(range1), Typ::Int(range2)) => range1 == range2,
        (Typ::Path(p1), Typ::Path(p2)) => p1 == p2,
        _ => false,
    }
}
