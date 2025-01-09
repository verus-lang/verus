use crate::ast::Ident;
use std::sync::Arc;

pub const PREFIX_LABEL: &str = "%%location_label%%";
pub const GLOBAL_PREFIX_LABEL: &str = "%%global_location_label%%";
const BREAK_LABEL: &str = "%%break_label%%";
pub const SWITCH_LABEL: &str = "%%switch_label%%";
pub const FUNCTION: &str = "%%Function%%";
pub const ARRAY: &str = "%%array%%";
pub const LAMBDA: &str = "%%lambda%%";
pub const CHOOSE: &str = "%%choose%%";
pub const HOLE: &str = "%%hole%%";
pub const APPLY: &str = "%%apply%%";
pub const TEMP: &str = "%%x%%";
pub const SKOLEM_ID_PREFIX: &str = "skolem";
pub const ARRAY_QID: &str = "__AIR_ARRAY_QID__";

pub fn mk_skolem_id(qid: &str) -> String {
    format!("{}_{}", crate::def::SKOLEM_ID_PREFIX, qid)
}

pub(crate) fn break_label(label: &Ident) -> Ident {
    Arc::new(format!("{}{}", BREAK_LABEL, label))
}
