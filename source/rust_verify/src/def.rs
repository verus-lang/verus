pub const IS_VARIANT_PREFIX: &str = "is";
pub const GET_VARIANT_PREFIX: &str = "get";

pub(crate) fn is_variant_fn_name(variant_ident: &str) -> String {
    format!("{}_{}", crate::def::IS_VARIANT_PREFIX, variant_ident)
}

pub(crate) fn get_variant_fn_name(variant_ident: &str, field_ident: &str) -> String {
    format!("{}_{}_{}", crate::def::GET_VARIANT_PREFIX, variant_ident, field_ident)
}
